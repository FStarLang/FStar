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
              let rec aux uu___85_2834 =
                match uu___85_2834 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____2845 = get_exported_id_set env mname  in
                      match uu____2845 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2870 = mex eikind  in
                            FStar_ST.op_Bang uu____2870  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____2992 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____2992 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3072 = qual modul id1  in
                        find_in_module uu____3072
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3076 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___86_3083  ->
    match uu___86_3083 with
    | Exported_id_field  -> true
    | uu____3084 -> false
  
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
                  let check_local_binding_id uu___87_3205 =
                    match uu___87_3205 with
                    | (id',uu____3207,uu____3208) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___88_3214 =
                    match uu___88_3214 with
                    | (id',uu____3216,uu____3217) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3221 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3221  in
                  let proc uu___89_3229 =
                    match uu___89_3229 with
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
                        let uu____3237 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3237 id1
                    | uu____3242 -> Cont_ignore  in
                  let rec aux uu___90_3252 =
                    match uu___90_3252 with
                    | a::q ->
                        let uu____3261 = proc a  in
                        option_of_cont (fun uu____3265  -> aux q) uu____3261
                    | [] ->
                        let uu____3266 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____3270  -> FStar_Pervasives_Native.None)
                          uu____3266
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____3279 'Auu____3280 .
    FStar_Range.range ->
      ('Auu____3279,FStar_Syntax_Syntax.bv,'Auu____3280)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3280)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3300  ->
      match uu____3300 with
      | (id',x,mut) -> let uu____3310 = bv_to_name x r  in (uu____3310, mut)
  
let find_in_module :
  'Auu____3321 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3321)
          -> 'Auu____3321 -> 'Auu____3321
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3360 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____3360 with
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
      let uu____3400 = unmangleOpName id1  in
      match uu____3400 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3426 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3440 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3440) (fun uu____3450  -> Cont_fail)
            (fun uu____3456  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3471  -> fun uu____3472  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3487  -> fun uu____3488  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____3567 ->
                let lid = qualify env id1  in
                let uu____3569 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3569 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3593 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3593
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3616 = current_module env  in qual uu____3616 id1
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
        let rec aux uu___91_3679 =
          match uu___91_3679 with
          | [] ->
              let uu____3684 = module_is_defined env lid  in
              if uu____3684
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3693 =
                  let uu____3694 = FStar_Ident.path_of_lid ns  in
                  let uu____3697 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____3694 uu____3697  in
                let uu____3700 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____3693 uu____3700  in
              let uu____3701 = module_is_defined env new_lid  in
              if uu____3701
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3707 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3714::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3733 =
          let uu____3734 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3734  in
        if uu____3733
        then
          let uu____3735 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____3735
           then ()
           else
             (let uu____3737 =
                let uu____3742 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____3742)
                 in
              let uu____3743 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____3737 uu____3743))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3755 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____3759 = resolve_module_name env modul_orig true  in
          (match uu____3759 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3763 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___92_3784  ->
             match uu___92_3784 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3787 -> false) env.scope_mods
  
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
                 let uu____3906 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____3906
                   (FStar_Util.map_option
                      (fun uu____3956  ->
                         match uu____3956 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4026 = aux ns_rev_prefix ns_last_id  in
              (match uu____4026 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path
        then
          let uu____4087 =
            let uu____4090 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____4090 true  in
          match uu____4087 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4104 -> do_shorten env ids
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
                  | uu____4223::uu____4224 ->
                      let uu____4227 =
                        let uu____4230 =
                          let uu____4231 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4232 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4231 uu____4232  in
                        resolve_module_name env uu____4230 true  in
                      (match uu____4227 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4236 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4240  -> FStar_Pervasives_Native.None)
                             uu____4236)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___93_4263  ->
      match uu___93_4263 with
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
              let uu____4379 = k_global_def lid1 def  in
              cont_of_option k uu____4379  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4415 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4415)
              (fun r  ->
                 let uu____4421 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4421)
              (fun uu____4425  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4435,uu____4436,uu____4437,l,uu____4439,uu____4440) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___94_4451  ->
               match uu___94_4451 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4454,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4466 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4472,uu____4473,uu____4474)
        -> FStar_Pervasives_Native.None
    | uu____4475 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4490 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4498 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4498
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4490 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4516 =
         let uu____4517 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4517  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4516) &&
        (let uu____4525 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4525 ns)
  
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
          let k_global_def source_lid uu___99_4567 =
            match uu___99_4567 with
            | (uu____4574,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4576) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4579 ->
                     let uu____4596 =
                       let uu____4597 =
                         let uu____4606 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4606, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4597  in
                     FStar_Pervasives_Native.Some uu____4596
                 | FStar_Syntax_Syntax.Sig_datacon uu____4609 ->
                     let uu____4624 =
                       let uu____4625 =
                         let uu____4634 =
                           let uu____4635 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4635
                            in
                         (uu____4634, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4625  in
                     FStar_Pervasives_Native.Some uu____4624
                 | FStar_Syntax_Syntax.Sig_let ((uu____4640,lbs),uu____4642)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4658 =
                       let uu____4659 =
                         let uu____4668 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4668, false,
                           (se.FStar_Syntax_Syntax.sigattrs))
                          in
                       Term_name uu____4659  in
                     FStar_Pervasives_Native.Some uu____4658
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4672,uu____4673) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4677 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___95_4681  ->
                                  match uu___95_4681 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4682 -> false)))
                        in
                     if uu____4677
                     then
                       let lid2 =
                         let uu____4686 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____4686  in
                       let dd =
                         let uu____4688 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___96_4693  ->
                                      match uu___96_4693 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4694 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4699 -> true
                                      | uu____4700 -> false)))
                            in
                         if uu____4688
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let dd1 =
                         let uu____4703 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___97_4707  ->
                                   match uu___97_4707 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4708 -> false))
                            in
                         if uu____4703
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4710 =
                         FStar_Util.find_map quals
                           (fun uu___98_4715  ->
                              match uu___98_4715 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4719 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____4710 with
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
                        | uu____4730 ->
                            let uu____4733 =
                              let uu____4734 =
                                let uu____4743 =
                                  let uu____4744 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4744
                                   in
                                (uu____4743, false,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____4734  in
                            FStar_Pervasives_Native.Some uu____4733)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____4751 =
                       let uu____4752 =
                         let uu____4757 =
                           let uu____4758 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4758
                            in
                         (se, uu____4757)  in
                       Eff_name uu____4752  in
                     FStar_Pervasives_Native.Some uu____4751
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4760 =
                       let uu____4761 =
                         let uu____4766 =
                           let uu____4767 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4767
                            in
                         (se, uu____4766)  in
                       Eff_name uu____4761  in
                     FStar_Pervasives_Native.Some uu____4760
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4768 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____4787 =
                       let uu____4788 =
                         let uu____4797 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_defined_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____4797, false, [])  in
                       Term_name uu____4788  in
                     FStar_Pervasives_Native.Some uu____4787
                 | uu____4800 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let uu____4821 =
              let uu____4826 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____4826 r  in
            match uu____4821 with
            | (t,mut) ->
                FStar_Pervasives_Native.Some (Term_name (t, mut, []))
             in
          let k_rec_binding uu____4846 =
            match uu____4846 with
            | (id1,l,dd) ->
                let uu____4858 =
                  let uu____4859 =
                    let uu____4868 =
                      let uu____4869 =
                        let uu____4870 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____4870  in
                      FStar_Syntax_Syntax.fvar uu____4869 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____4868, false, [])  in
                  Term_name uu____4859  in
                FStar_Pervasives_Native.Some uu____4858
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4878 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____4878 with
                 | FStar_Pervasives_Native.Some (t,mut) ->
                     FStar_Pervasives_Native.Some (Term_name (t, mut, []))
                 | uu____4895 -> FStar_Pervasives_Native.None)
            | uu____4902 -> FStar_Pervasives_Native.None  in
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
        let uu____4937 = try_lookup_name true exclude_interf env lid  in
        match uu____4937 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4952 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4971 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____4971 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4986 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5011 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5011 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5027;
             FStar_Syntax_Syntax.sigquals = uu____5028;
             FStar_Syntax_Syntax.sigmeta = uu____5029;
             FStar_Syntax_Syntax.sigattrs = uu____5030;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5049;
             FStar_Syntax_Syntax.sigquals = uu____5050;
             FStar_Syntax_Syntax.sigmeta = uu____5051;
             FStar_Syntax_Syntax.sigattrs = uu____5052;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5070,uu____5071,uu____5072,uu____5073,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5075;
             FStar_Syntax_Syntax.sigquals = uu____5076;
             FStar_Syntax_Syntax.sigmeta = uu____5077;
             FStar_Syntax_Syntax.sigattrs = uu____5078;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5100 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5125 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5125 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5135;
             FStar_Syntax_Syntax.sigquals = uu____5136;
             FStar_Syntax_Syntax.sigmeta = uu____5137;
             FStar_Syntax_Syntax.sigattrs = uu____5138;_},uu____5139)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____5149;
             FStar_Syntax_Syntax.sigquals = uu____5150;
             FStar_Syntax_Syntax.sigmeta = uu____5151;
             FStar_Syntax_Syntax.sigattrs = uu____5152;_},uu____5153)
          -> FStar_Pervasives_Native.Some ne
      | uu____5162 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____5179 = try_lookup_effect_name env lid  in
      match uu____5179 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5182 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5195 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5195 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5205,uu____5206,uu____5207,uu____5208);
             FStar_Syntax_Syntax.sigrng = uu____5209;
             FStar_Syntax_Syntax.sigquals = uu____5210;
             FStar_Syntax_Syntax.sigmeta = uu____5211;
             FStar_Syntax_Syntax.sigattrs = uu____5212;_},uu____5213)
          ->
          let rec aux new_name =
            let uu____5234 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____5234 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5252) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____5260 =
                       let uu____5261 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5261
                        in
                     FStar_Pervasives_Native.Some uu____5260
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5263 =
                       let uu____5264 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5264
                        in
                     FStar_Pervasives_Native.Some uu____5263
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5265,uu____5266,uu____5267,cmp,uu____5269) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5275 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5276,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5282 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___100_5319 =
        match uu___100_5319 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5328,uu____5329,uu____5330);
             FStar_Syntax_Syntax.sigrng = uu____5331;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5333;
             FStar_Syntax_Syntax.sigattrs = uu____5334;_},uu____5335)
            -> FStar_Pervasives_Native.Some quals
        | uu____5342 -> FStar_Pervasives_Native.None  in
      let uu____5349 =
        resolve_in_open_namespaces' env lid
          (fun uu____5357  -> FStar_Pervasives_Native.None)
          (fun uu____5361  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5349 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5371 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5388 =
        FStar_List.tryFind
          (fun uu____5403  ->
             match uu____5403 with
             | (mlid,modul) ->
                 let uu____5410 = FStar_Ident.path_of_lid mlid  in
                 uu____5410 = path) env.modules
         in
      match uu____5388 with
      | FStar_Pervasives_Native.Some (uu____5413,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___101_5451 =
        match uu___101_5451 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5458,lbs),uu____5460);
             FStar_Syntax_Syntax.sigrng = uu____5461;
             FStar_Syntax_Syntax.sigquals = uu____5462;
             FStar_Syntax_Syntax.sigmeta = uu____5463;
             FStar_Syntax_Syntax.sigattrs = uu____5464;_},uu____5465)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____5485 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____5485
        | uu____5486 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5492  -> FStar_Pervasives_Native.None)
        (fun uu____5494  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___102_5525 =
        match uu___102_5525 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5535);
             FStar_Syntax_Syntax.sigrng = uu____5536;
             FStar_Syntax_Syntax.sigquals = uu____5537;
             FStar_Syntax_Syntax.sigmeta = uu____5538;
             FStar_Syntax_Syntax.sigattrs = uu____5539;_},uu____5540)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5563 -> FStar_Pervasives_Native.None)
        | uu____5570 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5580  -> FStar_Pervasives_Native.None)
        (fun uu____5584  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____5641 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____5641 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut,attrs)) ->
              FStar_Pervasives_Native.Some (e, mut, attrs)
          | uu____5671 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5727) ->
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
      let uu____5802 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5802 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5841 = try_lookup_lid env l  in
      match uu____5841 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5855) ->
          let uu____5860 =
            let uu____5861 = FStar_Syntax_Subst.compress e  in
            uu____5861.FStar_Syntax_Syntax.n  in
          (match uu____5860 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5867 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____5878 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____5878 with
      | (uu____5887,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____5907 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____5911 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____5911 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____5915 -> shorten_lid' env lid)
  
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
        let uu___123_5949 = env  in
        {
          curmodule = (uu___123_5949.curmodule);
          curmonad = (uu___123_5949.curmonad);
          modules = (uu___123_5949.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___123_5949.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___123_5949.sigaccum);
          sigmap = (uu___123_5949.sigmap);
          iface = (uu___123_5949.iface);
          admitted_iface = (uu___123_5949.admitted_iface);
          expect_typ = (uu___123_5949.expect_typ);
          docs = (uu___123_5949.docs);
          remaining_iface_decls = (uu___123_5949.remaining_iface_decls);
          syntax_only = (uu___123_5949.syntax_only);
          ds_hooks = (uu___123_5949.ds_hooks)
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
      let uu____5972 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____5972 drop_attributes
  
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
      let k_global_def lid1 uu___104_6039 =
        match uu___104_6039 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____6046,uu____6047,uu____6048);
             FStar_Syntax_Syntax.sigrng = uu____6049;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6051;
             FStar_Syntax_Syntax.sigattrs = uu____6052;_},uu____6053)
            ->
            let uu____6058 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___103_6062  ->
                      match uu___103_6062 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6063 -> false))
               in
            if uu____6058
            then
              let uu____6066 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6066
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6068;
             FStar_Syntax_Syntax.sigrng = uu____6069;
             FStar_Syntax_Syntax.sigquals = uu____6070;
             FStar_Syntax_Syntax.sigmeta = uu____6071;
             FStar_Syntax_Syntax.sigattrs = uu____6072;_},uu____6073)
            ->
            let uu____6092 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Pervasives_Native.Some uu____6092
        | uu____6093 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6099  -> FStar_Pervasives_Native.None)
        (fun uu____6101  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___105_6134 =
        match uu___105_6134 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6143,uu____6144,uu____6145,uu____6146,datas,uu____6148);
             FStar_Syntax_Syntax.sigrng = uu____6149;
             FStar_Syntax_Syntax.sigquals = uu____6150;
             FStar_Syntax_Syntax.sigmeta = uu____6151;
             FStar_Syntax_Syntax.sigattrs = uu____6152;_},uu____6153)
            -> FStar_Pervasives_Native.Some datas
        | uu____6168 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6178  -> FStar_Pervasives_Native.None)
        (fun uu____6182  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((unit -> unit,unit -> unit,unit -> record_or_dc Prims.list,record_or_dc ->
                                                                unit)
     FStar_Pervasives_Native.tuple4,unit -> unit)
    FStar_Pervasives_Native.tuple2)
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____6234 =
    let uu____6235 =
      let uu____6240 =
        let uu____6243 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6243  in
      let uu____6303 = FStar_ST.op_Bang record_cache  in uu____6240 ::
        uu____6303
       in
    FStar_ST.op_Colon_Equals record_cache uu____6235  in
  let pop1 uu____6421 =
    let uu____6422 =
      let uu____6427 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6427  in
    FStar_ST.op_Colon_Equals record_cache uu____6422  in
  let peek1 uu____6547 =
    let uu____6548 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6548  in
  let insert r =
    let uu____6614 =
      let uu____6619 = let uu____6622 = peek1 ()  in r :: uu____6622  in
      let uu____6625 =
        let uu____6630 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6630  in
      uu____6619 :: uu____6625  in
    FStar_ST.op_Colon_Equals record_cache uu____6614  in
  let filter1 uu____6750 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6759 =
      let uu____6764 =
        let uu____6769 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6769  in
      filtered :: uu____6764  in
    FStar_ST.op_Colon_Equals record_cache uu____6759  in
  let aux = (push1, pop1, peek1, insert)  in (aux, filter1) 
let (record_cache_aux :
  (unit -> unit,unit -> unit,unit -> record_or_dc Prims.list,record_or_dc ->
                                                               unit)
    FStar_Pervasives_Native.tuple4)
  =
  let uu____6968 = record_cache_aux_with_filter  in
  match uu____6968 with | (aux,uu____7021) -> aux 
let (filter_record_cache : unit -> unit) =
  let uu____7076 = record_cache_aux_with_filter  in
  match uu____7076 with | (uu____7109,filter1) -> filter1 
let (push_record_cache : unit -> unit) =
  let uu____7165 = record_cache_aux  in
  match uu____7165 with | (push1,uu____7192,uu____7193,uu____7194) -> push1 
let (pop_record_cache : unit -> unit) =
  let uu____7227 = record_cache_aux  in
  match uu____7227 with | (uu____7253,pop1,uu____7255,uu____7256) -> pop1 
let (peek_record_cache : unit -> record_or_dc Prims.list) =
  let uu____7291 = record_cache_aux  in
  match uu____7291 with | (uu____7319,uu____7320,peek1,uu____7322) -> peek1 
let (insert_record_cache : record_or_dc -> unit) =
  let uu____7355 = record_cache_aux  in
  match uu____7355 with | (uu____7381,uu____7382,uu____7383,insert) -> insert 
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref -> FStar_Syntax_Syntax.sigelt -> unit)
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____7459) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___106_7477  ->
                   match uu___106_7477 with
                   | FStar_Syntax_Syntax.RecordType uu____7478 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7487 -> true
                   | uu____7496 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___107_7520  ->
                      match uu___107_7520 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7522,uu____7523,uu____7524,uu____7525,uu____7526);
                          FStar_Syntax_Syntax.sigrng = uu____7527;
                          FStar_Syntax_Syntax.sigquals = uu____7528;
                          FStar_Syntax_Syntax.sigmeta = uu____7529;
                          FStar_Syntax_Syntax.sigattrs = uu____7530;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7539 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___108_7574  ->
                    match uu___108_7574 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7578,uu____7579,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7581;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7583;
                        FStar_Syntax_Syntax.sigattrs = uu____7584;_} ->
                        let uu____7595 =
                          let uu____7596 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____7596  in
                        (match uu____7595 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____7602,t,uu____7604,uu____7605,uu____7606);
                             FStar_Syntax_Syntax.sigrng = uu____7607;
                             FStar_Syntax_Syntax.sigquals = uu____7608;
                             FStar_Syntax_Syntax.sigmeta = uu____7609;
                             FStar_Syntax_Syntax.sigattrs = uu____7610;_} ->
                             let uu____7619 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____7619 with
                              | (formals,uu____7633) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____7682  ->
                                            match uu____7682 with
                                            | (x,q) ->
                                                let uu____7695 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____7695
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7752  ->
                                            match uu____7752 with
                                            | (x,q) ->
                                                let uu____7765 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____7765,
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
                                  ((let uu____7780 =
                                      let uu____7783 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____7783  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7780);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7896 =
                                            match uu____7896 with
                                            | (id1,uu____7904) ->
                                                let modul =
                                                  let uu____7910 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____7910.FStar_Ident.str
                                                   in
                                                let uu____7911 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____7911 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____7945 =
                                                         let uu____7946 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____7946
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7945);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8040 =
                                                               let uu____8041
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8041.FStar_Ident.ident
                                                                in
                                                             uu____8040.FStar_Ident.idText
                                                              in
                                                           let uu____8043 =
                                                             let uu____8044 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8044
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8043))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8148 -> ())
                    | uu____8149 -> ()))
        | uu____8150 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8171 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8171 with
        | (ns,id1) ->
            let uu____8188 = peek_record_cache ()  in
            FStar_Util.find_map uu____8188
              (fun record  ->
                 let uu____8194 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8200  -> FStar_Pervasives_Native.None)
                   uu____8194)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8202  -> Cont_ignore) (fun uu____8204  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8210 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8210)
        (fun k  -> fun uu____8216  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8231 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8231 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8237 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8255 = try_lookup_record_by_field_name env lid  in
        match uu____8255 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8259 =
              let uu____8260 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8260  in
            let uu____8261 =
              let uu____8262 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8262  in
            uu____8259 = uu____8261 ->
            let uu____8263 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8267  -> Cont_ok ())
               in
            (match uu____8263 with
             | Cont_ok uu____8268 -> true
             | uu____8269 -> false)
        | uu____8272 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8291 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8291 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8301 =
            let uu____8306 =
              let uu____8307 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8308 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8307 uu____8308  in
            (uu____8306, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8301
      | uu____8313 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8339  ->
    let uu____8340 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8340
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8367  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___109_8378  ->
      match uu___109_8378 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___110_8430 =
            match uu___110_8430 with
            | Rec_binding uu____8431 -> true
            | uu____8432 -> false  in
          let this_env =
            let uu___124_8434 = env  in
            let uu____8435 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___124_8434.curmodule);
              curmonad = (uu___124_8434.curmonad);
              modules = (uu___124_8434.modules);
              scope_mods = uu____8435;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___124_8434.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___124_8434.sigaccum);
              sigmap = (uu___124_8434.sigmap);
              iface = (uu___124_8434.iface);
              admitted_iface = (uu___124_8434.admitted_iface);
              expect_typ = (uu___124_8434.expect_typ);
              docs = (uu___124_8434.docs);
              remaining_iface_decls = (uu___124_8434.remaining_iface_decls);
              syntax_only = (uu___124_8434.syntax_only);
              ds_hooks = (uu___124_8434.ds_hooks)
            }  in
          let uu____8438 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8438 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8457 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___125_8484 = env  in
      {
        curmodule = (uu___125_8484.curmodule);
        curmonad = (uu___125_8484.curmonad);
        modules = (uu___125_8484.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___125_8484.exported_ids);
        trans_exported_ids = (uu___125_8484.trans_exported_ids);
        includes = (uu___125_8484.includes);
        sigaccum = (uu___125_8484.sigaccum);
        sigmap = (uu___125_8484.sigmap);
        iface = (uu___125_8484.iface);
        admitted_iface = (uu___125_8484.admitted_iface);
        expect_typ = (uu___125_8484.expect_typ);
        docs = (uu___125_8484.docs);
        remaining_iface_decls = (uu___125_8484.remaining_iface_decls);
        syntax_only = (uu___125_8484.syntax_only);
        ds_hooks = (uu___125_8484.ds_hooks)
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
        let uu____8549 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____8549
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____8551 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____8551)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
           in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____8581) ->
              let uu____8586 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____8586 with
               | FStar_Pervasives_Native.Some l1 ->
                   let uu____8590 = FStar_Ident.range_of_lid l1  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____8590
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>"  in
        let uu____8595 =
          let uu____8600 =
            let uu____8601 = FStar_Ident.text_of_lid l  in
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              uu____8601 r
             in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8600)  in
        let uu____8602 = FStar_Ident.range_of_lid l  in
        FStar_Errors.raise_error uu____8595 uu____8602  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____8611 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____8620 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____8627 -> (false, true)
          | uu____8636 -> (false, false)  in
        match uu____8611 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____8642 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____8648 =
                     let uu____8649 = unique any_val exclude_interface env l
                        in
                     Prims.op_Negation uu____8649  in
                   if uu____8648
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None)
               in
            (match uu____8642 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____8654 ->
                 (extract_record env globals s;
                  (let uu___126_8680 = env  in
                   {
                     curmodule = (uu___126_8680.curmodule);
                     curmonad = (uu___126_8680.curmonad);
                     modules = (uu___126_8680.modules);
                     scope_mods = (uu___126_8680.scope_mods);
                     exported_ids = (uu___126_8680.exported_ids);
                     trans_exported_ids = (uu___126_8680.trans_exported_ids);
                     includes = (uu___126_8680.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___126_8680.sigmap);
                     iface = (uu___126_8680.iface);
                     admitted_iface = (uu___126_8680.admitted_iface);
                     expect_typ = (uu___126_8680.expect_typ);
                     docs = (uu___126_8680.docs);
                     remaining_iface_decls =
                       (uu___126_8680.remaining_iface_decls);
                     syntax_only = (uu___126_8680.syntax_only);
                     ds_hooks = (uu___126_8680.ds_hooks)
                   })))
         in
      let env2 =
        let uu___127_8682 = env1  in
        let uu____8683 = FStar_ST.op_Bang globals  in
        {
          curmodule = (uu___127_8682.curmodule);
          curmonad = (uu___127_8682.curmonad);
          modules = (uu___127_8682.modules);
          scope_mods = uu____8683;
          exported_ids = (uu___127_8682.exported_ids);
          trans_exported_ids = (uu___127_8682.trans_exported_ids);
          includes = (uu___127_8682.includes);
          sigaccum = (uu___127_8682.sigaccum);
          sigmap = (uu___127_8682.sigmap);
          iface = (uu___127_8682.iface);
          admitted_iface = (uu___127_8682.admitted_iface);
          expect_typ = (uu___127_8682.expect_typ);
          docs = (uu___127_8682.docs);
          remaining_iface_decls = (uu___127_8682.remaining_iface_decls);
          syntax_only = (uu___127_8682.syntax_only);
          ds_hooks = (uu___127_8682.ds_hooks)
        }  in
      let uu____8735 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8761) ->
            let uu____8770 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____8770)
        | uu____8797 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____8735 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____8856  ->
                   match uu____8856 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____8878 =
                                  let uu____8881 = FStar_ST.op_Bang globals
                                     in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____8881
                                   in
                                FStar_ST.op_Colon_Equals globals uu____8878);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____8983 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____8983.FStar_Ident.str  in
                                    ((let uu____8985 =
                                        get_exported_id_set env3 modul  in
                                      match uu____8985 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____9018 =
                                            let uu____9019 =
                                              FStar_ST.op_Bang
                                                my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____9019
                                             in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____9018
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
              let uu___128_9123 = env3  in
              let uu____9124 = FStar_ST.op_Bang globals  in
              {
                curmodule = (uu___128_9123.curmodule);
                curmonad = (uu___128_9123.curmonad);
                modules = (uu___128_9123.modules);
                scope_mods = uu____9124;
                exported_ids = (uu___128_9123.exported_ids);
                trans_exported_ids = (uu___128_9123.trans_exported_ids);
                includes = (uu___128_9123.includes);
                sigaccum = (uu___128_9123.sigaccum);
                sigmap = (uu___128_9123.sigmap);
                iface = (uu___128_9123.iface);
                admitted_iface = (uu___128_9123.admitted_iface);
                expect_typ = (uu___128_9123.expect_typ);
                docs = (uu___128_9123.docs);
                remaining_iface_decls = (uu___128_9123.remaining_iface_decls);
                syntax_only = (uu___128_9123.syntax_only);
                ds_hooks = (uu___128_9123.ds_hooks)
              }  in
            env4))
  
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9186 =
        let uu____9191 = resolve_module_name env ns false  in
        match uu____9191 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9205 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9221  ->
                      match uu____9221 with
                      | (m,uu____9227) ->
                          let uu____9228 =
                            let uu____9229 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____9229 "."  in
                          let uu____9230 =
                            let uu____9231 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____9231 "."  in
                          FStar_Util.starts_with uu____9228 uu____9230))
               in
            if uu____9205
            then (ns, Open_namespace)
            else
              (let uu____9237 =
                 let uu____9242 =
                   let uu____9243 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9243
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9242)  in
               let uu____9244 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9237 uu____9244)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____9186 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9265 = resolve_module_name env ns false  in
      match uu____9265 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9273 = current_module env1  in
              uu____9273.FStar_Ident.str  in
            (let uu____9275 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9275 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9299 =
                   let uu____9302 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9302
                    in
                 FStar_ST.op_Colon_Equals incl uu____9299);
            (match () with
             | () ->
                 let uu____9403 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____9403 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9423 =
                          let uu____9442 = get_exported_id_set env1 curmod
                             in
                          let uu____9450 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____9442, uu____9450)  in
                        match uu____9423 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____9515 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____9515  in
                              let ex = cur_exports k  in
                              (let uu____9649 =
                                 let uu____9650 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____9650 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____9649);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____9758 =
                                     let uu____9759 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____9759 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____9758)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____9852 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____9876 =
                        let uu____9881 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____9881)
                         in
                      let uu____9882 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____9876 uu____9882))))
      | uu____9883 ->
          let uu____9886 =
            let uu____9891 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____9891)  in
          let uu____9892 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____9886 uu____9892
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____9908 = module_is_defined env l  in
        if uu____9908
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____9912 =
             let uu____9917 =
               let uu____9918 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____9918  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____9917)  in
           let uu____9919 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____9912 uu____9919)
  
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
            ((let uu____9941 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____9941 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____9945 = FStar_Ident.range_of_lid l  in
                  let uu____9946 =
                    let uu____9951 =
                      let uu____9952 = FStar_Ident.string_of_lid l  in
                      let uu____9953 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____9954 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____9952 uu____9953 uu____9954
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____9951)  in
                  FStar_Errors.log_issue uu____9945 uu____9946);
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
                      let uu____9994 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____9994 ->
                      let uu____9997 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____9997 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____10010;
                              FStar_Syntax_Syntax.sigrng = uu____10011;
                              FStar_Syntax_Syntax.sigquals = uu____10012;
                              FStar_Syntax_Syntax.sigmeta = uu____10013;
                              FStar_Syntax_Syntax.sigattrs = uu____10014;_},uu____10015)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____10030;
                              FStar_Syntax_Syntax.sigrng = uu____10031;
                              FStar_Syntax_Syntax.sigquals = uu____10032;
                              FStar_Syntax_Syntax.sigmeta = uu____10033;
                              FStar_Syntax_Syntax.sigattrs = uu____10034;_},uu____10035)
                           -> lids
                       | uu____10060 ->
                           ((let uu____10068 =
                               let uu____10069 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____10069  in
                             if uu____10068
                             then
                               let uu____10070 = FStar_Ident.range_of_lid l
                                  in
                               let uu____10071 =
                                 let uu____10076 =
                                   let uu____10077 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____10077
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____10076)
                                  in
                               FStar_Errors.log_issue uu____10070 uu____10071
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___129_10088 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___129_10088.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___129_10088.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___129_10088.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___129_10088.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____10089 -> lids) [])
         in
      let uu___130_10090 = m  in
      let uu____10091 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____10101,uu____10102) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___131_10105 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___131_10105.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___131_10105.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___131_10105.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___131_10105.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____10106 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___130_10090.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____10091;
        FStar_Syntax_Syntax.exports =
          (uu___130_10090.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___130_10090.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10127) ->
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
                                (lid,uu____10147,uu____10148,uu____10149,uu____10150,uu____10151)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____10164,uu____10165)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____10180 =
                                        let uu____10187 =
                                          let uu____10190 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____10191 =
                                            let uu____10198 =
                                              let uu____10199 =
                                                let uu____10212 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____10212)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____10199
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____10198
                                             in
                                          uu____10191
                                            FStar_Pervasives_Native.None
                                            uu____10190
                                           in
                                        (lid, univ_names, uu____10187)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____10180
                                       in
                                    let se2 =
                                      let uu___132_10219 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___132_10219.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___132_10219.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___132_10219.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____10225 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____10228,uu____10229) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____10235,lbs),uu____10237)
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
                             let uu____10258 =
                               let uu____10259 =
                                 let uu____10260 =
                                   let uu____10263 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____10263.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____10260.FStar_Syntax_Syntax.v  in
                               uu____10259.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____10258))
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
                               let uu____10277 =
                                 let uu____10280 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____10280.FStar_Syntax_Syntax.fv_name  in
                               uu____10277.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___133_10285 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___133_10285.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___133_10285.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___133_10285.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____10295 -> ()));
      (let curmod =
         let uu____10297 = current_module env  in uu____10297.FStar_Ident.str
          in
       (let uu____10299 =
          let uu____10318 = get_exported_id_set env curmod  in
          let uu____10326 = get_trans_exported_id_set env curmod  in
          (uu____10318, uu____10326)  in
        match uu____10299 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____10391 = cur_ex eikind  in
                FStar_ST.op_Bang uu____10391  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____10524 =
                let uu____10525 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____10525  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____10524  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____10618 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___134_10638 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___134_10638.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___134_10638.exported_ids);
                    trans_exported_ids = (uu___134_10638.trans_exported_ids);
                    includes = (uu___134_10638.includes);
                    sigaccum = [];
                    sigmap = (uu___134_10638.sigmap);
                    iface = (uu___134_10638.iface);
                    admitted_iface = (uu___134_10638.admitted_iface);
                    expect_typ = (uu___134_10638.expect_typ);
                    docs = (uu___134_10638.docs);
                    remaining_iface_decls =
                      (uu___134_10638.remaining_iface_decls);
                    syntax_only = (uu___134_10638.syntax_only);
                    ds_hooks = (uu___134_10638.ds_hooks)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    push_record_cache ();
    (let uu____10667 =
       let uu____10670 = FStar_ST.op_Bang stack  in env :: uu____10670  in
     FStar_ST.op_Colon_Equals stack uu____10667);
    (let uu___135_10727 = env  in
     let uu____10728 = FStar_Util.smap_copy (sigmap env)  in
     let uu____10739 = FStar_Util.smap_copy env.docs  in
     {
       curmodule = (uu___135_10727.curmodule);
       curmonad = (uu___135_10727.curmonad);
       modules = (uu___135_10727.modules);
       scope_mods = (uu___135_10727.scope_mods);
       exported_ids = (uu___135_10727.exported_ids);
       trans_exported_ids = (uu___135_10727.trans_exported_ids);
       includes = (uu___135_10727.includes);
       sigaccum = (uu___135_10727.sigaccum);
       sigmap = uu____10728;
       iface = (uu___135_10727.iface);
       admitted_iface = (uu___135_10727.admitted_iface);
       expect_typ = (uu___135_10727.expect_typ);
       docs = uu____10739;
       remaining_iface_decls = (uu___135_10727.remaining_iface_decls);
       syntax_only = (uu___135_10727.syntax_only);
       ds_hooks = (uu___135_10727.ds_hooks)
     })
  
let (pop : unit -> env) =
  fun uu____10746  ->
    let uu____10747 = FStar_ST.op_Bang stack  in
    match uu____10747 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10810 -> failwith "Impossible: Too many pops"
  
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____10830 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____10833 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____10867 = FStar_Util.smap_try_find sm' k  in
              match uu____10867 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___136_10892 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___136_10892.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___136_10892.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___136_10892.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___136_10892.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____10893 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____10898 -> ()));
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
      let uu____10921 = finish env modul1  in (uu____10921, modul1)
  
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
      let uu____11007 =
        let uu____11010 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____11010  in
      FStar_Util.set_elements uu____11007  in
    let fields =
      let uu____11132 =
        let uu____11135 = e Exported_id_field  in
        FStar_ST.op_Bang uu____11135  in
      FStar_Util.set_elements uu____11132  in
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
          let uu____11294 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____11294  in
        let fields =
          let uu____11304 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____11304  in
        (fun uu___111_11309  ->
           match uu___111_11309 with
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
  'Auu____11437 .
    'Auu____11437 Prims.list FStar_Pervasives_Native.option ->
      'Auu____11437 Prims.list FStar_ST.ref
  =
  fun uu___112_11450  ->
    match uu___112_11450 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____11491 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____11491 as_exported_ids  in
      let uu____11497 = as_ids_opt env.exported_ids  in
      let uu____11500 = as_ids_opt env.trans_exported_ids  in
      let uu____11503 =
        let uu____11508 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____11508 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____11497;
        mii_trans_exported_ids = uu____11500;
        mii_includes = uu____11503
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
                let uu____11627 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____11627 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___113_11647 =
                  match uu___113_11647 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____11659  ->
                     match uu____11659 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____11683 =
                    let uu____11688 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____11688, Open_namespace)  in
                  [uu____11683]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____11718 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____11718);
              (match () with
               | () ->
                   ((let uu____11745 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____11745);
                    (match () with
                     | () ->
                         ((let uu____11772 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____11772);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___137_11804 = env1  in
                                 let uu____11805 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___137_11804.curmonad);
                                   modules = (uu___137_11804.modules);
                                   scope_mods = uu____11805;
                                   exported_ids =
                                     (uu___137_11804.exported_ids);
                                   trans_exported_ids =
                                     (uu___137_11804.trans_exported_ids);
                                   includes = (uu___137_11804.includes);
                                   sigaccum = (uu___137_11804.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___137_11804.expect_typ);
                                   docs = (uu___137_11804.docs);
                                   remaining_iface_decls =
                                     (uu___137_11804.remaining_iface_decls);
                                   syntax_only = (uu___137_11804.syntax_only);
                                   ds_hooks = (uu___137_11804.ds_hooks)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____11817 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____11843  ->
                      match uu____11843 with
                      | (l,uu____11849) -> FStar_Ident.lid_equals l mname))
               in
            match uu____11817 with
            | FStar_Pervasives_Native.None  ->
                let uu____11858 = prep env  in (uu____11858, false)
            | FStar_Pervasives_Native.Some (uu____11859,m) ->
                ((let uu____11866 =
                    (let uu____11869 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____11869) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____11866
                  then
                    let uu____11870 =
                      let uu____11875 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____11875)
                       in
                    let uu____11876 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____11870 uu____11876
                  else ());
                 (let uu____11878 =
                    let uu____11879 = push env  in prep uu____11879  in
                  (uu____11878, true)))
  
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
          let uu___138_11891 = env  in
          {
            curmodule = (uu___138_11891.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___138_11891.modules);
            scope_mods = (uu___138_11891.scope_mods);
            exported_ids = (uu___138_11891.exported_ids);
            trans_exported_ids = (uu___138_11891.trans_exported_ids);
            includes = (uu___138_11891.includes);
            sigaccum = (uu___138_11891.sigaccum);
            sigmap = (uu___138_11891.sigmap);
            iface = (uu___138_11891.iface);
            admitted_iface = (uu___138_11891.admitted_iface);
            expect_typ = (uu___138_11891.expect_typ);
            docs = (uu___138_11891.docs);
            remaining_iface_decls = (uu___138_11891.remaining_iface_decls);
            syntax_only = (uu___138_11891.syntax_only);
            ds_hooks = (uu___138_11891.ds_hooks)
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
        let uu____11925 = lookup1 lid  in
        match uu____11925 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____11938  ->
                   match uu____11938 with
                   | (lid1,uu____11944) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____11946 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____11946  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____11950 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____11951 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____11950 uu____11951  in
                 let uu____11952 = resolve_module_name env modul true  in
                 match uu____11952 with
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
            let uu____11961 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____11961
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____11989 = lookup1 id1  in
      match uu____11989 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  
let (mk_copy : env -> env) =
  fun en  ->
    let uu___139_11998 = en  in
    let uu____11999 = FStar_Util.smap_copy en.exported_ids  in
    let uu____12004 = FStar_Util.smap_copy en.trans_exported_ids  in
    let uu____12009 = FStar_Util.smap_copy en.sigmap  in
    let uu____12020 = FStar_Util.smap_copy en.docs  in
    {
      curmodule = (uu___139_11998.curmodule);
      curmonad = (uu___139_11998.curmonad);
      modules = (uu___139_11998.modules);
      scope_mods = (uu___139_11998.scope_mods);
      exported_ids = uu____11999;
      trans_exported_ids = uu____12004;
      includes = (uu___139_11998.includes);
      sigaccum = (uu___139_11998.sigaccum);
      sigmap = uu____12009;
      iface = (uu___139_11998.iface);
      admitted_iface = (uu___139_11998.admitted_iface);
      expect_typ = (uu___139_11998.expect_typ);
      docs = uu____12020;
      remaining_iface_decls = (uu___139_11998.remaining_iface_decls);
      syntax_only = (uu___139_11998.syntax_only);
      ds_hooks = (uu___139_11998.ds_hooks)
    }
  