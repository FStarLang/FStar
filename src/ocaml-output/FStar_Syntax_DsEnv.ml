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
let uu___is_Open_module : open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____22 -> false
  
let uu___is_Open_namespace : open_kind -> Prims.bool =
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
let __proj__Mkrecord_or_dc__item__typename :
  record_or_dc -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__typename
  
let __proj__Mkrecord_or_dc__item__constrname :
  record_or_dc -> FStar_Ident.ident =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__constrname
  
let __proj__Mkrecord_or_dc__item__parms :
  record_or_dc -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__parms
  
let __proj__Mkrecord_or_dc__item__fields :
  record_or_dc ->
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__fields
  
let __proj__Mkrecord_or_dc__item__is_private_or_abstract :
  record_or_dc -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__is_private_or_abstract
  
let __proj__Mkrecord_or_dc__item__is_record : record_or_dc -> Prims.bool =
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
let uu___is_Local_binding : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Local_binding _0 -> true | uu____219 -> false
  
let __proj__Local_binding__item___0 : scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let uu___is_Rec_binding : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____233 -> false
  
let __proj__Rec_binding__item___0 : scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let uu___is_Module_abbrev : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____247 -> false
  
let __proj__Module_abbrev__item___0 : scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let uu___is_Open_module_or_namespace : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____261 -> false
  
let __proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let uu___is_Top_level_def : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____275 -> false
  
let __proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let uu___is_Record_or_dc : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____289 -> false
  
let __proj__Record_or_dc__item___0 : scope_mod -> record_or_dc =
  fun projectee  -> match projectee with | Record_or_dc _0 -> _0 
type string_set = Prims.string FStar_Util.set[@@deriving show]
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field [@@deriving show]
let uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____304 -> false
  
let uu___is_Exported_id_field : exported_id_kind -> Prims.bool =
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
let __proj__Mkenv__item__curmodule :
  env -> FStar_Ident.lident FStar_Pervasives_Native.option =
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
  
let __proj__Mkenv__item__curmonad :
  env -> FStar_Ident.ident FStar_Pervasives_Native.option =
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
  
let __proj__Mkenv__item__modules :
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
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
  
let __proj__Mkenv__item__scope_mods : env -> scope_mod Prims.list =
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
  
let __proj__Mkenv__item__exported_ids :
  env -> exported_id_set FStar_Util.smap =
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
  
let __proj__Mkenv__item__trans_exported_ids :
  env -> exported_id_set FStar_Util.smap =
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
  
let __proj__Mkenv__item__includes :
  env -> FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap =
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
  
let __proj__Mkenv__item__sigaccum : env -> FStar_Syntax_Syntax.sigelts =
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
  
let __proj__Mkenv__item__sigmap :
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
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
  
let __proj__Mkenv__item__iface : env -> Prims.bool =
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
  
let __proj__Mkenv__item__admitted_iface : env -> Prims.bool =
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
  
let __proj__Mkenv__item__expect_typ : env -> Prims.bool =
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
  
let __proj__Mkenv__item__docs : env -> FStar_Parser_AST.fsdoc FStar_Util.smap
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
        -> __fname__docs
  
let __proj__Mkenv__item__remaining_iface_decls :
  env ->
    (FStar_Ident.lident,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
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
  
let __proj__Mkenv__item__syntax_only : env -> Prims.bool =
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
  
let __proj__Mkenv__item__ds_hooks : env -> dsenv_hooks =
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
  
let __proj__Mkdsenv_hooks__item__ds_push_open_hook :
  dsenv_hooks -> env -> open_module_or_namespace -> unit =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_open_hook
  
let __proj__Mkdsenv_hooks__item__ds_push_include_hook :
  dsenv_hooks -> env -> FStar_Ident.lident -> unit =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_include_hook
  
let __proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook :
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> unit =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook = __fname__ds_push_open_hook;
        ds_push_include_hook = __fname__ds_push_include_hook;
        ds_push_module_abbrev_hook = __fname__ds_push_module_abbrev_hook;_}
        -> __fname__ds_push_module_abbrev_hook
  
type 'a withenv = env -> ('a,env) FStar_Pervasives_Native.tuple2[@@deriving
                                                                  show]
let default_ds_hooks : dsenv_hooks =
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
let uu___is_Term_name : foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____1773 -> false
  
let __proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool,FStar_Syntax_Syntax.attribute
                                          Prims.list)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let uu___is_Eff_name : foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1815 -> false
  
let __proj__Eff_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Eff_name _0 -> _0 
let set_iface : env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___112_1845 = env  in
      {
        curmodule = (uu___112_1845.curmodule);
        curmonad = (uu___112_1845.curmonad);
        modules = (uu___112_1845.modules);
        scope_mods = (uu___112_1845.scope_mods);
        exported_ids = (uu___112_1845.exported_ids);
        trans_exported_ids = (uu___112_1845.trans_exported_ids);
        includes = (uu___112_1845.includes);
        sigaccum = (uu___112_1845.sigaccum);
        sigmap = (uu___112_1845.sigmap);
        iface = b;
        admitted_iface = (uu___112_1845.admitted_iface);
        expect_typ = (uu___112_1845.expect_typ);
        docs = (uu___112_1845.docs);
        remaining_iface_decls = (uu___112_1845.remaining_iface_decls);
        syntax_only = (uu___112_1845.syntax_only);
        ds_hooks = (uu___112_1845.ds_hooks)
      }
  
let iface : env -> Prims.bool = fun e  -> e.iface 
let set_admitted_iface : env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___113_1861 = e  in
      {
        curmodule = (uu___113_1861.curmodule);
        curmonad = (uu___113_1861.curmonad);
        modules = (uu___113_1861.modules);
        scope_mods = (uu___113_1861.scope_mods);
        exported_ids = (uu___113_1861.exported_ids);
        trans_exported_ids = (uu___113_1861.trans_exported_ids);
        includes = (uu___113_1861.includes);
        sigaccum = (uu___113_1861.sigaccum);
        sigmap = (uu___113_1861.sigmap);
        iface = (uu___113_1861.iface);
        admitted_iface = b;
        expect_typ = (uu___113_1861.expect_typ);
        docs = (uu___113_1861.docs);
        remaining_iface_decls = (uu___113_1861.remaining_iface_decls);
        syntax_only = (uu___113_1861.syntax_only);
        ds_hooks = (uu___113_1861.ds_hooks)
      }
  
let admitted_iface : env -> Prims.bool = fun e  -> e.admitted_iface 
let set_expect_typ : env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___114_1877 = e  in
      {
        curmodule = (uu___114_1877.curmodule);
        curmonad = (uu___114_1877.curmonad);
        modules = (uu___114_1877.modules);
        scope_mods = (uu___114_1877.scope_mods);
        exported_ids = (uu___114_1877.exported_ids);
        trans_exported_ids = (uu___114_1877.trans_exported_ids);
        includes = (uu___114_1877.includes);
        sigaccum = (uu___114_1877.sigaccum);
        sigmap = (uu___114_1877.sigmap);
        iface = (uu___114_1877.iface);
        admitted_iface = (uu___114_1877.admitted_iface);
        expect_typ = b;
        docs = (uu___114_1877.docs);
        remaining_iface_decls = (uu___114_1877.remaining_iface_decls);
        syntax_only = (uu___114_1877.syntax_only);
        ds_hooks = (uu___114_1877.ds_hooks)
      }
  
let expect_typ : env -> Prims.bool = fun e  -> e.expect_typ 
let all_exported_id_kinds : exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type] 
let transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list =
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
  
let open_modules :
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  = fun e  -> e.modules 
let open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    FStar_List.filter_map
      (fun uu___81_2052  ->
         match uu___81_2052 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2057 -> FStar_Pervasives_Native.None) env.scope_mods
  
let set_current_module : env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___115_2068 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___115_2068.curmonad);
        modules = (uu___115_2068.modules);
        scope_mods = (uu___115_2068.scope_mods);
        exported_ids = (uu___115_2068.exported_ids);
        trans_exported_ids = (uu___115_2068.trans_exported_ids);
        includes = (uu___115_2068.includes);
        sigaccum = (uu___115_2068.sigaccum);
        sigmap = (uu___115_2068.sigmap);
        iface = (uu___115_2068.iface);
        admitted_iface = (uu___115_2068.admitted_iface);
        expect_typ = (uu___115_2068.expect_typ);
        docs = (uu___115_2068.docs);
        remaining_iface_decls = (uu___115_2068.remaining_iface_decls);
        syntax_only = (uu___115_2068.syntax_only);
        ds_hooks = (uu___115_2068.ds_hooks)
      }
  
let current_module : env -> FStar_Ident.lident =
  fun env  ->
    match env.curmodule with
    | FStar_Pervasives_Native.None  -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
  
let iface_decls :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option
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
  
let set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
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
            let uu___116_2258 = env  in
            {
              curmodule = (uu___116_2258.curmodule);
              curmonad = (uu___116_2258.curmonad);
              modules = (uu___116_2258.modules);
              scope_mods = (uu___116_2258.scope_mods);
              exported_ids = (uu___116_2258.exported_ids);
              trans_exported_ids = (uu___116_2258.trans_exported_ids);
              includes = (uu___116_2258.includes);
              sigaccum = (uu___116_2258.sigaccum);
              sigmap = (uu___116_2258.sigmap);
              iface = (uu___116_2258.iface);
              admitted_iface = (uu___116_2258.admitted_iface);
              expect_typ = (uu___116_2258.expect_typ);
              docs = (uu___116_2258.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___116_2258.syntax_only);
              ds_hooks = (uu___116_2258.ds_hooks)
            }
  
let qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id 
let qualify : env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2285 = current_module env  in qual uu____2285 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2287 =
            let uu____2288 = current_module env  in qual uu____2288 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2287 id1
  
let syntax_only : env -> Prims.bool = fun env  -> env.syntax_only 
let set_syntax_only : env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___117_2304 = env  in
      {
        curmodule = (uu___117_2304.curmodule);
        curmonad = (uu___117_2304.curmonad);
        modules = (uu___117_2304.modules);
        scope_mods = (uu___117_2304.scope_mods);
        exported_ids = (uu___117_2304.exported_ids);
        trans_exported_ids = (uu___117_2304.trans_exported_ids);
        includes = (uu___117_2304.includes);
        sigaccum = (uu___117_2304.sigaccum);
        sigmap = (uu___117_2304.sigmap);
        iface = (uu___117_2304.iface);
        admitted_iface = (uu___117_2304.admitted_iface);
        expect_typ = (uu___117_2304.expect_typ);
        docs = (uu___117_2304.docs);
        remaining_iface_decls = (uu___117_2304.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___117_2304.ds_hooks)
      }
  
let ds_hooks : env -> dsenv_hooks = fun env  -> env.ds_hooks 
let set_ds_hooks : env -> dsenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___118_2320 = env  in
      {
        curmodule = (uu___118_2320.curmodule);
        curmonad = (uu___118_2320.curmonad);
        modules = (uu___118_2320.modules);
        scope_mods = (uu___118_2320.scope_mods);
        exported_ids = (uu___118_2320.exported_ids);
        trans_exported_ids = (uu___118_2320.trans_exported_ids);
        includes = (uu___118_2320.includes);
        sigaccum = (uu___118_2320.sigaccum);
        sigmap = (uu___118_2320.sigmap);
        iface = (uu___118_2320.iface);
        admitted_iface = (uu___118_2320.admitted_iface);
        expect_typ = (uu___118_2320.expect_typ);
        docs = (uu___118_2320.docs);
        remaining_iface_decls = (uu___118_2320.remaining_iface_decls);
        syntax_only = (uu___118_2320.syntax_only);
        ds_hooks = hooks
      }
  
let new_sigmap : 'Auu____2325 . unit -> 'Auu____2325 FStar_Util.smap =
  fun uu____2332  -> FStar_Util.smap_create (Prims.lift_native_int (100)) 
let empty_env : unit -> env =
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
  
let sigmap :
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
  = fun env  -> env.sigmap 
let has_all_in_scope : env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____2406  ->
         match uu____2406 with
         | (m,uu____2412) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___119_2424 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___119_2424.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___120_2425 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___120_2425.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___120_2425.FStar_Syntax_Syntax.sort)
      }
  
let bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r) 
let unmangleMap :
  (Prims.string,Prims.string,FStar_Syntax_Syntax.delta_depth,FStar_Syntax_Syntax.fv_qual
                                                               FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple4 Prims.list
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational,
    FStar_Pervasives_Native.None)]
  
let unmangleOpName :
  FStar_Ident.ident ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
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
    fun uu___82_2667  ->
      match uu___82_2667 with
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
  
let get_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option
  = fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname 
let get_trans_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option
  =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname 
let string_of_exported_id_kind : exported_id_kind -> Prims.string =
  fun uu___83_2806  ->
    match uu___83_2806 with
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
              let rec aux uu___84_2877 =
                match uu___84_2877 with
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
  
let is_exported_id_field : exported_id_kind -> Prims.bool =
  fun uu___85_3126  ->
    match uu___85_3126 with
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
                  let check_local_binding_id uu___86_3248 =
                    match uu___86_3248 with
                    | (id',uu____3250,uu____3251) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___87_3257 =
                    match uu___87_3257 with
                    | (id',uu____3259,uu____3260) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3264 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3264  in
                  let proc uu___88_3272 =
                    match uu___88_3272 with
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
                  let rec aux uu___89_3295 =
                    match uu___89_3295 with
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
  
let try_lookup_id :
  env ->
    FStar_Ident.ident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
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
  
let lid_is_curmod : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some m -> FStar_Ident.lid_equals lid m
  
let module_is_defined : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (lid_is_curmod env lid) ||
        (FStar_List.existsb
           (fun x  ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env.modules)
  
let resolve_module_name :
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns  in
        let rec aux uu___90_3722 =
          match uu___90_3722 with
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
              (nslen = (Prims.lift_native_int (0))) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3757::q -> aux q  in
        aux env.scope_mods
  
let fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit =
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
  
let fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit =
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
  
let is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___91_3827  ->
             match uu___91_3827 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____3830 -> false) env.scope_mods
  
let namespace_is_open : env -> FStar_Ident.lident -> Prims.bool =
  fun env  -> fun lid  -> is_open env lid Open_namespace 
let module_is_open : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  -> (lid_is_curmod env lid) || (is_open env lid Open_module)
  
let shorten_module_path :
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
          FStar_Pervasives_Native.tuple2
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
    fun uu___92_4306  ->
      match uu___92_4306 with
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
  
let fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4478,uu____4479,uu____4480,l,uu____4482,uu____4483) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___93_4494  ->
               match uu___93_4494 with
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
  
let lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
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
  
let ns_of_lid_equals : FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      (let uu____4559 =
         let uu____4560 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4560  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4559) &&
        (let uu____4568 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4568 ns)
  
let try_lookup_name :
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid  in
          let k_global_def source_lid uu___98_4610 =
            match uu___98_4610 with
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
                               (fun uu___94_4724  ->
                                  match uu___94_4724 with
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
                                   (fun uu___95_4736  ->
                                      match uu___95_4736 with
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
                                (fun uu___96_4750  ->
                                   match uu___96_4750 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4751 -> false))
                            in
                         if uu____4746
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd  in
                       let uu____4753 =
                         FStar_Util.find_map quals
                           (fun uu___97_4758  ->
                              match uu___97_4758 with
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
                                (Prims.lift_native_int (1)))
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
  
let try_lookup_effect_name' :
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____4980 = try_lookup_name true exclude_interf env lid  in
        match uu____4980 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4995 -> FStar_Pervasives_Native.None
  
let try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____5014 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5014 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5029 -> FStar_Pervasives_Native.None
  
let try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
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
  
let try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
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
  
let is_effect_name : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____5222 = try_lookup_effect_name env lid  in
      match uu____5222 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5225 -> true
  
let try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
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
  
let lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___99_5362 =
        match uu___99_5362 with
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
  
let try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
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
  
let try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___100_5494 =
        match uu___100_5494 with
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
  
let try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___101_5568 =
        match uu___101_5568 with
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
  
let empty_include_smap :
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = new_sigmap () 
let empty_exported_id_smap : exported_id_set FStar_Util.smap = new_sigmap () 
let try_lookup_lid' :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                                 Prims.list)
            FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
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
  
let drop_attributes :
  (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                         Prims.list)
    FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,mut,uu____5770) ->
        FStar_Pervasives_Native.Some (t, mut)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let try_lookup_lid_with_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                             Prims.list)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l 
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____5845 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____5845 drop_attributes
  
let resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
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
  
let shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____5921 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____5921 with
      | (uu____5930,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid =
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
  
let try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool,FStar_Syntax_Syntax.attribute
                                             Prims.list)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___121_5992 = env  in
        {
          curmodule = (uu___121_5992.curmodule);
          curmonad = (uu___121_5992.curmonad);
          modules = (uu___121_5992.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___121_5992.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___121_5992.sigaccum);
          sigmap = (uu___121_5992.sigmap);
          iface = (uu___121_5992.iface);
          admitted_iface = (uu___121_5992.admitted_iface);
          expect_typ = (uu___121_5992.expect_typ);
          docs = (uu___121_5992.docs);
          remaining_iface_decls = (uu___121_5992.remaining_iface_decls);
          syntax_only = (uu___121_5992.syntax_only);
          ds_hooks = (uu___121_5992.ds_hooks)
        }  in
      try_lookup_lid_with_attributes env' l
  
let try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____6015 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____6015 drop_attributes
  
let try_lookup_doc :
  env ->
    FStar_Ident.lid -> FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option
  = fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str 
let try_lookup_datacon :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 se =
        match se with
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
                   (fun uu___102_6105  ->
                      match uu___102_6105 with
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
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____6138 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____6138
        | uu____6139 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6145  -> FStar_Pervasives_Native.None)
        (fun uu____6147  -> FStar_Pervasives_Native.None) k_global_def
  
let find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___103_6180 =
        match uu___103_6180 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6189,uu____6190,uu____6191,uu____6192,datas,uu____6194);
             FStar_Syntax_Syntax.sigrng = uu____6195;
             FStar_Syntax_Syntax.sigquals = uu____6196;
             FStar_Syntax_Syntax.sigmeta = uu____6197;
             FStar_Syntax_Syntax.sigattrs = uu____6198;_},uu____6199)
            -> FStar_Pervasives_Native.Some datas
        | uu____6214 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6224  -> FStar_Pervasives_Native.None)
        (fun uu____6228  -> FStar_Pervasives_Native.None) k_global_def
  
let record_cache_aux_with_filter :
  ((unit -> unit,unit -> unit,unit -> record_or_dc Prims.list,record_or_dc ->
                                                                unit)
     FStar_Pervasives_Native.tuple4,unit -> unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____6280 =
    let uu____6281 =
      let uu____6286 =
        let uu____6289 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6289  in
      let uu____6349 = FStar_ST.op_Bang record_cache  in uu____6286 ::
        uu____6349
       in
    FStar_ST.op_Colon_Equals record_cache uu____6281  in
  let pop1 uu____6467 =
    let uu____6468 =
      let uu____6473 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6473  in
    FStar_ST.op_Colon_Equals record_cache uu____6468  in
  let peek1 uu____6593 =
    let uu____6594 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6594  in
  let insert r =
    let uu____6660 =
      let uu____6665 = let uu____6668 = peek1 ()  in r :: uu____6668  in
      let uu____6671 =
        let uu____6676 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6676  in
      uu____6665 :: uu____6671  in
    FStar_ST.op_Colon_Equals record_cache uu____6660  in
  let filter1 uu____6796 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____6805 =
      let uu____6810 =
        let uu____6815 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____6815  in
      filtered :: uu____6810  in
    FStar_ST.op_Colon_Equals record_cache uu____6805  in
  let aux = (push1, pop1, peek1, insert)  in (aux, filter1) 
let record_cache_aux :
  (unit -> unit,unit -> unit,unit -> record_or_dc Prims.list,record_or_dc ->
                                                               unit)
    FStar_Pervasives_Native.tuple4
  =
  let uu____7014 = record_cache_aux_with_filter  in
  match uu____7014 with | (aux,uu____7067) -> aux 
let filter_record_cache : unit -> unit =
  let uu____7122 = record_cache_aux_with_filter  in
  match uu____7122 with | (uu____7155,filter1) -> filter1 
let push_record_cache : unit -> unit =
  let uu____7211 = record_cache_aux  in
  match uu____7211 with | (push1,uu____7238,uu____7239,uu____7240) -> push1 
let pop_record_cache : unit -> unit =
  let uu____7273 = record_cache_aux  in
  match uu____7273 with | (uu____7299,pop1,uu____7301,uu____7302) -> pop1 
let peek_record_cache : unit -> record_or_dc Prims.list =
  let uu____7337 = record_cache_aux  in
  match uu____7337 with | (uu____7365,uu____7366,peek1,uu____7368) -> peek1 
let insert_record_cache : record_or_dc -> unit =
  let uu____7401 = record_cache_aux  in
  match uu____7401 with | (uu____7427,uu____7428,uu____7429,insert) -> insert 
let extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref -> FStar_Syntax_Syntax.sigelt -> unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____7505) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___104_7523  ->
                   match uu___104_7523 with
                   | FStar_Syntax_Syntax.RecordType uu____7524 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7533 -> true
                   | uu____7542 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___105_7566  ->
                      match uu___105_7566 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____7568,uu____7569,uu____7570,uu____7571,uu____7572);
                          FStar_Syntax_Syntax.sigrng = uu____7573;
                          FStar_Syntax_Syntax.sigquals = uu____7574;
                          FStar_Syntax_Syntax.sigmeta = uu____7575;
                          FStar_Syntax_Syntax.sigattrs = uu____7576;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7585 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___106_7620  ->
                    match uu___106_7620 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____7624,uu____7625,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7627;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7629;
                        FStar_Syntax_Syntax.sigattrs = uu____7630;_} ->
                        let uu____7641 =
                          let uu____7642 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____7642  in
                        (match uu____7641 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____7648,t,uu____7650,uu____7651,uu____7652);
                             FStar_Syntax_Syntax.sigrng = uu____7653;
                             FStar_Syntax_Syntax.sigquals = uu____7654;
                             FStar_Syntax_Syntax.sigmeta = uu____7655;
                             FStar_Syntax_Syntax.sigattrs = uu____7656;_} ->
                             let uu____7665 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____7665 with
                              | (formals,uu____7679) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____7728  ->
                                            match uu____7728 with
                                            | (x,q) ->
                                                let uu____7741 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____7741
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____7798  ->
                                            match uu____7798 with
                                            | (x,q) ->
                                                let uu____7811 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____7811,
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
                                  ((let uu____7826 =
                                      let uu____7829 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____7829  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7826);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7942 =
                                            match uu____7942 with
                                            | (id1,uu____7950) ->
                                                let modul =
                                                  let uu____7956 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____7956.FStar_Ident.str
                                                   in
                                                let uu____7957 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____7957 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____7991 =
                                                         let uu____7992 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____7992
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7991);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8086 =
                                                               let uu____8087
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8087.FStar_Ident.ident
                                                                in
                                                             uu____8086.FStar_Ident.idText
                                                              in
                                                           let uu____8089 =
                                                             let uu____8090 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8090
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8089))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8194 -> ())
                    | uu____8195 -> ()))
        | uu____8196 -> ()
  
let try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8217 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8217 with
        | (ns,id1) ->
            let uu____8234 = peek_record_cache ()  in
            FStar_Util.find_map uu____8234
              (fun record  ->
                 let uu____8240 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8246  -> FStar_Pervasives_Native.None)
                   uu____8240)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8248  -> Cont_ignore) (fun uu____8250  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8256 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8256)
        (fun k  -> fun uu____8262  -> k)
  
let try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____8277 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8277 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8283 -> FStar_Pervasives_Native.None
  
let belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8301 = try_lookup_record_by_field_name env lid  in
        match uu____8301 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8305 =
              let uu____8306 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8306  in
            let uu____8307 =
              let uu____8308 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8308  in
            uu____8305 = uu____8307 ->
            let uu____8309 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8313  -> Cont_ok ())
               in
            (match uu____8309 with
             | Cont_ok uu____8314 -> true
             | uu____8315 -> false)
        | uu____8318 -> false
  
let try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____8337 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8337 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8347 =
            let uu____8352 =
              let uu____8353 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8354 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8353 uu____8354  in
            (uu____8352, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8347
      | uu____8359 -> FStar_Pervasives_Native.None
  
let string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____8385  ->
    let uu____8386 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8386
  
let exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____8413  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___107_8424  ->
      match uu___107_8424 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___108_8476 =
            match uu___108_8476 with
            | Rec_binding uu____8477 -> true
            | uu____8478 -> false  in
          let this_env =
            let uu___122_8480 = env  in
            let uu____8481 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___122_8480.curmodule);
              curmonad = (uu___122_8480.curmonad);
              modules = (uu___122_8480.modules);
              scope_mods = uu____8481;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___122_8480.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___122_8480.sigaccum);
              sigmap = (uu___122_8480.sigmap);
              iface = (uu___122_8480.iface);
              admitted_iface = (uu___122_8480.admitted_iface);
              expect_typ = (uu___122_8480.expect_typ);
              docs = (uu___122_8480.docs);
              remaining_iface_decls = (uu___122_8480.remaining_iface_decls);
              syntax_only = (uu___122_8480.syntax_only);
              ds_hooks = (uu___122_8480.ds_hooks)
            }  in
          let uu____8484 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8484 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8503 -> false
  
let push_scope_mod : env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___123_8530 = env  in
      {
        curmodule = (uu___123_8530.curmodule);
        curmonad = (uu___123_8530.curmonad);
        modules = (uu___123_8530.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___123_8530.exported_ids);
        trans_exported_ids = (uu___123_8530.trans_exported_ids);
        includes = (uu___123_8530.includes);
        sigaccum = (uu___123_8530.sigaccum);
        sigmap = (uu___123_8530.sigmap);
        iface = (uu___123_8530.iface);
        admitted_iface = (uu___123_8530.admitted_iface);
        expect_typ = (uu___123_8530.expect_typ);
        docs = (uu___123_8530.docs);
        remaining_iface_decls = (uu___123_8530.remaining_iface_decls);
        syntax_only = (uu___123_8530.syntax_only);
        ds_hooks = (uu___123_8530.ds_hooks)
      }
  
let push_bv' :
  env ->
    FStar_Ident.ident ->
      Prims.bool ->
        (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
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
  
let push_bv_mutable :
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x true 
let push_bv :
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x false 
let push_top_level_rec_binding :
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x  in
        let uu____8595 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____8595
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____8597 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____8597)
  
let push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
           in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____8627) ->
              let uu____8632 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____8632 with
               | FStar_Pervasives_Native.Some l1 ->
                   let uu____8636 = FStar_Ident.range_of_lid l1  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____8636
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>"  in
        let uu____8641 =
          let uu____8646 =
            let uu____8647 = FStar_Ident.text_of_lid l  in
            FStar_Util.format2
              "Duplicate top-level names [%s]; previously declared at %s"
              uu____8647 r
             in
          (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8646)  in
        let uu____8648 = FStar_Ident.range_of_lid l  in
        FStar_Errors.raise_error uu____8641 uu____8648  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____8657 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____8666 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____8673 -> (false, true)
          | uu____8682 -> (false, false)  in
        match uu____8657 with
        | (any_val,exclude_interface) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____8688 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____8694 =
                     let uu____8695 = unique any_val exclude_interface env l
                        in
                     Prims.op_Negation uu____8695  in
                   if uu____8694
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None)
               in
            (match uu____8688 with
             | FStar_Pervasives_Native.Some l -> err l
             | uu____8700 ->
                 (extract_record env globals s;
                  (let uu___124_8726 = env  in
                   {
                     curmodule = (uu___124_8726.curmodule);
                     curmonad = (uu___124_8726.curmonad);
                     modules = (uu___124_8726.modules);
                     scope_mods = (uu___124_8726.scope_mods);
                     exported_ids = (uu___124_8726.exported_ids);
                     trans_exported_ids = (uu___124_8726.trans_exported_ids);
                     includes = (uu___124_8726.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___124_8726.sigmap);
                     iface = (uu___124_8726.iface);
                     admitted_iface = (uu___124_8726.admitted_iface);
                     expect_typ = (uu___124_8726.expect_typ);
                     docs = (uu___124_8726.docs);
                     remaining_iface_decls =
                       (uu___124_8726.remaining_iface_decls);
                     syntax_only = (uu___124_8726.syntax_only);
                     ds_hooks = (uu___124_8726.ds_hooks)
                   })))
         in
      let env2 =
        let uu___125_8728 = env1  in
        let uu____8729 = FStar_ST.op_Bang globals  in
        {
          curmodule = (uu___125_8728.curmodule);
          curmonad = (uu___125_8728.curmonad);
          modules = (uu___125_8728.modules);
          scope_mods = uu____8729;
          exported_ids = (uu___125_8728.exported_ids);
          trans_exported_ids = (uu___125_8728.trans_exported_ids);
          includes = (uu___125_8728.includes);
          sigaccum = (uu___125_8728.sigaccum);
          sigmap = (uu___125_8728.sigmap);
          iface = (uu___125_8728.iface);
          admitted_iface = (uu___125_8728.admitted_iface);
          expect_typ = (uu___125_8728.expect_typ);
          docs = (uu___125_8728.docs);
          remaining_iface_decls = (uu___125_8728.remaining_iface_decls);
          syntax_only = (uu___125_8728.syntax_only);
          ds_hooks = (uu___125_8728.ds_hooks)
        }  in
      let uu____8781 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8807) ->
            let uu____8816 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____8816)
        | uu____8843 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____8781 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____8902  ->
                   match uu____8902 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____8924 =
                                  let uu____8927 = FStar_ST.op_Bang globals
                                     in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____8927
                                   in
                                FStar_ST.op_Colon_Equals globals uu____8924);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____9029 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____9029.FStar_Ident.str  in
                                    ((let uu____9031 =
                                        get_exported_id_set env3 modul  in
                                      match uu____9031 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____9064 =
                                            let uu____9065 =
                                              FStar_ST.op_Bang
                                                my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____9065
                                             in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____9064
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
              let uu___126_9169 = env3  in
              let uu____9170 = FStar_ST.op_Bang globals  in
              {
                curmodule = (uu___126_9169.curmodule);
                curmonad = (uu___126_9169.curmonad);
                modules = (uu___126_9169.modules);
                scope_mods = uu____9170;
                exported_ids = (uu___126_9169.exported_ids);
                trans_exported_ids = (uu___126_9169.trans_exported_ids);
                includes = (uu___126_9169.includes);
                sigaccum = (uu___126_9169.sigaccum);
                sigmap = (uu___126_9169.sigmap);
                iface = (uu___126_9169.iface);
                admitted_iface = (uu___126_9169.admitted_iface);
                expect_typ = (uu___126_9169.expect_typ);
                docs = (uu___126_9169.docs);
                remaining_iface_decls = (uu___126_9169.remaining_iface_decls);
                syntax_only = (uu___126_9169.syntax_only);
                ds_hooks = (uu___126_9169.ds_hooks)
              }  in
            env4))
  
let push_namespace : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____9232 =
        let uu____9237 = resolve_module_name env ns false  in
        match uu____9237 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9251 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9267  ->
                      match uu____9267 with
                      | (m,uu____9273) ->
                          let uu____9274 =
                            let uu____9275 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____9275 "."  in
                          let uu____9276 =
                            let uu____9277 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____9277 "."  in
                          FStar_Util.starts_with uu____9274 uu____9276))
               in
            if uu____9251
            then (ns, Open_namespace)
            else
              (let uu____9283 =
                 let uu____9288 =
                   let uu____9289 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9289
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9288)  in
               let uu____9290 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9283 uu____9290)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____9232 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let push_include : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9311 = resolve_module_name env ns false  in
      match uu____9311 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9319 = current_module env1  in
              uu____9319.FStar_Ident.str  in
            (let uu____9321 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9321 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9345 =
                   let uu____9348 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9348
                    in
                 FStar_ST.op_Colon_Equals incl uu____9345);
            (match () with
             | () ->
                 let uu____9449 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____9449 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9469 =
                          let uu____9488 = get_exported_id_set env1 curmod
                             in
                          let uu____9496 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____9488, uu____9496)  in
                        match uu____9469 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____9561 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____9561  in
                              let ex = cur_exports k  in
                              (let uu____9695 =
                                 let uu____9696 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____9696 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____9695);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____9804 =
                                     let uu____9805 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____9805 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____9804)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____9898 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____9922 =
                        let uu____9927 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____9927)
                         in
                      let uu____9928 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____9922 uu____9928))))
      | uu____9929 ->
          let uu____9932 =
            let uu____9937 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____9937)  in
          let uu____9938 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____9932 uu____9938
  
let push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____9954 = module_is_defined env l  in
        if uu____9954
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____9958 =
             let uu____9963 =
               let uu____9964 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____9964  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____9963)  in
           let uu____9965 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____9958 uu____9965)
  
let push_doc :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | FStar_Pervasives_Native.None  -> env
        | FStar_Pervasives_Native.Some doc1 ->
            ((let uu____9987 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____9987 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____9991 = FStar_Ident.range_of_lid l  in
                  let uu____9992 =
                    let uu____9997 =
                      let uu____9998 = FStar_Ident.string_of_lid l  in
                      let uu____9999 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____10000 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____9998 uu____9999 uu____10000
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____9997)  in
                  FStar_Errors.log_issue uu____9991 uu____9992);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
  
let check_admits :
  env -> FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul =
  fun env  ->
    fun m  ->
      let admitted_sig_lids =
        FStar_All.pipe_right env.sigaccum
          (FStar_List.fold_left
             (fun lids  ->
                fun se  ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) when
                      let uu____10040 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____10040 ->
                      let uu____10043 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____10043 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____10056;
                              FStar_Syntax_Syntax.sigrng = uu____10057;
                              FStar_Syntax_Syntax.sigquals = uu____10058;
                              FStar_Syntax_Syntax.sigmeta = uu____10059;
                              FStar_Syntax_Syntax.sigattrs = uu____10060;_},uu____10061)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____10076;
                              FStar_Syntax_Syntax.sigrng = uu____10077;
                              FStar_Syntax_Syntax.sigquals = uu____10078;
                              FStar_Syntax_Syntax.sigmeta = uu____10079;
                              FStar_Syntax_Syntax.sigattrs = uu____10080;_},uu____10081)
                           -> lids
                       | uu____10106 ->
                           ((let uu____10114 =
                               let uu____10115 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____10115  in
                             if uu____10114
                             then
                               let uu____10116 = FStar_Ident.range_of_lid l
                                  in
                               let uu____10117 =
                                 let uu____10122 =
                                   let uu____10123 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____10123
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____10122)
                                  in
                               FStar_Errors.log_issue uu____10116 uu____10117
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___127_10134 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___127_10134.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___127_10134.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___127_10134.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___127_10134.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____10135 -> lids) [])
         in
      let uu___128_10136 = m  in
      let uu____10137 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____10147,uu____10148) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___129_10151 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___129_10151.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___129_10151.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___129_10151.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___129_10151.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____10152 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___128_10136.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____10137;
        FStar_Syntax_Syntax.exports =
          (uu___128_10136.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___128_10136.FStar_Syntax_Syntax.is_interface)
      }
  
let finish : env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10173) ->
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
                                (lid,uu____10193,uu____10194,uu____10195,uu____10196,uu____10197)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____10210,uu____10211)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____10226 =
                                        let uu____10233 =
                                          let uu____10236 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____10237 =
                                            let uu____10244 =
                                              let uu____10245 =
                                                let uu____10258 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____10258)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____10245
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____10244
                                             in
                                          uu____10237
                                            FStar_Pervasives_Native.None
                                            uu____10236
                                           in
                                        (lid, univ_names, uu____10233)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____10226
                                       in
                                    let se2 =
                                      let uu___130_10265 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___130_10265.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___130_10265.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___130_10265.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____10271 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____10274,uu____10275) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____10281,lbs),uu____10283)
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
                             let uu____10304 =
                               let uu____10305 =
                                 let uu____10306 =
                                   let uu____10309 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____10309.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____10306.FStar_Syntax_Syntax.v  in
                               uu____10305.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____10304))
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
                               let uu____10323 =
                                 let uu____10326 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____10326.FStar_Syntax_Syntax.fv_name  in
                               uu____10323.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___131_10331 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___131_10331.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___131_10331.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___131_10331.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____10341 -> ()));
      (let curmod =
         let uu____10343 = current_module env  in uu____10343.FStar_Ident.str
          in
       (let uu____10345 =
          let uu____10364 = get_exported_id_set env curmod  in
          let uu____10372 = get_trans_exported_id_set env curmod  in
          (uu____10364, uu____10372)  in
        match uu____10345 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____10437 = cur_ex eikind  in
                FStar_ST.op_Bang uu____10437  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____10570 =
                let uu____10571 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____10571  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____10570  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____10664 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___132_10684 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___132_10684.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___132_10684.exported_ids);
                    trans_exported_ids = (uu___132_10684.trans_exported_ids);
                    includes = (uu___132_10684.includes);
                    sigaccum = [];
                    sigmap = (uu___132_10684.sigmap);
                    iface = (uu___132_10684.iface);
                    admitted_iface = (uu___132_10684.admitted_iface);
                    expect_typ = (uu___132_10684.expect_typ);
                    docs = (uu___132_10684.docs);
                    remaining_iface_decls =
                      (uu___132_10684.remaining_iface_decls);
                    syntax_only = (uu___132_10684.syntax_only);
                    ds_hooks = (uu___132_10684.ds_hooks)
                  }))))
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push : env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____10713 =
       let uu____10716 = FStar_ST.op_Bang stack  in env :: uu____10716  in
     FStar_ST.op_Colon_Equals stack uu____10713);
    (let uu___133_10773 = env  in
     let uu____10774 = FStar_Util.smap_copy (sigmap env)  in
     let uu____10785 = FStar_Util.smap_copy env.docs  in
     {
       curmodule = (uu___133_10773.curmodule);
       curmonad = (uu___133_10773.curmonad);
       modules = (uu___133_10773.modules);
       scope_mods = (uu___133_10773.scope_mods);
       exported_ids = (uu___133_10773.exported_ids);
       trans_exported_ids = (uu___133_10773.trans_exported_ids);
       includes = (uu___133_10773.includes);
       sigaccum = (uu___133_10773.sigaccum);
       sigmap = uu____10774;
       iface = (uu___133_10773.iface);
       admitted_iface = (uu___133_10773.admitted_iface);
       expect_typ = (uu___133_10773.expect_typ);
       docs = uu____10785;
       remaining_iface_decls = (uu___133_10773.remaining_iface_decls);
       syntax_only = (uu___133_10773.syntax_only);
       ds_hooks = (uu___133_10773.ds_hooks)
     })
  
let pop : unit -> env =
  fun uu____10792  ->
    let uu____10793 = FStar_ST.op_Bang stack  in
    match uu____10793 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10856 -> failwith "Impossible: Too many pops"
  
let export_interface : FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____10876 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____10879 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____10913 = FStar_Util.smap_try_find sm' k  in
              match uu____10913 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___134_10938 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___134_10938.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___134_10938.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___134_10938.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___134_10938.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____10939 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____10944 -> ()));
      env1
  
let finish_module_or_interface :
  env ->
    FStar_Syntax_Syntax.modul ->
      (env,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____10967 = finish env modul1  in (uu____10967, modul1)
  
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list ;
  exported_id_fields: Prims.string Prims.list }[@@deriving show]
let __proj__Mkexported_ids__item__exported_id_terms :
  exported_ids -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_terms
  
let __proj__Mkexported_ids__item__exported_id_fields :
  exported_ids -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_fields
  
let as_exported_ids : exported_id_set -> exported_ids =
  fun e  ->
    let terms =
      let uu____11055 =
        let uu____11058 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____11058  in
      FStar_Util.set_elements uu____11055  in
    let fields =
      let uu____11180 =
        let uu____11183 = e Exported_id_field  in
        FStar_ST.op_Bang uu____11183  in
      FStar_Util.set_elements uu____11180  in
    { exported_id_terms = terms; exported_id_fields = fields }
  
let as_exported_id_set :
  exported_ids FStar_Pervasives_Native.option ->
    exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun e  ->
    match e with
    | FStar_Pervasives_Native.None  -> exported_id_set_new ()
    | FStar_Pervasives_Native.Some e1 ->
        let terms =
          let uu____11342 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____11342  in
        let fields =
          let uu____11352 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____11352  in
        (fun uu___109_11357  ->
           match uu___109_11357 with
           | Exported_id_term_type  -> terms
           | Exported_id_field  -> fields)
  
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option }
[@@deriving show]
let __proj__Mkmodule_inclusion_info__item__mii_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_exported_ids
  
let __proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} ->
        __fname__mii_trans_exported_ids
  
let __proj__Mkmodule_inclusion_info__item__mii_includes :
  module_inclusion_info ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_includes
  
let default_mii : module_inclusion_info =
  {
    mii_exported_ids = FStar_Pervasives_Native.None;
    mii_trans_exported_ids = FStar_Pervasives_Native.None;
    mii_includes = FStar_Pervasives_Native.None
  } 
let as_includes :
  'Auu____11488 .
    'Auu____11488 Prims.list FStar_Pervasives_Native.option ->
      'Auu____11488 Prims.list FStar_ST.ref
  =
  fun uu___110_11501  ->
    match uu___110_11501 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____11542 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____11542 as_exported_ids  in
      let uu____11548 = as_ids_opt env.exported_ids  in
      let uu____11551 = as_ids_opt env.trans_exported_ids  in
      let uu____11554 =
        let uu____11559 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____11559 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____11548;
        mii_trans_exported_ids = uu____11551;
        mii_includes = uu____11554
      }
  
let prepare_module_or_interface :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          module_inclusion_info ->
            (env,Prims.bool) FStar_Pervasives_Native.tuple2
  =
  fun intf  ->
    fun admitted  ->
      fun env  ->
        fun mname  ->
          fun mii  ->
            let prep env1 =
              let filename =
                let uu____11678 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____11678 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___111_11698 =
                  match uu___111_11698 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____11710  ->
                     match uu____11710 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.lift_native_int (0))
                then
                  let uu____11734 =
                    let uu____11739 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____11739, Open_namespace)  in
                  [uu____11734]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____11769 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____11769);
              (match () with
               | () ->
                   ((let uu____11796 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____11796);
                    (match () with
                     | () ->
                         ((let uu____11823 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____11823);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___135_11855 = env1  in
                                 let uu____11856 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___135_11855.curmonad);
                                   modules = (uu___135_11855.modules);
                                   scope_mods = uu____11856;
                                   exported_ids =
                                     (uu___135_11855.exported_ids);
                                   trans_exported_ids =
                                     (uu___135_11855.trans_exported_ids);
                                   includes = (uu___135_11855.includes);
                                   sigaccum = (uu___135_11855.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___135_11855.expect_typ);
                                   docs = (uu___135_11855.docs);
                                   remaining_iface_decls =
                                     (uu___135_11855.remaining_iface_decls);
                                   syntax_only = (uu___135_11855.syntax_only);
                                   ds_hooks = (uu___135_11855.ds_hooks)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____11868 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____11894  ->
                      match uu____11894 with
                      | (l,uu____11900) -> FStar_Ident.lid_equals l mname))
               in
            match uu____11868 with
            | FStar_Pervasives_Native.None  ->
                let uu____11909 = prep env  in (uu____11909, false)
            | FStar_Pervasives_Native.Some (uu____11910,m) ->
                ((let uu____11917 =
                    (let uu____11920 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____11920) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____11917
                  then
                    let uu____11921 =
                      let uu____11926 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____11926)
                       in
                    let uu____11927 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____11921 uu____11927
                  else ());
                 (let uu____11929 =
                    let uu____11930 = push env  in prep uu____11930  in
                  (uu____11929, true)))
  
let enter_monad_scope : env -> FStar_Ident.ident -> env =
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
          let uu___136_11942 = env  in
          {
            curmodule = (uu___136_11942.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___136_11942.modules);
            scope_mods = (uu___136_11942.scope_mods);
            exported_ids = (uu___136_11942.exported_ids);
            trans_exported_ids = (uu___136_11942.trans_exported_ids);
            includes = (uu___136_11942.includes);
            sigaccum = (uu___136_11942.sigaccum);
            sigmap = (uu___136_11942.sigmap);
            iface = (uu___136_11942.iface);
            admitted_iface = (uu___136_11942.admitted_iface);
            expect_typ = (uu___136_11942.expect_typ);
            docs = (uu___136_11942.docs);
            remaining_iface_decls = (uu___136_11942.remaining_iface_decls);
            syntax_only = (uu___136_11942.syntax_only);
            ds_hooks = (uu___136_11942.ds_hooks)
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
        let uu____11976 = lookup1 lid  in
        match uu____11976 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____11989  ->
                   match uu____11989 with
                   | (lid1,uu____11995) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____11997 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____11997  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.lift_native_int (0))
              then msg
              else
                (let modul =
                   let uu____12001 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____12002 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____12001 uu____12002  in
                 let uu____12003 = resolve_module_name env modul true  in
                 match uu____12003 with
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
            let uu____12012 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____12012
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____12040 = lookup1 id1  in
      match uu____12040 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  
let mk_copy : env -> env =
  fun en  ->
    let uu___137_12049 = en  in
    let uu____12050 = FStar_Util.smap_copy en.exported_ids  in
    let uu____12055 = FStar_Util.smap_copy en.trans_exported_ids  in
    let uu____12060 = FStar_Util.smap_copy en.sigmap  in
    let uu____12071 = FStar_Util.smap_copy en.docs  in
    {
      curmodule = (uu___137_12049.curmodule);
      curmonad = (uu___137_12049.curmonad);
      modules = (uu___137_12049.modules);
      scope_mods = (uu___137_12049.scope_mods);
      exported_ids = uu____12050;
      trans_exported_ids = uu____12055;
      includes = (uu___137_12049.includes);
      sigaccum = (uu___137_12049.sigaccum);
      sigmap = uu____12060;
      iface = (uu___137_12049.iface);
      admitted_iface = (uu___137_12049.admitted_iface);
      expect_typ = (uu___137_12049.expect_typ);
      docs = uu____12071;
      remaining_iface_decls = (uu___137_12049.remaining_iface_decls);
      syntax_only = (uu___137_12049.syntax_only);
      ds_hooks = (uu___137_12049.ds_hooks)
    }
  