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
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____21 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____26 -> false
type open_module_or_namespace =
  (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2
type record_or_dc =
  {
  typename: FStar_Ident.lident;
  constrname: FStar_Ident.ident;
  parms: FStar_Syntax_Syntax.binders;
  fields:
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list;
  is_private_or_abstract: Prims.bool;
  is_record: Prims.bool;}
let __proj__Mkrecord_or_dc__item__typename:
  record_or_dc -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__typename
let __proj__Mkrecord_or_dc__item__constrname:
  record_or_dc -> FStar_Ident.ident =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__constrname
let __proj__Mkrecord_or_dc__item__parms:
  record_or_dc -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__parms
let __proj__Mkrecord_or_dc__item__fields:
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
let __proj__Mkrecord_or_dc__item__is_private_or_abstract:
  record_or_dc -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { typename = __fname__typename; constrname = __fname__constrname;
        parms = __fname__parms; fields = __fname__fields;
        is_private_or_abstract = __fname__is_private_or_abstract;
        is_record = __fname__is_record;_} -> __fname__is_private_or_abstract
let __proj__Mkrecord_or_dc__item__is_record: record_or_dc -> Prims.bool =
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
let uu___is_Local_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Local_binding _0 -> true | uu____198 -> false
let __proj__Local_binding__item___0: scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0
let uu___is_Rec_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____212 -> false
let __proj__Rec_binding__item___0: scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____226 -> false
let __proj__Module_abbrev__item___0: scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____240 -> false
let __proj__Open_module_or_namespace__item___0:
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_def: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____254 -> false
let __proj__Top_level_def__item___0: scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0
let uu___is_Record_or_dc: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____268 -> false
let __proj__Record_or_dc__item___0: scope_mod -> record_or_dc =
  fun projectee  -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStar_Util.set
type exported_id_kind =
  | Exported_id_term_type
  | Exported_id_field
let uu___is_Exported_id_term_type: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____283 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____288 -> false
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref
type env =
  {
  curmodule: FStar_Ident.lident FStar_Pervasives_Native.option;
  curmonad: FStar_Ident.ident FStar_Pervasives_Native.option;
  modules:
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list;
  scope_mods: scope_mod Prims.list;
  exported_ids: exported_id_set FStar_Util.smap;
  trans_exported_ids: exported_id_set FStar_Util.smap;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap;
  sigaccum: FStar_Syntax_Syntax.sigelts;
  sigmap:
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap;
  iface: Prims.bool;
  admitted_iface: Prims.bool;
  expect_typ: Prims.bool;
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap;
  remaining_iface_decls:
    (FStar_Ident.lident,FStar_Parser_AST.decl Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list;
  syntax_only: Prims.bool;}
let __proj__Mkenv__item__curmodule:
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
        syntax_only = __fname__syntax_only;_} -> __fname__curmodule
let __proj__Mkenv__item__curmonad:
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
        syntax_only = __fname__syntax_only;_} -> __fname__curmonad
let __proj__Mkenv__item__modules:
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
        syntax_only = __fname__syntax_only;_} -> __fname__modules
let __proj__Mkenv__item__scope_mods: env -> scope_mod Prims.list =
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
        syntax_only = __fname__syntax_only;_} -> __fname__scope_mods
let __proj__Mkenv__item__exported_ids: env -> exported_id_set FStar_Util.smap
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
        syntax_only = __fname__syntax_only;_} -> __fname__exported_ids
let __proj__Mkenv__item__trans_exported_ids:
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
        syntax_only = __fname__syntax_only;_} -> __fname__trans_exported_ids
let __proj__Mkenv__item__includes:
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
        syntax_only = __fname__syntax_only;_} -> __fname__includes
let __proj__Mkenv__item__sigaccum: env -> FStar_Syntax_Syntax.sigelts =
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
        syntax_only = __fname__syntax_only;_} -> __fname__sigaccum
let __proj__Mkenv__item__sigmap:
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
        syntax_only = __fname__syntax_only;_} -> __fname__sigmap
let __proj__Mkenv__item__iface: env -> Prims.bool =
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
        syntax_only = __fname__syntax_only;_} -> __fname__iface
let __proj__Mkenv__item__admitted_iface: env -> Prims.bool =
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
        syntax_only = __fname__syntax_only;_} -> __fname__admitted_iface
let __proj__Mkenv__item__expect_typ: env -> Prims.bool =
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
        syntax_only = __fname__syntax_only;_} -> __fname__expect_typ
let __proj__Mkenv__item__docs: env -> FStar_Parser_AST.fsdoc FStar_Util.smap
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
        syntax_only = __fname__syntax_only;_} -> __fname__docs
let __proj__Mkenv__item__remaining_iface_decls:
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
        syntax_only = __fname__syntax_only;_} ->
        __fname__remaining_iface_decls
let __proj__Mkenv__item__syntax_only: env -> Prims.bool =
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
        syntax_only = __fname__syntax_only;_} -> __fname__syntax_only
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ,Prims.bool)
  FStar_Pervasives_Native.tuple2
  | Eff_name of (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
  FStar_Pervasives_Native.tuple2
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____1349 -> false
let __proj__Term_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1379 -> false
let __proj__Eff_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___176_1408 = env in
      {
        curmodule = (uu___176_1408.curmodule);
        curmonad = (uu___176_1408.curmonad);
        modules = (uu___176_1408.modules);
        scope_mods = (uu___176_1408.scope_mods);
        exported_ids = (uu___176_1408.exported_ids);
        trans_exported_ids = (uu___176_1408.trans_exported_ids);
        includes = (uu___176_1408.includes);
        sigaccum = (uu___176_1408.sigaccum);
        sigmap = (uu___176_1408.sigmap);
        iface = b;
        admitted_iface = (uu___176_1408.admitted_iface);
        expect_typ = (uu___176_1408.expect_typ);
        docs = (uu___176_1408.docs);
        remaining_iface_decls = (uu___176_1408.remaining_iface_decls);
        syntax_only = (uu___176_1408.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___177_1421 = e in
      {
        curmodule = (uu___177_1421.curmodule);
        curmonad = (uu___177_1421.curmonad);
        modules = (uu___177_1421.modules);
        scope_mods = (uu___177_1421.scope_mods);
        exported_ids = (uu___177_1421.exported_ids);
        trans_exported_ids = (uu___177_1421.trans_exported_ids);
        includes = (uu___177_1421.includes);
        sigaccum = (uu___177_1421.sigaccum);
        sigmap = (uu___177_1421.sigmap);
        iface = (uu___177_1421.iface);
        admitted_iface = b;
        expect_typ = (uu___177_1421.expect_typ);
        docs = (uu___177_1421.docs);
        remaining_iface_decls = (uu___177_1421.remaining_iface_decls);
        syntax_only = (uu___177_1421.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___178_1434 = e in
      {
        curmodule = (uu___178_1434.curmodule);
        curmonad = (uu___178_1434.curmonad);
        modules = (uu___178_1434.modules);
        scope_mods = (uu___178_1434.scope_mods);
        exported_ids = (uu___178_1434.exported_ids);
        trans_exported_ids = (uu___178_1434.trans_exported_ids);
        includes = (uu___178_1434.includes);
        sigaccum = (uu___178_1434.sigaccum);
        sigmap = (uu___178_1434.sigmap);
        iface = (uu___178_1434.iface);
        admitted_iface = (uu___178_1434.admitted_iface);
        expect_typ = b;
        docs = (uu___178_1434.docs);
        remaining_iface_decls = (uu___178_1434.remaining_iface_decls);
        syntax_only = (uu___178_1434.syntax_only)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1452 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1452 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1458 =
            let uu____1459 = exported_id_set Exported_id_term_type in
            FStar_ST.read uu____1459 in
          FStar_All.pipe_right uu____1458 FStar_Util.set_elements
let open_modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  = fun e  -> e.modules
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___179_1485 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___179_1485.curmonad);
        modules = (uu___179_1485.modules);
        scope_mods = (uu___179_1485.scope_mods);
        exported_ids = (uu___179_1485.exported_ids);
        trans_exported_ids = (uu___179_1485.trans_exported_ids);
        includes = (uu___179_1485.includes);
        sigaccum = (uu___179_1485.sigaccum);
        sigmap = (uu___179_1485.sigmap);
        iface = (uu___179_1485.iface);
        admitted_iface = (uu___179_1485.admitted_iface);
        expect_typ = (uu___179_1485.expect_typ);
        docs = (uu___179_1485.docs);
        remaining_iface_decls = (uu___179_1485.remaining_iface_decls);
        syntax_only = (uu___179_1485.syntax_only)
      }
let current_module: env -> FStar_Ident.lident =
  fun env  ->
    match env.curmodule with
    | FStar_Pervasives_Native.None  -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
let iface_decls:
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____1503 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____1537  ->
                match uu____1537 with
                | (m,uu____1545) -> FStar_Ident.lid_equals l m)) in
      match uu____1503 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____1562,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____1592 =
          FStar_List.partition
            (fun uu____1622  ->
               match uu____1622 with
               | (m,uu____1630) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____1592 with
        | (uu____1635,rest) ->
            let uu___180_1669 = env in
            {
              curmodule = (uu___180_1669.curmodule);
              curmonad = (uu___180_1669.curmonad);
              modules = (uu___180_1669.modules);
              scope_mods = (uu___180_1669.scope_mods);
              exported_ids = (uu___180_1669.exported_ids);
              trans_exported_ids = (uu___180_1669.trans_exported_ids);
              includes = (uu___180_1669.includes);
              sigaccum = (uu___180_1669.sigaccum);
              sigmap = (uu___180_1669.sigmap);
              iface = (uu___180_1669.iface);
              admitted_iface = (uu___180_1669.admitted_iface);
              expect_typ = (uu___180_1669.expect_typ);
              docs = (uu___180_1669.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___180_1669.syntax_only)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____1692 = current_module env in qual uu____1692 id
      | FStar_Pervasives_Native.Some monad ->
          let uu____1694 =
            let uu____1695 = current_module env in qual uu____1695 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____1694 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___181_1708 = env in
      {
        curmodule = (uu___181_1708.curmodule);
        curmonad = (uu___181_1708.curmonad);
        modules = (uu___181_1708.modules);
        scope_mods = (uu___181_1708.scope_mods);
        exported_ids = (uu___181_1708.exported_ids);
        trans_exported_ids = (uu___181_1708.trans_exported_ids);
        includes = (uu___181_1708.includes);
        sigaccum = (uu___181_1708.sigaccum);
        sigmap = (uu___181_1708.sigmap);
        iface = (uu___181_1708.iface);
        admitted_iface = (uu___181_1708.admitted_iface);
        expect_typ = (uu___181_1708.expect_typ);
        docs = (uu___181_1708.docs);
        remaining_iface_decls = (uu___181_1708.remaining_iface_decls);
        syntax_only = b
      }
let new_sigmap uu____1719 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____1723  ->
    let uu____1724 = new_sigmap () in
    let uu____1727 = new_sigmap () in
    let uu____1730 = new_sigmap () in
    let uu____1741 = new_sigmap () in
    let uu____1752 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____1724;
      trans_exported_ids = uu____1727;
      includes = uu____1730;
      sigaccum = [];
      sigmap = uu____1741;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____1752;
      remaining_iface_decls = [];
      syntax_only = false
    }
let sigmap:
  env ->
    (FStar_Syntax_Syntax.sigelt,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Util.smap
  = fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____1786  ->
         match uu____1786 with
         | (m,uu____1792) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___182_1802 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___182_1802.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___183_1803 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___183_1803.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___183_1803.FStar_Syntax_Syntax.sort)
      }
let bv_to_name:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)
let unmangleMap:
  (Prims.string,Prims.string,FStar_Syntax_Syntax.delta_depth,FStar_Syntax_Syntax.fv_qual
                                                               FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple4 Prims.list
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational,
    FStar_Pervasives_Native.None)]
let unmangleOpName:
  FStar_Ident.ident ->
    (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun id  ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____1893  ->
           match uu____1893 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____1916 =
                   let uu____1917 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____1917 dd dq in
                 FStar_Pervasives_Native.Some uu____1916
               else FStar_Pervasives_Native.None) in
    match t with
    | FStar_Pervasives_Native.Some v1 ->
        FStar_Pervasives_Native.Some (v1, false)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____1962 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____1995 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____2011 -> false
let option_of_cont k_ignore uu___148_2037 =
  match uu___148_2037 with
  | Cont_ok a -> FStar_Pervasives_Native.Some a
  | Cont_fail  -> FStar_Pervasives_Native.None
  | Cont_ignore  -> k_ignore ()
let find_in_record ns id record cont =
  let typename' =
    FStar_Ident.lid_of_ids
      (FStar_List.append ns [(record.typename).FStar_Ident.ident]) in
  if FStar_Ident.lid_equals typename' record.typename
  then
    let fname =
      FStar_Ident.lid_of_ids
        (FStar_List.append (record.typename).FStar_Ident.ns [id]) in
    let find1 =
      FStar_Util.find_map record.fields
        (fun uu____2101  ->
           match uu____2101 with
           | (f,uu____2109) ->
               if id.FStar_Ident.idText = f.FStar_Ident.idText
               then FStar_Pervasives_Native.Some record
               else FStar_Pervasives_Native.None) in
    match find1 with
    | FStar_Pervasives_Native.Some r -> cont r
    | FStar_Pervasives_Native.None  -> Cont_ignore
  else Cont_ignore
let get_exported_id_set:
  env -> Prims.string -> exported_id_set FStar_Pervasives_Native.option =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname
let get_trans_exported_id_set:
  env -> Prims.string -> exported_id_set FStar_Pervasives_Native.option =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname
let string_of_exported_id_kind: exported_id_kind -> Prims.string =
  fun uu___149_2160  ->
    match uu___149_2160 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___150_2223 =
    match uu___150_2223 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
          let uu____2234 = get_exported_id_set env mname in
          match uu____2234 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some mex ->
              let mexports =
                let uu____2255 = mex eikind in FStar_ST.read uu____2255 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____2264 = FStar_Util.smap_try_find env.includes mname in
          match uu____2264 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
          then let uu____2299 = qual modul id in find_in_module uu____2299
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____2303 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___151_2309  ->
    match uu___151_2309 with
    | Exported_id_field  -> true
    | uu____2310 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___152_2421 =
    match uu___152_2421 with
    | (id',uu____2423,uu____2424) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___153_2428 =
    match uu___153_2428 with
    | (id',uu____2430,uu____2431) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____2435 = current_module env in FStar_Ident.ids_of_lid uu____2435 in
  let proc uu___154_2441 =
    match uu___154_2441 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,Open_module ) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____2449 = FStar_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____2449 id
    | uu____2454 -> Cont_ignore in
  let rec aux uu___155_2462 =
    match uu___155_2462 with
    | a::q ->
        let uu____2471 = proc a in
        option_of_cont (fun uu____2475  -> aux q) uu____2471
    | [] ->
        let uu____2476 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____2480  -> FStar_Pervasives_Native.None)
          uu____2476 in
  aux env.scope_mods
let found_local_binding r uu____2508 =
  match uu____2508 with
  | (id',x,mut) -> let uu____2518 = bv_to_name x r in (uu____2518, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____2564 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____2564 with
  | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
  | FStar_Pervasives_Native.None  -> k_not_found
let try_lookup_id:
  env ->
    FStar_Ident.ident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun id  ->
      let uu____2602 = unmangleOpName id in
      match uu____2602 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____2628 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____2642 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____2642) (fun uu____2652  -> Cont_fail)
            (fun uu____2658  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____2673  -> fun uu____2674  -> Cont_fail)
                 Cont_ignore)
            (fun uu____2689  -> fun uu____2690  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | FStar_Pervasives_Native.Some uu____2765 ->
        let lid = qualify env id in
        let uu____2767 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____2767 with
         | FStar_Pervasives_Native.Some r ->
             let uu____2791 = k_global_def lid r in
             FStar_Pervasives_Native.Some uu____2791
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
  match find_in_monad with
  | FStar_Pervasives_Native.Some v1 -> v1
  | FStar_Pervasives_Native.None  ->
      let lid = let uu____2814 = current_module env in qual uu____2814 id in
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____2826 = current_module env in
           FStar_Ident.lid_equals lid uu____2826)
        ||
        (FStar_List.existsb
           (fun x  ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env.modules)
let resolve_module_name:
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
        let rec aux uu___156_2861 =
          match uu___156_2861 with
          | [] ->
              let uu____2866 = module_is_defined env lid in
              if uu____2866
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____2875 =
                  let uu____2878 = FStar_Ident.path_of_lid ns in
                  let uu____2881 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____2878 uu____2881 in
                FStar_Ident.lid_of_path uu____2875
                  (FStar_Ident.range_of_lid lid) in
              let uu____2884 = module_is_defined env new_lid in
              if uu____2884
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____2890 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____2897::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____2913 =
          let uu____2914 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____2914 in
        if uu____2913
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____2916 =
                let uu____2917 =
                  let uu____2922 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____2922, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____2917 in
              raise uu____2916))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____2932 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____2936 = resolve_module_name env modul_orig true in
          (match uu____2936 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____2940 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___157_2953  ->
           match uu___157_2953 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____2955 -> false) env.scope_mods
let shorten_module_path:
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list,FStar_Ident.ident Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ids  ->
      fun is_full_path  ->
        let rec aux revns id =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id in
          if namespace_is_open env lid
          then
            FStar_Pervasives_Native.Some ((FStar_List.rev (id :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu____3047 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3047
                   (FStar_Util.map_option
                      (fun uu____3097  ->
                         match uu____3097 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____3128 =
          is_full_path &&
            (let uu____3130 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____3130) in
        if uu____3128
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3160 = aux ns_rev_prefix ns_last_id in
               (match uu____3160 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____3221 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____3221 with
      | (uu____3230,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____3347::uu____3348 ->
      let uu____3351 =
        let uu____3354 =
          let uu____3355 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____3355 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____3354 true in
      (match uu____3351 with
       | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some modul ->
           let uu____3359 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____3363  -> FStar_Pervasives_Native.None)
             uu____3359)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___158_3384 =
  match uu___158_3384 with
  | FStar_Pervasives_Native.Some v1 -> Cont_ok v1
  | FStar_Pervasives_Native.None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____3489 = k_global_def lid1 def in cont_of_option k uu____3489 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____3519 = k_local_binding l in
       cont_of_option Cont_fail uu____3519)
    (fun r  ->
       let uu____3525 = k_rec_binding r in
       cont_of_option Cont_fail uu____3525) (fun uu____3529  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3538,uu____3539,uu____3540,l,uu____3542,uu____3543) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___159_3554  ->
               match uu___159_3554 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____3557,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____3569 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____3575,uu____3576,uu____3577)
        -> FStar_Pervasives_Native.None
    | uu____3578 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____3591 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____3599 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____3599
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____3591 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____3614 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____3614 ns)
let try_lookup_name:
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___163_3648 =
            match uu___163_3648 with
            | (uu____3655,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____3657) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____3660 ->
                     let uu____3677 =
                       let uu____3678 =
                         let uu____3683 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____3683, false) in
                       Term_name uu____3678 in
                     FStar_Pervasives_Native.Some uu____3677
                 | FStar_Syntax_Syntax.Sig_datacon uu____3684 ->
                     let uu____3699 =
                       let uu____3700 =
                         let uu____3705 =
                           let uu____3706 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____3706 in
                         (uu____3705, false) in
                       Term_name uu____3700 in
                     FStar_Pervasives_Native.Some uu____3699
                 | FStar_Syntax_Syntax.Sig_let ((uu____3709,lbs),uu____3711)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____3727 =
                       let uu____3728 =
                         let uu____3733 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____3733, false) in
                       Term_name uu____3728 in
                     FStar_Pervasives_Native.Some uu____3727
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____3735,uu____3736) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____3740 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___160_3744  ->
                                  match uu___160_3744 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____3745 -> false))) in
                     if uu____3740
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____3750 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___161_3755  ->
                                      match uu___161_3755 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____3756 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____3761 -> true
                                      | uu____3762 -> false))) in
                         if uu____3750
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____3764 =
                         FStar_Util.find_map quals
                           (fun uu___162_3769  ->
                              match uu___162_3769 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____3773 -> FStar_Pervasives_Native.None) in
                       (match uu____3764 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____3786 ->
                            let uu____3789 =
                              let uu____3790 =
                                let uu____3795 =
                                  let uu____3796 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____3796 in
                                (uu____3795, false) in
                              Term_name uu____3790 in
                            FStar_Pervasives_Native.Some uu____3789)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3802 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____3815 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____3834 =
              let uu____3835 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____3835 in
            FStar_Pervasives_Native.Some uu____3834 in
          let k_rec_binding uu____3851 =
            match uu____3851 with
            | (id,l,dd) ->
                let uu____3863 =
                  let uu____3864 =
                    let uu____3869 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____3869, false) in
                  Term_name uu____3864 in
                FStar_Pervasives_Native.Some uu____3863 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____3875 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____3875 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____3893 -> FStar_Pervasives_Native.None)
            | uu____3900 -> FStar_Pervasives_Native.None in
          match found_unmangled with
          | FStar_Pervasives_Native.None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
let try_lookup_effect_name':
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____3932 = try_lookup_name true exclude_interf env lid in
        match uu____3932 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____3947 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____3964 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____3964 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____3979 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4002 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4002 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4018;
             FStar_Syntax_Syntax.sigquals = uu____4019;
             FStar_Syntax_Syntax.sigmeta = uu____4020;
             FStar_Syntax_Syntax.sigattrs = uu____4021;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4040;
             FStar_Syntax_Syntax.sigquals = uu____4041;
             FStar_Syntax_Syntax.sigmeta = uu____4042;
             FStar_Syntax_Syntax.sigattrs = uu____4043;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4061,uu____4062,uu____4063,uu____4064,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4066;
             FStar_Syntax_Syntax.sigquals = uu____4067;
             FStar_Syntax_Syntax.sigmeta = uu____4068;
             FStar_Syntax_Syntax.sigattrs = uu____4069;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4091 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4114 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4114 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4124;
             FStar_Syntax_Syntax.sigquals = uu____4125;
             FStar_Syntax_Syntax.sigmeta = uu____4126;
             FStar_Syntax_Syntax.sigattrs = uu____4127;_},uu____4128)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4138;
             FStar_Syntax_Syntax.sigquals = uu____4139;
             FStar_Syntax_Syntax.sigmeta = uu____4140;
             FStar_Syntax_Syntax.sigattrs = uu____4141;_},uu____4142)
          -> FStar_Pervasives_Native.Some ne
      | uu____4151 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4166 = try_lookup_effect_name env lid in
      match uu____4166 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4169 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4180 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4180 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____4190,uu____4191,uu____4192,uu____4193);
             FStar_Syntax_Syntax.sigrng = uu____4194;
             FStar_Syntax_Syntax.sigquals = uu____4195;
             FStar_Syntax_Syntax.sigmeta = uu____4196;
             FStar_Syntax_Syntax.sigattrs = uu____4197;_},uu____4198)
          ->
          let rec aux new_name =
            let uu____4217 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____4217 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____4235) ->
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
                     (uu____4244,uu____4245,uu____4246,cmp,uu____4248) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____4254 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4255,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4261 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___164_4292 =
        match uu___164_4292 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4301,uu____4302,uu____4303);
             FStar_Syntax_Syntax.sigrng = uu____4304;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4306;
             FStar_Syntax_Syntax.sigattrs = uu____4307;_},uu____4308)
            -> FStar_Pervasives_Native.Some quals
        | uu____4315 -> FStar_Pervasives_Native.None in
      let uu____4322 =
        resolve_in_open_namespaces' env lid
          (fun uu____4330  -> FStar_Pervasives_Native.None)
          (fun uu____4334  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____4322 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____4344 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____4363 =
        FStar_List.tryFind
          (fun uu____4378  ->
             match uu____4378 with
             | (mlid,modul) ->
                 let uu____4385 = FStar_Ident.path_of_lid mlid in
                 uu____4385 = path) env.modules in
      match uu____4363 with
      | FStar_Pervasives_Native.Some (uu____4392,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___165_4424 =
        match uu___165_4424 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____4431,lbs),uu____4433);
             FStar_Syntax_Syntax.sigrng = uu____4434;
             FStar_Syntax_Syntax.sigquals = uu____4435;
             FStar_Syntax_Syntax.sigmeta = uu____4436;
             FStar_Syntax_Syntax.sigattrs = uu____4437;_},uu____4438)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____4458 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____4458
        | uu____4459 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____4465  -> FStar_Pervasives_Native.None)
        (fun uu____4467  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___166_4494 =
        match uu___166_4494 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____4506);
             FStar_Syntax_Syntax.sigrng = uu____4507;
             FStar_Syntax_Syntax.sigquals = uu____4508;
             FStar_Syntax_Syntax.sigmeta = uu____4509;
             FStar_Syntax_Syntax.sigattrs = uu____4510;_},uu____4511)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____4540 -> FStar_Pervasives_Native.None)
        | uu____4549 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____4563  -> FStar_Pervasives_Native.None)
        (fun uu____4569  -> FStar_Pervasives_Native.None) k_global_def
let empty_include_smap:
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = new_sigmap ()
let empty_exported_id_smap: exported_id_set FStar_Util.smap = new_sigmap ()
let try_lookup_lid':
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term,Prims.bool)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let uu____4614 = try_lookup_name any_val exclude_interf env lid in
          match uu____4614 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____4629 -> FStar_Pervasives_Native.None
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4660 = try_lookup_lid env l in
      match uu____4660 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____4674) ->
          let uu____4679 =
            let uu____4680 = FStar_Syntax_Subst.compress e in
            uu____4680.FStar_Syntax_Syntax.n in
          (match uu____4679 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____4688 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___184_4704 = env in
        {
          curmodule = (uu___184_4704.curmodule);
          curmonad = (uu___184_4704.curmonad);
          modules = (uu___184_4704.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___184_4704.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___184_4704.sigaccum);
          sigmap = (uu___184_4704.sigmap);
          iface = (uu___184_4704.iface);
          admitted_iface = (uu___184_4704.admitted_iface);
          expect_typ = (uu___184_4704.expect_typ);
          docs = (uu___184_4704.docs);
          remaining_iface_decls = (uu___184_4704.remaining_iface_decls);
          syntax_only = (uu___184_4704.syntax_only)
        } in
      try_lookup_lid env' l
let try_lookup_doc:
  env ->
    FStar_Ident.lid -> FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option
  = fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___168_4737 =
        match uu___168_4737 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4744,uu____4745,uu____4746);
             FStar_Syntax_Syntax.sigrng = uu____4747;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4749;
             FStar_Syntax_Syntax.sigattrs = uu____4750;_},uu____4751)
            ->
            let uu____4756 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___167_4760  ->
                      match uu___167_4760 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____4761 -> false)) in
            if uu____4756
            then
              let uu____4764 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____4764
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____4766;
             FStar_Syntax_Syntax.sigrng = uu____4767;
             FStar_Syntax_Syntax.sigquals = uu____4768;
             FStar_Syntax_Syntax.sigmeta = uu____4769;
             FStar_Syntax_Syntax.sigattrs = uu____4770;_},uu____4771)
            ->
            let uu____4790 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____4790
        | uu____4791 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____4797  -> FStar_Pervasives_Native.None)
        (fun uu____4799  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___169_4826 =
        match uu___169_4826 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____4835,uu____4836,uu____4837,uu____4838,datas,uu____4840);
             FStar_Syntax_Syntax.sigrng = uu____4841;
             FStar_Syntax_Syntax.sigquals = uu____4842;
             FStar_Syntax_Syntax.sigmeta = uu____4843;
             FStar_Syntax_Syntax.sigattrs = uu____4844;_},uu____4845)
            -> FStar_Pervasives_Native.Some datas
        | uu____4860 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____4870  -> FStar_Pervasives_Native.None)
        (fun uu____4874  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit,Prims.unit -> Prims.unit)
     FStar_Pervasives_Native.tuple5,Prims.unit -> Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____4923 =
    let uu____4924 =
      let uu____4929 =
        let uu____4932 = FStar_ST.read record_cache in
        FStar_List.hd uu____4932 in
      let uu____4945 = FStar_ST.read record_cache in uu____4929 :: uu____4945 in
    FStar_ST.write record_cache uu____4924 in
  let pop1 uu____4967 =
    let uu____4968 =
      let uu____4973 = FStar_ST.read record_cache in FStar_List.tl uu____4973 in
    FStar_ST.write record_cache uu____4968 in
  let peek1 uu____4997 =
    let uu____4998 = FStar_ST.read record_cache in FStar_List.hd uu____4998 in
  let insert r =
    let uu____5015 =
      let uu____5020 = let uu____5023 = peek1 () in r :: uu____5023 in
      let uu____5026 =
        let uu____5031 = FStar_ST.read record_cache in
        FStar_List.tl uu____5031 in
      uu____5020 :: uu____5026 in
    FStar_ST.write record_cache uu____5015 in
  let commit1 uu____5055 =
    let uu____5056 = FStar_ST.read record_cache in
    match uu____5056 with
    | hd1::uu____5068::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____5090 -> failwith "Impossible" in
  let filter1 uu____5098 =
    let rc = peek1 () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____5108 =
           let uu____5113 = FStar_ST.read record_cache in filtered ::
             uu____5113 in
         FStar_ST.write record_cache uu____5108) in
  let aux = (push1, pop1, peek1, insert, commit1) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit,
    Prims.unit -> Prims.unit) FStar_Pervasives_Native.tuple5
  =
  let uu____5213 = record_cache_aux_with_filter in
  match uu____5213 with | (aux,uu____5265) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____5317 = record_cache_aux_with_filter in
  match uu____5317 with | (uu____5348,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____5401 = record_cache_aux in
  match uu____5401 with
  | (push1,uu____5427,uu____5428,uu____5429,uu____5430) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____5458 = record_cache_aux in
  match uu____5458 with
  | (uu____5483,pop1,uu____5485,uu____5486,uu____5487) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____5517 = record_cache_aux in
  match uu____5517 with
  | (uu____5544,uu____5545,peek1,uu____5547,uu____5548) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____5576 = record_cache_aux in
  match uu____5576 with
  | (uu____5601,uu____5602,uu____5603,insert,uu____5605) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____5633 = record_cache_aux in
  match uu____5633 with
  | (uu____5658,uu____5659,uu____5660,uu____5661,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____5710) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___170_5726  ->
                   match uu___170_5726 with
                   | FStar_Syntax_Syntax.RecordType uu____5727 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____5736 -> true
                   | uu____5745 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___171_5767  ->
                      match uu___171_5767 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____5769,uu____5770,uu____5771,uu____5772,uu____5773);
                          FStar_Syntax_Syntax.sigrng = uu____5774;
                          FStar_Syntax_Syntax.sigquals = uu____5775;
                          FStar_Syntax_Syntax.sigmeta = uu____5776;
                          FStar_Syntax_Syntax.sigattrs = uu____5777;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____5786 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___172_5821  ->
                    match uu___172_5821 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____5825,uu____5826,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____5828;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____5830;
                        FStar_Syntax_Syntax.sigattrs = uu____5831;_} ->
                        let uu____5842 =
                          let uu____5843 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____5843 in
                        (match uu____5842 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____5849,t,uu____5851,uu____5852,uu____5853);
                             FStar_Syntax_Syntax.sigrng = uu____5854;
                             FStar_Syntax_Syntax.sigquals = uu____5855;
                             FStar_Syntax_Syntax.sigmeta = uu____5856;
                             FStar_Syntax_Syntax.sigattrs = uu____5857;_} ->
                             let uu____5866 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____5866 with
                              | (formals,uu____5882) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____5935  ->
                                            match uu____5935 with
                                            | (x,q) ->
                                                let uu____5948 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____5948
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____6011  ->
                                            match uu____6011 with
                                            | (x,q) ->
                                                let uu____6026 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____6026,
                                                  (x.FStar_Syntax_Syntax.sort)))) in
                                  let fields = fields' in
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
                                    } in
                                  ((let uu____6045 =
                                      let uu____6048 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____6048 in
                                    FStar_ST.write new_globs uu____6045);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____6071 =
                                            match uu____6071 with
                                            | (id,uu____6081) ->
                                                let modul =
                                                  let uu____6091 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____6091.FStar_Ident.str in
                                                let uu____6092 =
                                                  get_exported_id_set e modul in
                                                (match uu____6092 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____6113 =
                                                         let uu____6114 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____6114 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____6113);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____6122 =
                                                               let uu____6123
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____6123.FStar_Ident.ident in
                                                             uu____6122.FStar_Ident.idText in
                                                           let uu____6125 =
                                                             let uu____6126 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____6126 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____6125))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____6145 -> ())
                    | uu____6146 -> ()))
        | uu____6147 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____6164 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____6164 with
        | (ns,id) ->
            let uu____6181 = peek_record_cache () in
            FStar_Util.find_map uu____6181
              (fun record  ->
                 let uu____6187 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____6193  -> FStar_Pervasives_Native.None)
                   uu____6187) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____6195  -> Cont_ignore) (fun uu____6197  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____6203 = find_in_cache fn in
           cont_of_option Cont_ignore uu____6203)
        (fun k  -> fun uu____6209  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____6222 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____6222 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____6228 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____6243 = try_lookup_record_by_field_name env lid in
        match uu____6243 with
        | FStar_Pervasives_Native.Some record' when
            let uu____6247 =
              let uu____6248 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____6248 in
            let uu____6251 =
              let uu____6252 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____6252 in
            uu____6247 = uu____6251 ->
            let uu____6255 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____6259  -> Cont_ok ()) in
            (match uu____6255 with
             | Cont_ok uu____6260 -> true
             | uu____6261 -> false)
        | uu____6264 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____6281 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____6281 with
      | FStar_Pervasives_Native.Some r ->
          let uu____6291 =
            let uu____6296 =
              let uu____6297 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____6297
                (FStar_Ident.range_of_lid fieldname) in
            (uu____6296, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____6291
      | uu____6302 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____6317  ->
    let uu____6318 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____6318
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____6333  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___173_6344  ->
      match uu___173_6344 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___174_6370 =
            match uu___174_6370 with
            | Rec_binding uu____6371 -> true
            | uu____6372 -> false in
          let this_env =
            let uu___185_6374 = env in
            let uu____6375 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___185_6374.curmodule);
              curmonad = (uu___185_6374.curmonad);
              modules = (uu___185_6374.modules);
              scope_mods = uu____6375;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___185_6374.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___185_6374.sigaccum);
              sigmap = (uu___185_6374.sigmap);
              iface = (uu___185_6374.iface);
              admitted_iface = (uu___185_6374.admitted_iface);
              expect_typ = (uu___185_6374.expect_typ);
              docs = (uu___185_6374.docs);
              remaining_iface_decls = (uu___185_6374.remaining_iface_decls);
              syntax_only = (uu___185_6374.syntax_only)
            } in
          let uu____6378 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____6378 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____6389 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___186_6406 = env in
      {
        curmodule = (uu___186_6406.curmodule);
        curmonad = (uu___186_6406.curmonad);
        modules = (uu___186_6406.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___186_6406.exported_ids);
        trans_exported_ids = (uu___186_6406.trans_exported_ids);
        includes = (uu___186_6406.includes);
        sigaccum = (uu___186_6406.sigaccum);
        sigmap = (uu___186_6406.sigmap);
        iface = (uu___186_6406.iface);
        admitted_iface = (uu___186_6406.admitted_iface);
        expect_typ = (uu___186_6406.expect_typ);
        docs = (uu___186_6406.docs);
        remaining_iface_decls = (uu___186_6406.remaining_iface_decls);
        syntax_only = (uu___186_6406.syntax_only)
      }
let push_bv':
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
            FStar_Syntax_Syntax.tun in
        ((push_scope_mod env (Local_binding (x, bv, is_mutable))), bv)
let push_bv_mutable:
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x true
let push_bv:
  env ->
    FStar_Ident.ident ->
      (env,FStar_Syntax_Syntax.bv) FStar_Pervasives_Native.tuple2
  = fun env  -> fun x  -> push_bv' env x false
let push_top_level_rec_binding:
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x in
        let uu____6461 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____6461
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          raise
            (FStar_Errors.Error
               ((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str),
                 (FStar_Ident.range_of_lid l)))
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let err1 l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str in
        let r =
          match sopt with
          | FStar_Pervasives_Native.Some (se,uu____6488) ->
              let uu____6493 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____6493 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____6501 =
          let uu____6502 =
            let uu____6507 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____6507, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____6502 in
        raise uu____6501 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____6516 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____6525 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____6532 -> (true, true)
          | uu____6541 -> (false, false) in
        match uu____6516 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____6547 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____6553 =
                     let uu____6554 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____6554 in
                   if uu____6553
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____6547 with
             | FStar_Pervasives_Native.Some l when
                 let uu____6559 = FStar_Options.interactive () in
                 Prims.op_Negation uu____6559 -> err1 l
             | uu____6560 ->
                 (extract_record env globals s;
                  (let uu___187_6566 = env in
                   {
                     curmodule = (uu___187_6566.curmodule);
                     curmonad = (uu___187_6566.curmonad);
                     modules = (uu___187_6566.modules);
                     scope_mods = (uu___187_6566.scope_mods);
                     exported_ids = (uu___187_6566.exported_ids);
                     trans_exported_ids = (uu___187_6566.trans_exported_ids);
                     includes = (uu___187_6566.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___187_6566.sigmap);
                     iface = (uu___187_6566.iface);
                     admitted_iface = (uu___187_6566.admitted_iface);
                     expect_typ = (uu___187_6566.expect_typ);
                     docs = (uu___187_6566.docs);
                     remaining_iface_decls =
                       (uu___187_6566.remaining_iface_decls);
                     syntax_only = (uu___187_6566.syntax_only)
                   }))) in
      let env2 =
        let uu___188_6568 = env1 in
        let uu____6569 = FStar_ST.read globals in
        {
          curmodule = (uu___188_6568.curmodule);
          curmonad = (uu___188_6568.curmonad);
          modules = (uu___188_6568.modules);
          scope_mods = uu____6569;
          exported_ids = (uu___188_6568.exported_ids);
          trans_exported_ids = (uu___188_6568.trans_exported_ids);
          includes = (uu___188_6568.includes);
          sigaccum = (uu___188_6568.sigaccum);
          sigmap = (uu___188_6568.sigmap);
          iface = (uu___188_6568.iface);
          admitted_iface = (uu___188_6568.admitted_iface);
          expect_typ = (uu___188_6568.expect_typ);
          docs = (uu___188_6568.docs);
          remaining_iface_decls = (uu___188_6568.remaining_iface_decls);
          syntax_only = (uu___188_6568.syntax_only)
        } in
      let uu____6576 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6602) ->
            let uu____6611 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____6611)
        | uu____6638 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____6576 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____6697  ->
                   match uu____6697 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____6718 =
                                  let uu____6721 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____6721 in
                                FStar_ST.write globals uu____6718);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____6733 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____6733.FStar_Ident.str in
                                    ((let uu____6735 =
                                        get_exported_id_set env3 modul in
                                      match uu____6735 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____6755 =
                                            let uu____6756 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____6756 in
                                          FStar_ST.write my_exported_ids
                                            uu____6755
                                      | FStar_Pervasives_Native.None  -> ());
                                     (match () with
                                      | () ->
                                          FStar_Util.smap_add (sigmap env3)
                                            lid.FStar_Ident.str
                                            (se,
                                              (env3.iface &&
                                                 (Prims.op_Negation
                                                    env3.admitted_iface))))))))));
           (let env4 =
              let uu___189_6772 = env3 in
              let uu____6773 = FStar_ST.read globals in
              {
                curmodule = (uu___189_6772.curmodule);
                curmonad = (uu___189_6772.curmonad);
                modules = (uu___189_6772.modules);
                scope_mods = uu____6773;
                exported_ids = (uu___189_6772.exported_ids);
                trans_exported_ids = (uu___189_6772.trans_exported_ids);
                includes = (uu___189_6772.includes);
                sigaccum = (uu___189_6772.sigaccum);
                sigmap = (uu___189_6772.sigmap);
                iface = (uu___189_6772.iface);
                admitted_iface = (uu___189_6772.admitted_iface);
                expect_typ = (uu___189_6772.expect_typ);
                docs = (uu___189_6772.docs);
                remaining_iface_decls = (uu___189_6772.remaining_iface_decls);
                syntax_only = (uu___189_6772.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____6788 =
        let uu____6793 = resolve_module_name env ns false in
        match uu____6793 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____6807 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____6821  ->
                      match uu____6821 with
                      | (m,uu____6827) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____6807
            then (ns, Open_namespace)
            else
              (let uu____6833 =
                 let uu____6834 =
                   let uu____6839 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____6839, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____6834 in
               raise uu____6833)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____6788 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____6857 = resolve_module_name env ns false in
      match uu____6857 with
      | FStar_Pervasives_Native.Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____6864 = current_module env1 in
              uu____6864.FStar_Ident.str in
            (let uu____6866 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____6866 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____6890 =
                   let uu____6893 = FStar_ST.read incl in ns1 :: uu____6893 in
                 FStar_ST.write incl uu____6890);
            (match () with
             | () ->
                 let uu____6904 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____6904 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____6921 =
                          let uu____6938 = get_exported_id_set env1 curmod in
                          let uu____6945 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____6938, uu____6945) in
                        match uu____6921 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____6999 = ns_trans_exports k in
                                FStar_ST.read uu____6999 in
                              let ex = cur_exports k in
                              (let uu____7010 =
                                 let uu____7011 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____7011 ns_ex in
                               FStar_ST.write ex uu____7010);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____7023 =
                                     let uu____7024 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____7024 ns_ex in
                                   FStar_ST.write trans_ex uu____7023) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____7031 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7052 =
                        let uu____7053 =
                          let uu____7058 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____7058, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____7053 in
                      raise uu____7052))))
      | uu____7059 ->
          let uu____7062 =
            let uu____7063 =
              let uu____7068 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____7068, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____7063 in
          raise uu____7062
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____7081 = module_is_defined env l in
        if uu____7081
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____7084 =
             let uu____7085 =
               let uu____7090 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____7090, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____7085 in
           raise uu____7084)
let push_doc:
  env ->
    FStar_Ident.lid ->
      FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | FStar_Pervasives_Native.None  -> env
        | FStar_Pervasives_Native.Some doc1 ->
            ((let uu____7109 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____7109 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____7113 =
                    let uu____7114 = FStar_Ident.string_of_lid l in
                    let uu____7115 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____7116 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____7114 uu____7115 uu____7116 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____7113);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____7133 = try_lookup_lid env l in
                (match uu____7133 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____7145 =
                         let uu____7146 = FStar_Options.interactive () in
                         Prims.op_Negation uu____7146 in
                       if uu____7145
                       then
                         let uu____7147 =
                           let uu____7148 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____7149 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____7148 uu____7149 in
                         FStar_Util.print_string uu____7147
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___190_7159 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___190_7159.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___190_7159.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___190_7159.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___190_7159.FStar_Syntax_Syntax.sigattrs)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____7160 -> ())
            | uu____7169 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7188) ->
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
                                (lid,uu____7208,uu____7209,uu____7210,uu____7211,uu____7212)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____7221 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____7224,uu____7225) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____7231,lbs),uu____7233) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____7254 =
                               let uu____7255 =
                                 let uu____7256 =
                                   let uu____7259 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____7259.FStar_Syntax_Syntax.fv_name in
                                 uu____7256.FStar_Syntax_Syntax.v in
                               uu____7255.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____7254))
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
                               let uu____7273 =
                                 let uu____7276 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____7276.FStar_Syntax_Syntax.fv_name in
                               uu____7273.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___191_7281 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___191_7281.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___191_7281.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___191_7281.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____7293 -> ()));
      (let curmod =
         let uu____7295 = current_module env in uu____7295.FStar_Ident.str in
       (let uu____7297 =
          let uu____7314 = get_exported_id_set env curmod in
          let uu____7321 = get_trans_exported_id_set env curmod in
          (uu____7314, uu____7321) in
        match uu____7297 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____7375 = cur_ex eikind in FStar_ST.read uu____7375 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____7385 =
                let uu____7386 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____7386 in
              FStar_ST.write cur_trans_ex_set_ref uu____7385 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____7393 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___192_7411 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___192_7411.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___192_7411.exported_ids);
                    trans_exported_ids = (uu___192_7411.trans_exported_ids);
                    includes = (uu___192_7411.includes);
                    sigaccum = [];
                    sigmap = (uu___192_7411.sigmap);
                    iface = (uu___192_7411.iface);
                    admitted_iface = (uu___192_7411.admitted_iface);
                    expect_typ = (uu___192_7411.expect_typ);
                    docs = (uu___192_7411.docs);
                    remaining_iface_decls =
                      (uu___192_7411.remaining_iface_decls);
                    syntax_only = (uu___192_7411.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____7429 =
       let uu____7432 = FStar_ST.read stack in env :: uu____7432 in
     FStar_ST.write stack uu____7429);
    (let uu___193_7439 = env in
     let uu____7440 = FStar_Util.smap_copy (sigmap env) in
     let uu____7451 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___193_7439.curmodule);
       curmonad = (uu___193_7439.curmonad);
       modules = (uu___193_7439.modules);
       scope_mods = (uu___193_7439.scope_mods);
       exported_ids = (uu___193_7439.exported_ids);
       trans_exported_ids = (uu___193_7439.trans_exported_ids);
       includes = (uu___193_7439.includes);
       sigaccum = (uu___193_7439.sigaccum);
       sigmap = uu____7440;
       iface = (uu___193_7439.iface);
       admitted_iface = (uu___193_7439.admitted_iface);
       expect_typ = (uu___193_7439.expect_typ);
       docs = uu____7451;
       remaining_iface_decls = (uu___193_7439.remaining_iface_decls);
       syntax_only = (uu___193_7439.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____7457  ->
    let uu____7458 = FStar_ST.read stack in
    match uu____7458 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____7471 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____7479 = FStar_ST.read stack in
     match uu____7479 with
     | uu____7484::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____7491 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____7501  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____7515 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____7518 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____7552 = FStar_Util.smap_try_find sm' k in
              match uu____7552 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___194_7577 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___194_7577.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___194_7577.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___194_7577.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___194_7577.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____7578 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____7583 -> ()));
      env1
let finish_module_or_interface: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
      then check_admits env
      else ();
      finish env modul
let prepare_module_or_interface:
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident -> (env,Prims.bool) FStar_Pervasives_Native.tuple2
  =
  fun intf  ->
    fun admitted  ->
      fun env  ->
        fun mname  ->
          let prep env1 =
            let filename =
              FStar_Util.strcat (FStar_Ident.text_of_lid mname) ".fst" in
            let auto_open = FStar_Parser_Dep.hard_coded_dependencies filename in
            let auto_open1 =
              let convert_kind uu___175_7642 =
                match uu___175_7642 with
                | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                | FStar_Parser_Dep.Open_module  -> Open_module in
              FStar_List.map
                (fun uu____7654  ->
                   match uu____7654 with
                   | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
            let namespace_of_module =
              if
                (FStar_List.length mname.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                let uu____7678 =
                  let uu____7683 =
                    FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                  (uu____7683, Open_namespace) in
                [uu____7678]
              else [] in
            let auto_open2 =
              FStar_List.rev
                (FStar_List.append auto_open1 namespace_of_module) in
            (let uu____7713 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____7713);
            (match () with
             | () ->
                 ((let uu____7717 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____7717);
                  (match () with
                   | () ->
                       ((let uu____7721 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____7721);
                        (match () with
                         | () ->
                             let uu___195_7734 = env1 in
                             let uu____7735 =
                               FStar_List.map
                                 (fun x  -> Open_module_or_namespace x)
                                 auto_open2 in
                             {
                               curmodule =
                                 (FStar_Pervasives_Native.Some mname);
                               curmonad = (uu___195_7734.curmonad);
                               modules = (uu___195_7734.modules);
                               scope_mods = uu____7735;
                               exported_ids = (uu___195_7734.exported_ids);
                               trans_exported_ids =
                                 (uu___195_7734.trans_exported_ids);
                               includes = (uu___195_7734.includes);
                               sigaccum = (uu___195_7734.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___195_7734.expect_typ);
                               docs = (uu___195_7734.docs);
                               remaining_iface_decls =
                                 (uu___195_7734.remaining_iface_decls);
                               syntax_only = (uu___195_7734.syntax_only)
                             }))))) in
          let uu____7740 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____7766  ->
                    match uu____7766 with
                    | (l,uu____7772) -> FStar_Ident.lid_equals l mname)) in
          match uu____7740 with
          | FStar_Pervasives_Native.None  ->
              let uu____7781 = prep env in (uu____7781, false)
          | FStar_Pervasives_Native.Some (uu____7782,m) ->
              ((let uu____7789 =
                  (let uu____7792 = FStar_Options.interactive () in
                   Prims.op_Negation uu____7792) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____7789
                then
                  let uu____7793 =
                    let uu____7794 =
                      let uu____7799 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____7799, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____7794 in
                  raise uu____7793
                else ());
               (let uu____7801 = let uu____7802 = push env in prep uu____7802 in
                (uu____7801, true)))
let enter_monad_scope: env -> FStar_Ident.ident -> env =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          raise
            (FStar_Errors.Error
               ((Prims.strcat "Trying to define monad "
                   (Prims.strcat mname.FStar_Ident.idText
                      (Prims.strcat ", but already in monad scope "
                         mname'.FStar_Ident.idText))),
                 (mname.FStar_Ident.idRange)))
      | FStar_Pervasives_Native.None  ->
          let uu___196_7812 = env in
          {
            curmodule = (uu___196_7812.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___196_7812.modules);
            scope_mods = (uu___196_7812.scope_mods);
            exported_ids = (uu___196_7812.exported_ids);
            trans_exported_ids = (uu___196_7812.trans_exported_ids);
            includes = (uu___196_7812.includes);
            sigaccum = (uu___196_7812.sigaccum);
            sigmap = (uu___196_7812.sigmap);
            iface = (uu___196_7812.iface);
            admitted_iface = (uu___196_7812.admitted_iface);
            expect_typ = (uu___196_7812.expect_typ);
            docs = (uu___196_7812.docs);
            remaining_iface_decls = (uu___196_7812.remaining_iface_decls);
            syntax_only = (uu___196_7812.syntax_only)
          }
let fail_or env lookup lid =
  let uu____7843 = lookup lid in
  match uu____7843 with
  | FStar_Pervasives_Native.None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____7856  ->
             match uu____7856 with
             | (lid1,uu____7862) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____7867 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____7867
               (FStar_Ident.range_of_lid lid) in
           let uu____7868 = resolve_module_name env modul true in
           match uu____7868 with
           | FStar_Pervasives_Native.None  ->
               let opened_modules1 = FStar_String.concat ", " opened_modules in
               FStar_Util.format3
                 "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str opened_modules1
           | FStar_Pervasives_Native.Some modul' when
               Prims.op_Negation
                 (FStar_List.existsb (fun m  -> m = modul'.FStar_Ident.str)
                    opened_modules)
               ->
               let opened_modules1 = FStar_String.concat ", " opened_modules in
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 opened_modules1
           | FStar_Pervasives_Native.Some modul' ->
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, definition %s not found"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 (lid.FStar_Ident.ident).FStar_Ident.idText) in
      raise (FStar_Errors.Error (msg1, (FStar_Ident.range_of_lid lid)))
  | FStar_Pervasives_Native.Some r -> r
let fail_or2 lookup id =
  let uu____7902 = lookup id in
  match uu____7902 with
  | FStar_Pervasives_Native.None  ->
      raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | FStar_Pervasives_Native.Some r -> r