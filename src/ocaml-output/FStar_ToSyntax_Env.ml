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
  | Open_namespace[@@deriving show]
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____21 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____26 -> false
type open_module_or_namespace =
  (FStar_Ident.lident,open_kind) FStar_Pervasives_Native.tuple2[@@deriving
                                                                 show]
type record_or_dc =
  {
  typename: FStar_Ident.lident;
  constrname: FStar_Ident.ident;
  parms: FStar_Syntax_Syntax.binders;
  fields:
    (FStar_Ident.ident,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list;
  is_private_or_abstract: Prims.bool;
  is_record: Prims.bool;}[@@deriving show]
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
  | Record_or_dc of record_or_dc[@@deriving show]
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
type string_set = Prims.string FStar_Util.set[@@deriving show]
type exported_id_kind =
  | Exported_id_term_type
  | Exported_id_field[@@deriving show]
let uu___is_Exported_id_term_type: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____283 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____288 -> false
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref[@@deriving
                                                                    show]
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
  syntax_only: Prims.bool;}[@@deriving show]
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
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____1367 -> false
let __proj__Term_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____1397 -> false
let __proj__Eff_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___184_1426 = env in
      {
        curmodule = (uu___184_1426.curmodule);
        curmonad = (uu___184_1426.curmonad);
        modules = (uu___184_1426.modules);
        scope_mods = (uu___184_1426.scope_mods);
        exported_ids = (uu___184_1426.exported_ids);
        trans_exported_ids = (uu___184_1426.trans_exported_ids);
        includes = (uu___184_1426.includes);
        sigaccum = (uu___184_1426.sigaccum);
        sigmap = (uu___184_1426.sigmap);
        iface = b;
        admitted_iface = (uu___184_1426.admitted_iface);
        expect_typ = (uu___184_1426.expect_typ);
        docs = (uu___184_1426.docs);
        remaining_iface_decls = (uu___184_1426.remaining_iface_decls);
        syntax_only = (uu___184_1426.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___185_1439 = e in
      {
        curmodule = (uu___185_1439.curmodule);
        curmonad = (uu___185_1439.curmonad);
        modules = (uu___185_1439.modules);
        scope_mods = (uu___185_1439.scope_mods);
        exported_ids = (uu___185_1439.exported_ids);
        trans_exported_ids = (uu___185_1439.trans_exported_ids);
        includes = (uu___185_1439.includes);
        sigaccum = (uu___185_1439.sigaccum);
        sigmap = (uu___185_1439.sigmap);
        iface = (uu___185_1439.iface);
        admitted_iface = b;
        expect_typ = (uu___185_1439.expect_typ);
        docs = (uu___185_1439.docs);
        remaining_iface_decls = (uu___185_1439.remaining_iface_decls);
        syntax_only = (uu___185_1439.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___186_1452 = e in
      {
        curmodule = (uu___186_1452.curmodule);
        curmonad = (uu___186_1452.curmonad);
        modules = (uu___186_1452.modules);
        scope_mods = (uu___186_1452.scope_mods);
        exported_ids = (uu___186_1452.exported_ids);
        trans_exported_ids = (uu___186_1452.trans_exported_ids);
        includes = (uu___186_1452.includes);
        sigaccum = (uu___186_1452.sigaccum);
        sigmap = (uu___186_1452.sigmap);
        iface = (uu___186_1452.iface);
        admitted_iface = (uu___186_1452.admitted_iface);
        expect_typ = b;
        docs = (uu___186_1452.docs);
        remaining_iface_decls = (uu___186_1452.remaining_iface_decls);
        syntax_only = (uu___186_1452.syntax_only)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1470 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1470 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1476 =
            let uu____1477 = exported_id_set Exported_id_term_type in
            FStar_ST.op_Bang uu____1477 in
          FStar_All.pipe_right uu____1476 FStar_Util.set_elements
let open_modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  = fun e  -> e.modules
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___187_1669 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___187_1669.curmonad);
        modules = (uu___187_1669.modules);
        scope_mods = (uu___187_1669.scope_mods);
        exported_ids = (uu___187_1669.exported_ids);
        trans_exported_ids = (uu___187_1669.trans_exported_ids);
        includes = (uu___187_1669.includes);
        sigaccum = (uu___187_1669.sigaccum);
        sigmap = (uu___187_1669.sigmap);
        iface = (uu___187_1669.iface);
        admitted_iface = (uu___187_1669.admitted_iface);
        expect_typ = (uu___187_1669.expect_typ);
        docs = (uu___187_1669.docs);
        remaining_iface_decls = (uu___187_1669.remaining_iface_decls);
        syntax_only = (uu___187_1669.syntax_only)
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
      let uu____1687 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____1721  ->
                match uu____1721 with
                | (m,uu____1729) -> FStar_Ident.lid_equals l m)) in
      match uu____1687 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____1746,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____1776 =
          FStar_List.partition
            (fun uu____1806  ->
               match uu____1806 with
               | (m,uu____1814) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____1776 with
        | (uu____1819,rest) ->
            let uu___188_1853 = env in
            {
              curmodule = (uu___188_1853.curmodule);
              curmonad = (uu___188_1853.curmonad);
              modules = (uu___188_1853.modules);
              scope_mods = (uu___188_1853.scope_mods);
              exported_ids = (uu___188_1853.exported_ids);
              trans_exported_ids = (uu___188_1853.trans_exported_ids);
              includes = (uu___188_1853.includes);
              sigaccum = (uu___188_1853.sigaccum);
              sigmap = (uu___188_1853.sigmap);
              iface = (uu___188_1853.iface);
              admitted_iface = (uu___188_1853.admitted_iface);
              expect_typ = (uu___188_1853.expect_typ);
              docs = (uu___188_1853.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___188_1853.syntax_only)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____1876 = current_module env in qual uu____1876 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____1878 =
            let uu____1879 = current_module env in qual uu____1879 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____1878 id1
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___189_1892 = env in
      {
        curmodule = (uu___189_1892.curmodule);
        curmonad = (uu___189_1892.curmonad);
        modules = (uu___189_1892.modules);
        scope_mods = (uu___189_1892.scope_mods);
        exported_ids = (uu___189_1892.exported_ids);
        trans_exported_ids = (uu___189_1892.trans_exported_ids);
        includes = (uu___189_1892.includes);
        sigaccum = (uu___189_1892.sigaccum);
        sigmap = (uu___189_1892.sigmap);
        iface = (uu___189_1892.iface);
        admitted_iface = (uu___189_1892.admitted_iface);
        expect_typ = (uu___189_1892.expect_typ);
        docs = (uu___189_1892.docs);
        remaining_iface_decls = (uu___189_1892.remaining_iface_decls);
        syntax_only = b
      }
let new_sigmap: 'Auu____1897 . Prims.unit -> 'Auu____1897 FStar_Util.smap =
  fun uu____1903  -> FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____1907  ->
    let uu____1908 = new_sigmap () in
    let uu____1911 = new_sigmap () in
    let uu____1914 = new_sigmap () in
    let uu____1925 = new_sigmap () in
    let uu____1936 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____1908;
      trans_exported_ids = uu____1911;
      includes = uu____1914;
      sigaccum = [];
      sigmap = uu____1925;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____1936;
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
      (fun uu____1970  ->
         match uu____1970 with
         | (m,uu____1976) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___190_1986 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___190_1986.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___191_1987 = bv in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___191_1987.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___191_1987.FStar_Syntax_Syntax.sort)
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
  fun id1  ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____2077  ->
           match uu____2077 with
           | (x,y,dd,dq) ->
               if id1.FStar_Ident.idText = x
               then
                 let uu____2100 =
                   let uu____2101 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id1.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2101 dd dq in
                 FStar_Pervasives_Native.Some uu____2100
               else FStar_Pervasives_Native.None) in
    match t with
    | FStar_Pervasives_Native.Some v1 ->
        FStar_Pervasives_Native.Some (v1, false)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore[@@deriving show]
let uu___is_Cont_ok: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____2146 -> false
let __proj__Cont_ok__item___0: 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2179 -> false
let uu___is_Cont_ignore: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2195 -> false
let option_of_cont:
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___153_2221  ->
      match uu___153_2221 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
let find_in_record:
  'Auu____2239 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2239 cont_t) -> 'Auu____2239 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident]) in
          if FStar_Ident.lid_equals typename' record.typename
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1]) in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2285  ->
                   match uu____2285 with
                   | (f,uu____2293) ->
                       if id1.FStar_Ident.idText = f.FStar_Ident.idText
                       then FStar_Pervasives_Native.Some record
                       else FStar_Pervasives_Native.None) in
            match find1 with
            | FStar_Pervasives_Native.Some r -> cont r
            | FStar_Pervasives_Native.None  -> Cont_ignore
          else Cont_ignore
let get_exported_id_set:
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option
  = fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname
let get_trans_exported_id_set:
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option
  =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname
let string_of_exported_id_kind: exported_id_kind -> Prims.string =
  fun uu___154_2344  ->
    match uu___154_2344 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes:
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
              let idstr = id1.FStar_Ident.idText in
              let rec aux uu___155_2407 =
                match uu___155_2407 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____2418 = get_exported_id_set env mname in
                      match uu____2418 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2439 = mex eikind in
                            FStar_ST.op_Bang uu____2439 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____2614 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____2614 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____2677 = qual modul id1 in
                        find_in_module uu____2677
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____2681 -> look_into) in
              aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___156_2687  ->
    match uu___156_2687 with
    | Exported_id_field  -> true
    | uu____2688 -> false
let try_lookup_id'':
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
                  let check_local_binding_id uu___157_2799 =
                    match uu___157_2799 with
                    | (id',uu____2801,uu____2802) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let check_rec_binding_id uu___158_2806 =
                    match uu___158_2806 with
                    | (id',uu____2808,uu____2809) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____2813 = current_module env in
                    FStar_Ident.ids_of_lid uu____2813 in
                  let proc uu___159_2819 =
                    match uu___159_2819 with
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
                        let uu____2827 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____2827 id1
                    | uu____2832 -> Cont_ignore in
                  let rec aux uu___160_2840 =
                    match uu___160_2840 with
                    | a::q ->
                        let uu____2849 = proc a in
                        option_of_cont (fun uu____2853  -> aux q) uu____2849
                    | [] ->
                        let uu____2854 = lookup_default_id Cont_fail id1 in
                        option_of_cont
                          (fun uu____2858  -> FStar_Pervasives_Native.None)
                          uu____2854 in
                  aux env.scope_mods
let found_local_binding:
  'Auu____2867 'Auu____2868 .
    FStar_Range.range ->
      ('Auu____2868,FStar_Syntax_Syntax.bv,'Auu____2867)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____2867)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____2886  ->
      match uu____2886 with
      | (id',x,mut) -> let uu____2896 = bv_to_name x r in (uu____2896, mut)
let find_in_module:
  'Auu____2907 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____2907)
          -> 'Auu____2907 -> 'Auu____2907
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____2942 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____2942 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
let try_lookup_id:
  env ->
    FStar_Ident.ident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun id1  ->
      let uu____2980 = unmangleOpName id1 in
      match uu____2980 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3006 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3020 = found_local_binding id1.FStar_Ident.idRange r in
               Cont_ok uu____3020) (fun uu____3030  -> Cont_fail)
            (fun uu____3036  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3051  -> fun uu____3052  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3067  -> fun uu____3068  -> Cont_fail)
let lookup_default_id:
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
            | FStar_Pervasives_Native.Some uu____3143 ->
                let lid = qualify env id1 in
                let uu____3145 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3145 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3169 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3169
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3192 = current_module env in qual uu____3192 id1 in
              find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____3204 = current_module env in
           FStar_Ident.lid_equals lid uu____3204)
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
        let rec aux uu___161_3239 =
          match uu___161_3239 with
          | [] ->
              let uu____3244 = module_is_defined env lid in
              if uu____3244
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3253 =
                  let uu____3256 = FStar_Ident.path_of_lid ns in
                  let uu____3259 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3256 uu____3259 in
                FStar_Ident.lid_of_path uu____3253
                  (FStar_Ident.range_of_lid lid) in
              let uu____3262 = module_is_defined env new_lid in
              if uu____3262
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3268 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3275::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3291 =
          let uu____3292 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____3292 in
        if uu____3291
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3294 =
                let uu____3295 =
                  let uu____3300 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____3300, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____3295 in
              FStar_Exn.raise uu____3294))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3310 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____3314 = resolve_module_name env modul_orig true in
          (match uu____3314 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3318 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___162_3331  ->
           match uu___162_3331 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____3333 -> false) env.scope_mods
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
        let rec aux revns id1 =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id1 in
          if namespace_is_open env lid
          then
            FStar_Pervasives_Native.Some
              ((FStar_List.rev (id1 :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu____3425 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3425
                   (FStar_Util.map_option
                      (fun uu____3475  ->
                         match uu____3475 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids))))) in
        let uu____3506 =
          is_full_path &&
            (let uu____3508 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____3508) in
        if uu____3506
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3538 = aux ns_rev_prefix ns_last_id in
               (match uu____3538 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____3599 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____3599 with
      | (uu____3608,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'':
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
                  | uu____3725::uu____3726 ->
                      let uu____3729 =
                        let uu____3732 =
                          let uu____3733 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          FStar_Ident.set_lid_range uu____3733
                            (FStar_Ident.range_of_lid lid) in
                        resolve_module_name env uu____3732 true in
                      (match uu____3729 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____3737 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____3741  -> FStar_Pervasives_Native.None)
                             uu____3737)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option:
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___163_3762  ->
      match uu___163_3762 with
      | FStar_Pervasives_Native.Some v1 -> Cont_ok v1
      | FStar_Pervasives_Native.None  -> k_none
let resolve_in_open_namespaces':
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
              let uu____3867 = k_global_def lid1 def in
              cont_of_option k uu____3867 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____3897 = k_local_binding l in
                 cont_of_option Cont_fail uu____3897)
              (fun r  ->
                 let uu____3903 = k_rec_binding r in
                 cont_of_option Cont_fail uu____3903)
              (fun uu____3907  -> Cont_ignore) f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____3916,uu____3917,uu____3918,l,uu____3920,uu____3921) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___164_3932  ->
               match uu___164_3932 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____3935,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____3947 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____3953,uu____3954,uu____3955)
        -> FStar_Pervasives_Native.None
    | uu____3956 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____3969 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____3977 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____3977
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____3969 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____3992 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____3992 ns)
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
          let k_global_def source_lid uu___169_4026 =
            match uu___169_4026 with
            | (uu____4033,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4035) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4038 ->
                     let uu____4055 =
                       let uu____4056 =
                         let uu____4061 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4061, false) in
                       Term_name uu____4056 in
                     FStar_Pervasives_Native.Some uu____4055
                 | FStar_Syntax_Syntax.Sig_datacon uu____4062 ->
                     let uu____4077 =
                       let uu____4078 =
                         let uu____4083 =
                           let uu____4084 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4084 in
                         (uu____4083, false) in
                       Term_name uu____4078 in
                     FStar_Pervasives_Native.Some uu____4077
                 | FStar_Syntax_Syntax.Sig_let ((uu____4087,lbs),uu____4089)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4105 =
                       let uu____4106 =
                         let uu____4111 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4111, false) in
                       Term_name uu____4106 in
                     FStar_Pervasives_Native.Some uu____4105
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4113,uu____4114) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4118 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___165_4122  ->
                                  match uu___165_4122 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4123 -> false))) in
                     if uu____4118
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____4128 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___166_4133  ->
                                      match uu___166_4133 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4134 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4139 -> true
                                      | uu____4140 -> false))) in
                         if uu____4128
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let dd1 =
                         let uu____4143 =
                           FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___167_4147  ->
                                   match uu___167_4147 with
                                   | FStar_Syntax_Syntax.Abstract  -> true
                                   | uu____4148 -> false)) in
                         if uu____4143
                         then FStar_Syntax_Syntax.Delta_abstract dd
                         else dd in
                       let uu____4150 =
                         FStar_Util.find_map quals
                           (fun uu___168_4155  ->
                              match uu___168_4155 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4159 -> FStar_Pervasives_Native.None) in
                       (match uu____4150 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____4168 ->
                            let uu____4171 =
                              let uu____4172 =
                                let uu____4177 =
                                  let uu____4178 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd1
                                    uu____4178 in
                                (uu____4177, false) in
                              Term_name uu____4172 in
                            FStar_Pervasives_Native.Some uu____4171)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4184 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4197 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____4216 =
              let uu____4217 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____4217 in
            FStar_Pervasives_Native.Some uu____4216 in
          let k_rec_binding uu____4233 =
            match uu____4233 with
            | (id1,l,dd) ->
                let uu____4245 =
                  let uu____4246 =
                    let uu____4251 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____4251, false) in
                  Term_name uu____4246 in
                FStar_Pervasives_Native.Some uu____4245 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4257 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____4257 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____4275 -> FStar_Pervasives_Native.None)
            | uu____4282 -> FStar_Pervasives_Native.None in
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
        let uu____4314 = try_lookup_name true exclude_interf env lid in
        match uu____4314 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4329 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4346 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4346 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4361 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4384 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4384 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4400;
             FStar_Syntax_Syntax.sigquals = uu____4401;
             FStar_Syntax_Syntax.sigmeta = uu____4402;
             FStar_Syntax_Syntax.sigattrs = uu____4403;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4422;
             FStar_Syntax_Syntax.sigquals = uu____4423;
             FStar_Syntax_Syntax.sigmeta = uu____4424;
             FStar_Syntax_Syntax.sigattrs = uu____4425;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4443,uu____4444,uu____4445,uu____4446,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4448;
             FStar_Syntax_Syntax.sigquals = uu____4449;
             FStar_Syntax_Syntax.sigmeta = uu____4450;
             FStar_Syntax_Syntax.sigattrs = uu____4451;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4473 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4496 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4496 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4506;
             FStar_Syntax_Syntax.sigquals = uu____4507;
             FStar_Syntax_Syntax.sigmeta = uu____4508;
             FStar_Syntax_Syntax.sigattrs = uu____4509;_},uu____4510)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4520;
             FStar_Syntax_Syntax.sigquals = uu____4521;
             FStar_Syntax_Syntax.sigmeta = uu____4522;
             FStar_Syntax_Syntax.sigattrs = uu____4523;_},uu____4524)
          -> FStar_Pervasives_Native.Some ne
      | uu____4533 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4548 = try_lookup_effect_name env lid in
      match uu____4548 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4551 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4562 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4562 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____4572,uu____4573,uu____4574,uu____4575);
             FStar_Syntax_Syntax.sigrng = uu____4576;
             FStar_Syntax_Syntax.sigquals = uu____4577;
             FStar_Syntax_Syntax.sigmeta = uu____4578;
             FStar_Syntax_Syntax.sigattrs = uu____4579;_},uu____4580)
          ->
          let rec aux new_name =
            let uu____4599 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____4599 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____4617) ->
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
                     (uu____4626,uu____4627,uu____4628,cmp,uu____4630) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____4636 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4637,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4643 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___170_4674 =
        match uu___170_4674 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4683,uu____4684,uu____4685);
             FStar_Syntax_Syntax.sigrng = uu____4686;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4688;
             FStar_Syntax_Syntax.sigattrs = uu____4689;_},uu____4690)
            -> FStar_Pervasives_Native.Some quals
        | uu____4697 -> FStar_Pervasives_Native.None in
      let uu____4704 =
        resolve_in_open_namespaces' env lid
          (fun uu____4712  -> FStar_Pervasives_Native.None)
          (fun uu____4716  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____4704 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____4726 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____4745 =
        FStar_List.tryFind
          (fun uu____4760  ->
             match uu____4760 with
             | (mlid,modul) ->
                 let uu____4767 = FStar_Ident.path_of_lid mlid in
                 uu____4767 = path) env.modules in
      match uu____4745 with
      | FStar_Pervasives_Native.Some (uu____4774,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___171_4806 =
        match uu___171_4806 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____4813,lbs),uu____4815);
             FStar_Syntax_Syntax.sigrng = uu____4816;
             FStar_Syntax_Syntax.sigquals = uu____4817;
             FStar_Syntax_Syntax.sigmeta = uu____4818;
             FStar_Syntax_Syntax.sigattrs = uu____4819;_},uu____4820)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____4840 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____4840
        | uu____4841 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____4847  -> FStar_Pervasives_Native.None)
        (fun uu____4849  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___172_4874 =
        match uu___172_4874 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____4884);
             FStar_Syntax_Syntax.sigrng = uu____4885;
             FStar_Syntax_Syntax.sigquals = uu____4886;
             FStar_Syntax_Syntax.sigmeta = uu____4887;
             FStar_Syntax_Syntax.sigattrs = uu____4888;_},uu____4889)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____4912 -> FStar_Pervasives_Native.None)
        | uu____4919 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____4929  -> FStar_Pervasives_Native.None)
        (fun uu____4933  -> FStar_Pervasives_Native.None) k_global_def
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
          let uu____4976 = try_lookup_name any_val exclude_interf env lid in
          match uu____4976 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____4991 -> FStar_Pervasives_Native.None
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
      let uu____5022 = try_lookup_lid env l in
      match uu____5022 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5036) ->
          let uu____5041 =
            let uu____5042 = FStar_Syntax_Subst.compress e in
            uu____5042.FStar_Syntax_Syntax.n in
          (match uu____5041 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5048 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___192_5064 = env in
        {
          curmodule = (uu___192_5064.curmodule);
          curmonad = (uu___192_5064.curmonad);
          modules = (uu___192_5064.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___192_5064.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___192_5064.sigaccum);
          sigmap = (uu___192_5064.sigmap);
          iface = (uu___192_5064.iface);
          admitted_iface = (uu___192_5064.admitted_iface);
          expect_typ = (uu___192_5064.expect_typ);
          docs = (uu___192_5064.docs);
          remaining_iface_decls = (uu___192_5064.remaining_iface_decls);
          syntax_only = (uu___192_5064.syntax_only)
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
      let k_global_def lid1 uu___174_5097 =
        match uu___174_5097 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5104,uu____5105,uu____5106);
             FStar_Syntax_Syntax.sigrng = uu____5107;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5109;
             FStar_Syntax_Syntax.sigattrs = uu____5110;_},uu____5111)
            ->
            let uu____5116 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___173_5120  ->
                      match uu___173_5120 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5121 -> false)) in
            if uu____5116
            then
              let uu____5124 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____5124
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5126;
             FStar_Syntax_Syntax.sigrng = uu____5127;
             FStar_Syntax_Syntax.sigquals = uu____5128;
             FStar_Syntax_Syntax.sigmeta = uu____5129;
             FStar_Syntax_Syntax.sigattrs = uu____5130;_},uu____5131)
            ->
            let uu____5150 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____5150
        | uu____5151 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5157  -> FStar_Pervasives_Native.None)
        (fun uu____5159  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___175_5186 =
        match uu___175_5186 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5195,uu____5196,uu____5197,uu____5198,datas,uu____5200);
             FStar_Syntax_Syntax.sigrng = uu____5201;
             FStar_Syntax_Syntax.sigquals = uu____5202;
             FStar_Syntax_Syntax.sigmeta = uu____5203;
             FStar_Syntax_Syntax.sigattrs = uu____5204;_},uu____5205)
            -> FStar_Pervasives_Native.Some datas
        | uu____5220 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5230  -> FStar_Pervasives_Native.None)
        (fun uu____5234  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit,Prims.unit -> Prims.unit)
     FStar_Pervasives_Native.tuple5,Prims.unit -> Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____5283 =
    let uu____5284 =
      let uu____5289 =
        let uu____5292 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____5292 in
      let uu____5339 = FStar_ST.op_Bang record_cache in uu____5289 ::
        uu____5339 in
    FStar_ST.op_Colon_Equals record_cache uu____5284 in
  let pop1 uu____5429 =
    let uu____5430 =
      let uu____5435 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____5435 in
    FStar_ST.op_Colon_Equals record_cache uu____5430 in
  let peek1 uu____5527 =
    let uu____5528 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____5528 in
  let insert r =
    let uu____5579 =
      let uu____5584 = let uu____5587 = peek1 () in r :: uu____5587 in
      let uu____5590 =
        let uu____5595 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____5595 in
      uu____5584 :: uu____5590 in
    FStar_ST.op_Colon_Equals record_cache uu____5579 in
  let commit1 uu____5687 =
    let uu____5688 = FStar_ST.op_Bang record_cache in
    match uu____5688 with
    | hd1::uu____5734::tl1 ->
        FStar_ST.op_Colon_Equals record_cache (hd1 :: tl1)
    | uu____5790 -> failwith "Impossible" in
  let filter1 uu____5798 =
    let rc = peek1 () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____5808 =
           let uu____5813 = FStar_ST.op_Bang record_cache in filtered ::
             uu____5813 in
         FStar_ST.op_Colon_Equals record_cache uu____5808) in
  let aux = (push1, pop1, peek1, insert, commit1) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit,
    Prims.unit -> Prims.unit) FStar_Pervasives_Native.tuple5
  =
  let uu____5981 = record_cache_aux_with_filter in
  match uu____5981 with | (aux,uu____6033) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____6085 = record_cache_aux_with_filter in
  match uu____6085 with | (uu____6116,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____6169 = record_cache_aux in
  match uu____6169 with
  | (push1,uu____6195,uu____6196,uu____6197,uu____6198) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____6226 = record_cache_aux in
  match uu____6226 with
  | (uu____6251,pop1,uu____6253,uu____6254,uu____6255) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____6285 = record_cache_aux in
  match uu____6285 with
  | (uu____6312,uu____6313,peek1,uu____6315,uu____6316) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____6344 = record_cache_aux in
  match uu____6344 with
  | (uu____6369,uu____6370,uu____6371,insert,uu____6373) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____6401 = record_cache_aux in
  match uu____6401 with
  | (uu____6426,uu____6427,uu____6428,uu____6429,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____6490) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___176_6506  ->
                   match uu___176_6506 with
                   | FStar_Syntax_Syntax.RecordType uu____6507 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____6516 -> true
                   | uu____6525 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___177_6547  ->
                      match uu___177_6547 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____6549,uu____6550,uu____6551,uu____6552,uu____6553);
                          FStar_Syntax_Syntax.sigrng = uu____6554;
                          FStar_Syntax_Syntax.sigquals = uu____6555;
                          FStar_Syntax_Syntax.sigmeta = uu____6556;
                          FStar_Syntax_Syntax.sigattrs = uu____6557;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____6566 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___178_6601  ->
                    match uu___178_6601 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____6605,uu____6606,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____6608;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____6610;
                        FStar_Syntax_Syntax.sigattrs = uu____6611;_} ->
                        let uu____6622 =
                          let uu____6623 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____6623 in
                        (match uu____6622 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____6629,t,uu____6631,uu____6632,uu____6633);
                             FStar_Syntax_Syntax.sigrng = uu____6634;
                             FStar_Syntax_Syntax.sigquals = uu____6635;
                             FStar_Syntax_Syntax.sigmeta = uu____6636;
                             FStar_Syntax_Syntax.sigattrs = uu____6637;_} ->
                             let uu____6646 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____6646 with
                              | (formals,uu____6660) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____6709  ->
                                            match uu____6709 with
                                            | (x,q) ->
                                                let uu____6722 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____6722
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____6779  ->
                                            match uu____6779 with
                                            | (x,q) ->
                                                let uu____6792 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____6792,
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
                                  ((let uu____6807 =
                                      let uu____6810 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____6810 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____6807);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____6887 =
                                            match uu____6887 with
                                            | (id1,uu____6895) ->
                                                let modul =
                                                  let uu____6901 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____6901.FStar_Ident.str in
                                                let uu____6902 =
                                                  get_exported_id_set e modul in
                                                (match uu____6902 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____6929 =
                                                         let uu____6930 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____6930 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____6929);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____6982 =
                                                               let uu____6983
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1 in
                                                               uu____6983.FStar_Ident.ident in
                                                             uu____6982.FStar_Ident.idText in
                                                           let uu____6985 =
                                                             let uu____6986 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____6986 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____6985))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____7047 -> ())
                    | uu____7048 -> ()))
        | uu____7049 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____7066 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____7066 with
        | (ns,id1) ->
            let uu____7083 = peek_record_cache () in
            FStar_Util.find_map uu____7083
              (fun record  ->
                 let uu____7089 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____7095  -> FStar_Pervasives_Native.None)
                   uu____7089) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____7097  -> Cont_ignore) (fun uu____7099  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____7105 = find_in_cache fn in
           cont_of_option Cont_ignore uu____7105)
        (fun k  -> fun uu____7111  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____7124 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7124 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7130 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____7145 = try_lookup_record_by_field_name env lid in
        match uu____7145 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7149 =
              let uu____7150 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7150 in
            let uu____7153 =
              let uu____7154 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7154 in
            uu____7149 = uu____7153 ->
            let uu____7157 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____7161  -> Cont_ok ()) in
            (match uu____7157 with
             | Cont_ok uu____7162 -> true
             | uu____7163 -> false)
        | uu____7166 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____7183 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7183 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7193 =
            let uu____7198 =
              let uu____7199 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____7199
                (FStar_Ident.range_of_lid fieldname) in
            (uu____7198, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____7193
      | uu____7204 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____7225  ->
    let uu____7226 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____7226
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____7247  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___179_7258  ->
      match uu___179_7258 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___180_7296 =
            match uu___180_7296 with
            | Rec_binding uu____7297 -> true
            | uu____7298 -> false in
          let this_env =
            let uu___193_7300 = env in
            let uu____7301 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___193_7300.curmodule);
              curmonad = (uu___193_7300.curmonad);
              modules = (uu___193_7300.modules);
              scope_mods = uu____7301;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___193_7300.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___193_7300.sigaccum);
              sigmap = (uu___193_7300.sigmap);
              iface = (uu___193_7300.iface);
              admitted_iface = (uu___193_7300.admitted_iface);
              expect_typ = (uu___193_7300.expect_typ);
              docs = (uu___193_7300.docs);
              remaining_iface_decls = (uu___193_7300.remaining_iface_decls);
              syntax_only = (uu___193_7300.syntax_only)
            } in
          let uu____7304 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____7304 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____7315 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___194_7332 = env in
      {
        curmodule = (uu___194_7332.curmodule);
        curmonad = (uu___194_7332.curmonad);
        modules = (uu___194_7332.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___194_7332.exported_ids);
        trans_exported_ids = (uu___194_7332.trans_exported_ids);
        includes = (uu___194_7332.includes);
        sigaccum = (uu___194_7332.sigaccum);
        sigmap = (uu___194_7332.sigmap);
        iface = (uu___194_7332.iface);
        admitted_iface = (uu___194_7332.admitted_iface);
        expect_typ = (uu___194_7332.expect_typ);
        docs = (uu___194_7332.docs);
        remaining_iface_decls = (uu___194_7332.remaining_iface_decls);
        syntax_only = (uu___194_7332.syntax_only)
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
        let uu____7387 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____7387
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          FStar_Exn.raise
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
          | FStar_Pervasives_Native.Some (se,uu____7414) ->
              let uu____7419 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____7419 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____7427 =
          let uu____7428 =
            let uu____7433 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____7433, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____7428 in
        FStar_Exn.raise uu____7427 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____7442 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____7451 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____7458 -> (true, true)
          | uu____7467 -> (false, false) in
        match uu____7442 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____7473 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____7479 =
                     let uu____7480 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____7480 in
                   if uu____7479
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____7473 with
             | FStar_Pervasives_Native.Some l when
                 let uu____7485 = FStar_Options.interactive () in
                 Prims.op_Negation uu____7485 -> err1 l
             | uu____7486 ->
                 (extract_record env globals s;
                  (let uu___195_7504 = env in
                   {
                     curmodule = (uu___195_7504.curmodule);
                     curmonad = (uu___195_7504.curmonad);
                     modules = (uu___195_7504.modules);
                     scope_mods = (uu___195_7504.scope_mods);
                     exported_ids = (uu___195_7504.exported_ids);
                     trans_exported_ids = (uu___195_7504.trans_exported_ids);
                     includes = (uu___195_7504.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___195_7504.sigmap);
                     iface = (uu___195_7504.iface);
                     admitted_iface = (uu___195_7504.admitted_iface);
                     expect_typ = (uu___195_7504.expect_typ);
                     docs = (uu___195_7504.docs);
                     remaining_iface_decls =
                       (uu___195_7504.remaining_iface_decls);
                     syntax_only = (uu___195_7504.syntax_only)
                   }))) in
      let env2 =
        let uu___196_7506 = env1 in
        let uu____7507 = FStar_ST.op_Bang globals in
        {
          curmodule = (uu___196_7506.curmodule);
          curmonad = (uu___196_7506.curmonad);
          modules = (uu___196_7506.modules);
          scope_mods = uu____7507;
          exported_ids = (uu___196_7506.exported_ids);
          trans_exported_ids = (uu___196_7506.trans_exported_ids);
          includes = (uu___196_7506.includes);
          sigaccum = (uu___196_7506.sigaccum);
          sigmap = (uu___196_7506.sigmap);
          iface = (uu___196_7506.iface);
          admitted_iface = (uu___196_7506.admitted_iface);
          expect_typ = (uu___196_7506.expect_typ);
          docs = (uu___196_7506.docs);
          remaining_iface_decls = (uu___196_7506.remaining_iface_decls);
          syntax_only = (uu___196_7506.syntax_only)
        } in
      let uu____7542 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7568) ->
            let uu____7577 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____7577)
        | uu____7604 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____7542 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____7663  ->
                   match uu____7663 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____7684 =
                                  let uu____7687 = FStar_ST.op_Bang globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____7687 in
                                FStar_ST.op_Colon_Equals globals uu____7684);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____7755 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____7755.FStar_Ident.str in
                                    ((let uu____7757 =
                                        get_exported_id_set env3 modul in
                                      match uu____7757 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____7783 =
                                            let uu____7784 =
                                              FStar_ST.op_Bang
                                                my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____7784 in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____7783
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
              let uu___197_7844 = env3 in
              let uu____7845 = FStar_ST.op_Bang globals in
              {
                curmodule = (uu___197_7844.curmodule);
                curmonad = (uu___197_7844.curmonad);
                modules = (uu___197_7844.modules);
                scope_mods = uu____7845;
                exported_ids = (uu___197_7844.exported_ids);
                trans_exported_ids = (uu___197_7844.trans_exported_ids);
                includes = (uu___197_7844.includes);
                sigaccum = (uu___197_7844.sigaccum);
                sigmap = (uu___197_7844.sigmap);
                iface = (uu___197_7844.iface);
                admitted_iface = (uu___197_7844.admitted_iface);
                expect_typ = (uu___197_7844.expect_typ);
                docs = (uu___197_7844.docs);
                remaining_iface_decls = (uu___197_7844.remaining_iface_decls);
                syntax_only = (uu___197_7844.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____7888 =
        let uu____7893 = resolve_module_name env ns false in
        match uu____7893 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____7907 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____7921  ->
                      match uu____7921 with
                      | (m,uu____7927) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____7907
            then (ns, Open_namespace)
            else
              (let uu____7933 =
                 let uu____7934 =
                   let uu____7939 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____7939, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____7934 in
               FStar_Exn.raise uu____7933)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____7888 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____7957 = resolve_module_name env ns false in
      match uu____7957 with
      | FStar_Pervasives_Native.Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____7964 = current_module env1 in
              uu____7964.FStar_Ident.str in
            (let uu____7966 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____7966 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____7990 =
                   let uu____7993 = FStar_ST.op_Bang incl in ns1 ::
                     uu____7993 in
                 FStar_ST.op_Colon_Equals incl uu____7990);
            (match () with
             | () ->
                 let uu____8060 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____8060 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____8077 =
                          let uu____8094 = get_exported_id_set env1 curmod in
                          let uu____8101 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____8094, uu____8101) in
                        match uu____8077 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____8155 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____8155 in
                              let ex = cur_exports k in
                              (let uu____8338 =
                                 let uu____8339 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____8339 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____8338);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____8401 =
                                     let uu____8402 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____8402 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____8401) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____8453 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____8474 =
                        let uu____8475 =
                          let uu____8480 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____8480, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____8475 in
                      FStar_Exn.raise uu____8474))))
      | uu____8481 ->
          let uu____8484 =
            let uu____8485 =
              let uu____8490 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____8490, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____8485 in
          FStar_Exn.raise uu____8484
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____8503 = module_is_defined env l in
        if uu____8503
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____8506 =
             let uu____8507 =
               let uu____8512 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____8512, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____8507 in
           FStar_Exn.raise uu____8506)
let push_doc:
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
            ((let uu____8531 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____8531 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____8535 =
                    let uu____8536 = FStar_Ident.string_of_lid l in
                    let uu____8537 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____8538 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____8536 uu____8537 uu____8538 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____8535);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____8555 = try_lookup_lid env l in
                (match uu____8555 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8567 =
                         let uu____8568 = FStar_Options.interactive () in
                         Prims.op_Negation uu____8568 in
                       if uu____8567
                       then
                         let uu____8569 =
                           let uu____8570 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format1
                             "Admitting %s without a definition" uu____8570 in
                         FStar_Errors.warn (FStar_Ident.range_of_lid l)
                           uu____8569
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___198_8580 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___198_8580.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___198_8580.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___198_8580.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___198_8580.FStar_Syntax_Syntax.sigattrs)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____8581 -> ())
            | uu____8590 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8609) ->
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
                                (lid,uu____8629,uu____8630,uu____8631,uu____8632,uu____8633)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____8642 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____8645,uu____8646) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____8652,lbs),uu____8654) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____8675 =
                               let uu____8676 =
                                 let uu____8677 =
                                   let uu____8680 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____8680.FStar_Syntax_Syntax.fv_name in
                                 uu____8677.FStar_Syntax_Syntax.v in
                               uu____8676.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____8675))
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
                               let uu____8694 =
                                 let uu____8697 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____8697.FStar_Syntax_Syntax.fv_name in
                               uu____8694.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___199_8702 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___199_8702.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___199_8702.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___199_8702.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____8712 -> ()));
      (let curmod =
         let uu____8714 = current_module env in uu____8714.FStar_Ident.str in
       (let uu____8716 =
          let uu____8733 = get_exported_id_set env curmod in
          let uu____8740 = get_trans_exported_id_set env curmod in
          (uu____8733, uu____8740) in
        match uu____8716 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____8794 = cur_ex eikind in FStar_ST.op_Bang uu____8794 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____8976 =
                let uu____8977 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____8977 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____8976 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____9028 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___200_9046 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___200_9046.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___200_9046.exported_ids);
                    trans_exported_ids = (uu___200_9046.trans_exported_ids);
                    includes = (uu___200_9046.includes);
                    sigaccum = [];
                    sigmap = (uu___200_9046.sigmap);
                    iface = (uu___200_9046.iface);
                    admitted_iface = (uu___200_9046.admitted_iface);
                    expect_typ = (uu___200_9046.expect_typ);
                    docs = (uu___200_9046.docs);
                    remaining_iface_decls =
                      (uu___200_9046.remaining_iface_decls);
                    syntax_only = (uu___200_9046.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____9070 =
       let uu____9073 = FStar_ST.op_Bang stack in env :: uu____9073 in
     FStar_ST.op_Colon_Equals stack uu____9070);
    (let uu___201_9112 = env in
     let uu____9113 = FStar_Util.smap_copy (sigmap env) in
     let uu____9124 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___201_9112.curmodule);
       curmonad = (uu___201_9112.curmonad);
       modules = (uu___201_9112.modules);
       scope_mods = (uu___201_9112.scope_mods);
       exported_ids = (uu___201_9112.exported_ids);
       trans_exported_ids = (uu___201_9112.trans_exported_ids);
       includes = (uu___201_9112.includes);
       sigaccum = (uu___201_9112.sigaccum);
       sigmap = uu____9113;
       iface = (uu___201_9112.iface);
       admitted_iface = (uu___201_9112.admitted_iface);
       expect_typ = (uu___201_9112.expect_typ);
       docs = uu____9124;
       remaining_iface_decls = (uu___201_9112.remaining_iface_decls);
       syntax_only = (uu___201_9112.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____9130  ->
    let uu____9131 = FStar_ST.op_Bang stack in
    match uu____9131 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9176 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____9184 = FStar_ST.op_Bang stack in
     match uu____9184 with
     | uu____9205::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
     | uu____9228 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____9238  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____9252 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____9255 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____9289 = FStar_Util.smap_try_find sm' k in
              match uu____9289 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___202_9314 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___202_9314.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___202_9314.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___202_9314.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___202_9314.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____9315 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____9320 -> ()));
      env1
let finish_module_or_interface: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
      then check_admits env
      else ();
      finish env modul
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list;
  exported_id_fields: Prims.string Prims.list;}[@@deriving show]
let __proj__Mkexported_ids__item__exported_id_terms:
  exported_ids -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_terms
let __proj__Mkexported_ids__item__exported_id_fields:
  exported_ids -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { exported_id_terms = __fname__exported_id_terms;
        exported_id_fields = __fname__exported_id_fields;_} ->
        __fname__exported_id_fields
let as_exported_ids: exported_id_set -> exported_ids =
  fun e  ->
    let terms =
      let uu____9405 =
        let uu____9408 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____9408 in
      FStar_Util.set_elements uu____9405 in
    let fields =
      let uu____9583 =
        let uu____9586 = e Exported_id_field in FStar_ST.op_Bang uu____9586 in
      FStar_Util.set_elements uu____9583 in
    { exported_id_terms = terms; exported_id_fields = fields }
let as_exported_id_set:
  exported_ids FStar_Pervasives_Native.option ->
    exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun e  ->
    match e with
    | FStar_Pervasives_Native.None  -> exported_id_set_new ()
    | FStar_Pervasives_Native.Some e1 ->
        let terms =
          let uu____9791 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____9791 in
        let fields =
          let uu____9801 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____9801 in
        (fun uu___181_9806  ->
           match uu___181_9806 with
           | Exported_id_term_type  -> terms
           | Exported_id_field  -> fields)
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option;}
[@@deriving show]
let __proj__Mkmodule_inclusion_info__item__mii_exported_ids:
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_exported_ids
let __proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids:
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} ->
        __fname__mii_trans_exported_ids
let __proj__Mkmodule_inclusion_info__item__mii_includes:
  module_inclusion_info ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids = __fname__mii_exported_ids;
        mii_trans_exported_ids = __fname__mii_trans_exported_ids;
        mii_includes = __fname__mii_includes;_} -> __fname__mii_includes
let default_mii: module_inclusion_info =
  {
    mii_exported_ids = FStar_Pervasives_Native.None;
    mii_trans_exported_ids = FStar_Pervasives_Native.None;
    mii_includes = FStar_Pervasives_Native.None
  }
let as_includes:
  'Auu____9919 .
    'Auu____9919 Prims.list FStar_Pervasives_Native.option ->
      'Auu____9919 Prims.list FStar_ST.ref
  =
  fun uu___182_9931  ->
    match uu___182_9931 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let inclusion_info: env -> FStar_Ident.lident -> module_inclusion_info =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____9966 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____9966 as_exported_ids in
      let uu____9969 = as_ids_opt env.exported_ids in
      let uu____9972 = as_ids_opt env.trans_exported_ids in
      let uu____9975 =
        let uu____9980 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____9980 (fun r  -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____9969;
        mii_trans_exported_ids = uu____9972;
        mii_includes = uu____9975
      }
let prepare_module_or_interface:
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
                FStar_Util.strcat (FStar_Ident.text_of_lid mname) ".fst" in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename in
              let auto_open1 =
                let convert_kind uu___183_10088 =
                  match uu___183_10088 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module in
                FStar_List.map
                  (fun uu____10100  ->
                     match uu____10100 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____10124 =
                    let uu____10129 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____10129, Open_namespace) in
                  [uu____10124]
                else [] in
              let auto_open2 =
                FStar_List.rev
                  (FStar_List.append auto_open1 namespace_of_module) in
              (let uu____10159 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____10159);
              (match () with
               | () ->
                   ((let uu____10175 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____10175);
                    (match () with
                     | () ->
                         ((let uu____10191 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____10191);
                          (match () with
                           | () ->
                               let uu___203_10214 = env1 in
                               let uu____10215 =
                                 FStar_List.map
                                   (fun x  -> Open_module_or_namespace x)
                                   auto_open2 in
                               {
                                 curmodule =
                                   (FStar_Pervasives_Native.Some mname);
                                 curmonad = (uu___203_10214.curmonad);
                                 modules = (uu___203_10214.modules);
                                 scope_mods = uu____10215;
                                 exported_ids = (uu___203_10214.exported_ids);
                                 trans_exported_ids =
                                   (uu___203_10214.trans_exported_ids);
                                 includes = (uu___203_10214.includes);
                                 sigaccum = (uu___203_10214.sigaccum);
                                 sigmap = (env1.sigmap);
                                 iface = intf;
                                 admitted_iface = admitted;
                                 expect_typ = (uu___203_10214.expect_typ);
                                 docs = (uu___203_10214.docs);
                                 remaining_iface_decls =
                                   (uu___203_10214.remaining_iface_decls);
                                 syntax_only = (uu___203_10214.syntax_only)
                               }))))) in
            let uu____10220 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____10246  ->
                      match uu____10246 with
                      | (l,uu____10252) -> FStar_Ident.lid_equals l mname)) in
            match uu____10220 with
            | FStar_Pervasives_Native.None  ->
                let uu____10261 = prep env in (uu____10261, false)
            | FStar_Pervasives_Native.Some (uu____10262,m) ->
                ((let uu____10269 =
                    (let uu____10272 = FStar_Options.interactive () in
                     Prims.op_Negation uu____10272) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____10269
                  then
                    let uu____10273 =
                      let uu____10274 =
                        let uu____10279 =
                          FStar_Util.format1
                            "Duplicate module or interface name: %s"
                            mname.FStar_Ident.str in
                        (uu____10279, (FStar_Ident.range_of_lid mname)) in
                      FStar_Errors.Error uu____10274 in
                    FStar_Exn.raise uu____10273
                  else ());
                 (let uu____10281 =
                    let uu____10282 = push env in prep uu____10282 in
                  (uu____10281, true)))
let enter_monad_scope: env -> FStar_Ident.ident -> env =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          FStar_Exn.raise
            (FStar_Errors.Error
               ((Prims.strcat "Trying to define monad "
                   (Prims.strcat mname.FStar_Ident.idText
                      (Prims.strcat ", but already in monad scope "
                         mname'.FStar_Ident.idText))),
                 (mname.FStar_Ident.idRange)))
      | FStar_Pervasives_Native.None  ->
          let uu___204_10292 = env in
          {
            curmodule = (uu___204_10292.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___204_10292.modules);
            scope_mods = (uu___204_10292.scope_mods);
            exported_ids = (uu___204_10292.exported_ids);
            trans_exported_ids = (uu___204_10292.trans_exported_ids);
            includes = (uu___204_10292.includes);
            sigaccum = (uu___204_10292.sigaccum);
            sigmap = (uu___204_10292.sigmap);
            iface = (uu___204_10292.iface);
            admitted_iface = (uu___204_10292.admitted_iface);
            expect_typ = (uu___204_10292.expect_typ);
            docs = (uu___204_10292.docs);
            remaining_iface_decls = (uu___204_10292.remaining_iface_decls);
            syntax_only = (uu___204_10292.syntax_only)
          }
let fail_or:
  'a .
    env ->
      (FStar_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStar_Ident.lident -> 'a
  =
  fun env  ->
    fun lookup  ->
      fun lid  ->
        let uu____10323 = lookup lid in
        match uu____10323 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____10336  ->
                   match uu____10336 with
                   | (lid1,uu____10342) -> FStar_Ident.text_of_lid lid1)
                env.modules in
            let msg =
              FStar_Util.format1 "Identifier not found: [%s]"
                (FStar_Ident.text_of_lid lid) in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____10347 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   FStar_Ident.set_lid_range uu____10347
                     (FStar_Ident.range_of_lid lid) in
                 let uu____10348 = resolve_module_name env modul true in
                 match uu____10348 with
                 | FStar_Pervasives_Native.None  ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
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
                       FStar_String.concat ", " opened_modules in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       opened_modules1
                 | FStar_Pervasives_Native.Some modul' ->
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, definition %s not found"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       (lid.FStar_Ident.ident).FStar_Ident.idText) in
            FStar_Exn.raise
              (FStar_Errors.Error (msg1, (FStar_Ident.range_of_lid lid)))
        | FStar_Pervasives_Native.Some r -> r
let fail_or2:
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup  ->
    fun id1  ->
      let uu____10382 = lookup id1 in
      match uu____10382 with
      | FStar_Pervasives_Native.None  ->
          FStar_Exn.raise
            (FStar_Errors.Error
               ((Prims.strcat "Identifier not found ["
                   (Prims.strcat id1.FStar_Ident.idText "]")),
                 (id1.FStar_Ident.idRange)))
      | FStar_Pervasives_Native.Some r -> r