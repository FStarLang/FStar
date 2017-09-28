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
      let uu___182_1426 = env in
      {
        curmodule = (uu___182_1426.curmodule);
        curmonad = (uu___182_1426.curmonad);
        modules = (uu___182_1426.modules);
        scope_mods = (uu___182_1426.scope_mods);
        exported_ids = (uu___182_1426.exported_ids);
        trans_exported_ids = (uu___182_1426.trans_exported_ids);
        includes = (uu___182_1426.includes);
        sigaccum = (uu___182_1426.sigaccum);
        sigmap = (uu___182_1426.sigmap);
        iface = b;
        admitted_iface = (uu___182_1426.admitted_iface);
        expect_typ = (uu___182_1426.expect_typ);
        docs = (uu___182_1426.docs);
        remaining_iface_decls = (uu___182_1426.remaining_iface_decls);
        syntax_only = (uu___182_1426.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___183_1439 = e in
      {
        curmodule = (uu___183_1439.curmodule);
        curmonad = (uu___183_1439.curmonad);
        modules = (uu___183_1439.modules);
        scope_mods = (uu___183_1439.scope_mods);
        exported_ids = (uu___183_1439.exported_ids);
        trans_exported_ids = (uu___183_1439.trans_exported_ids);
        includes = (uu___183_1439.includes);
        sigaccum = (uu___183_1439.sigaccum);
        sigmap = (uu___183_1439.sigmap);
        iface = (uu___183_1439.iface);
        admitted_iface = b;
        expect_typ = (uu___183_1439.expect_typ);
        docs = (uu___183_1439.docs);
        remaining_iface_decls = (uu___183_1439.remaining_iface_decls);
        syntax_only = (uu___183_1439.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___184_1452 = e in
      {
        curmodule = (uu___184_1452.curmodule);
        curmonad = (uu___184_1452.curmonad);
        modules = (uu___184_1452.modules);
        scope_mods = (uu___184_1452.scope_mods);
        exported_ids = (uu___184_1452.exported_ids);
        trans_exported_ids = (uu___184_1452.trans_exported_ids);
        includes = (uu___184_1452.includes);
        sigaccum = (uu___184_1452.sigaccum);
        sigmap = (uu___184_1452.sigmap);
        iface = (uu___184_1452.iface);
        admitted_iface = (uu___184_1452.admitted_iface);
        expect_typ = b;
        docs = (uu___184_1452.docs);
        remaining_iface_decls = (uu___184_1452.remaining_iface_decls);
        syntax_only = (uu___184_1452.syntax_only)
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
      let uu___185_1741 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___185_1741.curmonad);
        modules = (uu___185_1741.modules);
        scope_mods = (uu___185_1741.scope_mods);
        exported_ids = (uu___185_1741.exported_ids);
        trans_exported_ids = (uu___185_1741.trans_exported_ids);
        includes = (uu___185_1741.includes);
        sigaccum = (uu___185_1741.sigaccum);
        sigmap = (uu___185_1741.sigmap);
        iface = (uu___185_1741.iface);
        admitted_iface = (uu___185_1741.admitted_iface);
        expect_typ = (uu___185_1741.expect_typ);
        docs = (uu___185_1741.docs);
        remaining_iface_decls = (uu___185_1741.remaining_iface_decls);
        syntax_only = (uu___185_1741.syntax_only)
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
      let uu____1759 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____1793  ->
                match uu____1793 with
                | (m,uu____1801) -> FStar_Ident.lid_equals l m)) in
      match uu____1759 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____1818,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____1848 =
          FStar_List.partition
            (fun uu____1878  ->
               match uu____1878 with
               | (m,uu____1886) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____1848 with
        | (uu____1891,rest) ->
            let uu___186_1925 = env in
            {
              curmodule = (uu___186_1925.curmodule);
              curmonad = (uu___186_1925.curmonad);
              modules = (uu___186_1925.modules);
              scope_mods = (uu___186_1925.scope_mods);
              exported_ids = (uu___186_1925.exported_ids);
              trans_exported_ids = (uu___186_1925.trans_exported_ids);
              includes = (uu___186_1925.includes);
              sigaccum = (uu___186_1925.sigaccum);
              sigmap = (uu___186_1925.sigmap);
              iface = (uu___186_1925.iface);
              admitted_iface = (uu___186_1925.admitted_iface);
              expect_typ = (uu___186_1925.expect_typ);
              docs = (uu___186_1925.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___186_1925.syntax_only)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____1948 = current_module env in qual uu____1948 id
      | FStar_Pervasives_Native.Some monad ->
          let uu____1950 =
            let uu____1951 = current_module env in qual uu____1951 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____1950 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___187_1964 = env in
      {
        curmodule = (uu___187_1964.curmodule);
        curmonad = (uu___187_1964.curmonad);
        modules = (uu___187_1964.modules);
        scope_mods = (uu___187_1964.scope_mods);
        exported_ids = (uu___187_1964.exported_ids);
        trans_exported_ids = (uu___187_1964.trans_exported_ids);
        includes = (uu___187_1964.includes);
        sigaccum = (uu___187_1964.sigaccum);
        sigmap = (uu___187_1964.sigmap);
        iface = (uu___187_1964.iface);
        admitted_iface = (uu___187_1964.admitted_iface);
        expect_typ = (uu___187_1964.expect_typ);
        docs = (uu___187_1964.docs);
        remaining_iface_decls = (uu___187_1964.remaining_iface_decls);
        syntax_only = b
      }
let new_sigmap: 'Auu____1969 . Prims.unit -> 'Auu____1969 FStar_Util.smap =
  fun uu____1975  -> FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____1979  ->
    let uu____1980 = new_sigmap () in
    let uu____1983 = new_sigmap () in
    let uu____1986 = new_sigmap () in
    let uu____1997 = new_sigmap () in
    let uu____2008 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____1980;
      trans_exported_ids = uu____1983;
      includes = uu____1986;
      sigaccum = [];
      sigmap = uu____1997;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2008;
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
      (fun uu____2042  ->
         match uu____2042 with
         | (m,uu____2048) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___188_2058 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___188_2058.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___189_2059 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___189_2059.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___189_2059.FStar_Syntax_Syntax.sort)
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
        (fun uu____2149  ->
           match uu____2149 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____2172 =
                   let uu____2173 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____2173 dd dq in
                 FStar_Pervasives_Native.Some uu____2172
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
    match projectee with | Cont_ok _0 -> true | uu____2218 -> false
let __proj__Cont_ok__item___0: 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2251 -> false
let uu___is_Cont_ignore: 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2267 -> false
let option_of_cont:
  'a .
    (Prims.unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___152_2293  ->
      match uu___152_2293 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
let find_in_record:
  'Auu____2311 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2311 cont_t) -> 'Auu____2311 cont_t
  =
  fun ns  ->
    fun id  ->
      fun record  ->
        fun cont  ->
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
                (fun uu____2357  ->
                   match uu____2357 with
                   | (f,uu____2365) ->
                       if id.FStar_Ident.idText = f.FStar_Ident.idText
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
  fun uu___153_2416  ->
    match uu___153_2416 with
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
            fun id  ->
              let idstr = id.FStar_Ident.idText in
              let rec aux uu___154_2479 =
                match uu___154_2479 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str in
                    let not_shadowed =
                      let uu____2490 = get_exported_id_set env mname in
                      match uu____2490 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2511 = mex eikind in
                            FStar_ST.op_Bang uu____2511 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____2758 =
                        FStar_Util.smap_try_find env.includes mname in
                      match uu____2758 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____2853 = qual modul id in
                        find_in_module uu____2853
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____2857 -> look_into) in
              aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___155_2863  ->
    match uu___155_2863 with
    | Exported_id_field  -> true
    | uu____2864 -> false
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
    fun id  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun find_in_module  ->
                fun lookup_default_id  ->
                  let check_local_binding_id uu___156_2975 =
                    match uu___156_2975 with
                    | (id',uu____2977,uu____2978) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText in
                  let check_rec_binding_id uu___157_2982 =
                    match uu___157_2982 with
                    | (id',uu____2984,uu____2985) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText in
                  let curmod_ns =
                    let uu____2989 = current_module env in
                    FStar_Ident.ids_of_lid uu____2989 in
                  let proc uu___158_2995 =
                    match uu___158_2995 with
                    | Local_binding l when check_local_binding_id l ->
                        k_local_binding l
                    | Rec_binding r when check_rec_binding_id r ->
                        k_rec_binding r
                    | Open_module_or_namespace (ns,Open_module ) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env ns id
                    | Top_level_def id' when
                        id'.FStar_Ident.idText = id.FStar_Ident.idText ->
                        lookup_default_id Cont_ignore id
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____3003 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id1 = lid.FStar_Ident.ident in
                             find_in_record lid.FStar_Ident.ns id1 r k_record)
                          Cont_ignore env uu____3003 id
                    | uu____3008 -> Cont_ignore in
                  let rec aux uu___159_3016 =
                    match uu___159_3016 with
                    | a::q ->
                        let uu____3025 = proc a in
                        option_of_cont (fun uu____3029  -> aux q) uu____3025
                    | [] ->
                        let uu____3030 = lookup_default_id Cont_fail id in
                        option_of_cont
                          (fun uu____3034  -> FStar_Pervasives_Native.None)
                          uu____3030 in
                  aux env.scope_mods
let found_local_binding:
  'Auu____3043 'Auu____3044 .
    FStar_Range.range ->
      ('Auu____3044,FStar_Syntax_Syntax.bv,'Auu____3043)
        FStar_Pervasives_Native.tuple3 ->
        (FStar_Syntax_Syntax.term,'Auu____3043)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun uu____3062  ->
      match uu____3062 with
      | (id',x,mut) -> let uu____3072 = bv_to_name x r in (uu____3072, mut)
let find_in_module:
  'Auu____3083 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt,Prims.bool)
             FStar_Pervasives_Native.tuple2 -> 'Auu____3083)
          -> 'Auu____3083 -> 'Auu____3083
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3118 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
          match uu____3118 with
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
      let uu____3156 = unmangleOpName id in
      match uu____3156 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3182 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____3196 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____3196) (fun uu____3206  -> Cont_fail)
            (fun uu____3212  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3227  -> fun uu____3228  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3243  -> fun uu____3244  -> Cont_fail)
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
    fun id  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let find_in_monad =
            match env.curmonad with
            | FStar_Pervasives_Native.Some uu____3319 ->
                let lid = qualify env id in
                let uu____3321 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
                (match uu____3321 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3345 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3345
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3368 = current_module env in qual uu____3368 id in
              find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____3380 = current_module env in
           FStar_Ident.lid_equals lid uu____3380)
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
        let rec aux uu___160_3415 =
          match uu___160_3415 with
          | [] ->
              let uu____3420 = module_is_defined env lid in
              if uu____3420
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3429 =
                  let uu____3432 = FStar_Ident.path_of_lid ns in
                  let uu____3435 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3432 uu____3435 in
                FStar_Ident.lid_of_path uu____3429
                  (FStar_Ident.range_of_lid lid) in
              let uu____3438 = module_is_defined env new_lid in
              if uu____3438
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3444 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3451::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3467 =
          let uu____3468 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____3468 in
        if uu____3467
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____3470 =
                let uu____3471 =
                  let uu____3476 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____3476, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____3471 in
              FStar_Exn.raise uu____3470))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____3486 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____3490 = resolve_module_name env modul_orig true in
          (match uu____3490 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____3494 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___161_3507  ->
           match uu___161_3507 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____3509 -> false) env.scope_mods
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
                 let uu____3601 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3601
                   (FStar_Util.map_option
                      (fun uu____3651  ->
                         match uu____3651 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____3682 =
          is_full_path &&
            (let uu____3684 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____3684) in
        if uu____3682
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____3714 = aux ns_rev_prefix ns_last_id in
               (match uu____3714 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____3775 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____3775 with
      | (uu____3784,short) ->
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
                  | uu____3901::uu____3902 ->
                      let uu____3905 =
                        let uu____3908 =
                          let uu____3909 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                          FStar_Ident.set_lid_range uu____3909
                            (FStar_Ident.range_of_lid lid) in
                        resolve_module_name env uu____3908 true in
                      (match uu____3905 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____3913 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident in
                           option_of_cont
                             (fun uu____3917  -> FStar_Pervasives_Native.None)
                             uu____3913)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
let cont_of_option:
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___162_3938  ->
      match uu___162_3938 with
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
              let uu____4043 = k_global_def lid1 def in
              cont_of_option k uu____4043 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env i (k_global_def' k) k in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4073 = k_local_binding l in
                 cont_of_option Cont_fail uu____4073)
              (fun r  ->
                 let uu____4079 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4079)
              (fun uu____4083  -> Cont_ignore) f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4092,uu____4093,uu____4094,l,uu____4096,uu____4097) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___163_4108  ->
               match uu___163_4108 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4111,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4123 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4129,uu____4130,uu____4131)
        -> FStar_Pervasives_Native.None
    | uu____4132 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____4145 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4153 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4153
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4145 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____4168 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____4168 ns)
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
          let k_global_def source_lid uu___167_4202 =
            match uu___167_4202 with
            | (uu____4209,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4211) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4214 ->
                     let uu____4231 =
                       let uu____4232 =
                         let uu____4237 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4237, false) in
                       Term_name uu____4232 in
                     FStar_Pervasives_Native.Some uu____4231
                 | FStar_Syntax_Syntax.Sig_datacon uu____4238 ->
                     let uu____4253 =
                       let uu____4254 =
                         let uu____4259 =
                           let uu____4260 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____4260 in
                         (uu____4259, false) in
                       Term_name uu____4254 in
                     FStar_Pervasives_Native.Some uu____4253
                 | FStar_Syntax_Syntax.Sig_let ((uu____4263,lbs),uu____4265)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4281 =
                       let uu____4282 =
                         let uu____4287 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4287, false) in
                       Term_name uu____4282 in
                     FStar_Pervasives_Native.Some uu____4281
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4289,uu____4290) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4294 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___164_4298  ->
                                  match uu___164_4298 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____4299 -> false))) in
                     if uu____4294
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____4304 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___165_4309  ->
                                      match uu___165_4309 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____4310 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____4315 -> true
                                      | uu____4316 -> false))) in
                         if uu____4304
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____4318 =
                         FStar_Util.find_map quals
                           (fun uu___166_4323  ->
                              match uu___166_4323 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4327 -> FStar_Pervasives_Native.None) in
                       (match uu____4318 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____4336 ->
                            let uu____4339 =
                              let uu____4340 =
                                let uu____4345 =
                                  let uu____4346 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____4346 in
                                (uu____4345, false) in
                              Term_name uu____4340 in
                            FStar_Pervasives_Native.Some uu____4339)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4352 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____4365 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____4384 =
              let uu____4385 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____4385 in
            FStar_Pervasives_Native.Some uu____4384 in
          let k_rec_binding uu____4401 =
            match uu____4401 with
            | (id,l,dd) ->
                let uu____4413 =
                  let uu____4414 =
                    let uu____4419 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____4419, false) in
                  Term_name uu____4414 in
                FStar_Pervasives_Native.Some uu____4413 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____4425 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____4425 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____4443 -> FStar_Pervasives_Native.None)
            | uu____4450 -> FStar_Pervasives_Native.None in
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
        let uu____4482 = try_lookup_name true exclude_interf env lid in
        match uu____4482 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4497 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4514 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4514 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4529 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4552 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4552 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4568;
             FStar_Syntax_Syntax.sigquals = uu____4569;
             FStar_Syntax_Syntax.sigmeta = uu____4570;
             FStar_Syntax_Syntax.sigattrs = uu____4571;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4590;
             FStar_Syntax_Syntax.sigquals = uu____4591;
             FStar_Syntax_Syntax.sigmeta = uu____4592;
             FStar_Syntax_Syntax.sigattrs = uu____4593;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4611,uu____4612,uu____4613,uu____4614,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4616;
             FStar_Syntax_Syntax.sigquals = uu____4617;
             FStar_Syntax_Syntax.sigmeta = uu____4618;
             FStar_Syntax_Syntax.sigattrs = uu____4619;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4641 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4664 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4664 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4674;
             FStar_Syntax_Syntax.sigquals = uu____4675;
             FStar_Syntax_Syntax.sigmeta = uu____4676;
             FStar_Syntax_Syntax.sigattrs = uu____4677;_},uu____4678)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____4688;
             FStar_Syntax_Syntax.sigquals = uu____4689;
             FStar_Syntax_Syntax.sigmeta = uu____4690;
             FStar_Syntax_Syntax.sigattrs = uu____4691;_},uu____4692)
          -> FStar_Pervasives_Native.Some ne
      | uu____4701 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4716 = try_lookup_effect_name env lid in
      match uu____4716 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____4719 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4730 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____4730 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____4740,uu____4741,uu____4742,uu____4743);
             FStar_Syntax_Syntax.sigrng = uu____4744;
             FStar_Syntax_Syntax.sigquals = uu____4745;
             FStar_Syntax_Syntax.sigmeta = uu____4746;
             FStar_Syntax_Syntax.sigattrs = uu____4747;_},uu____4748)
          ->
          let rec aux new_name =
            let uu____4767 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____4767 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____4785) ->
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
                     (uu____4794,uu____4795,uu____4796,cmp,uu____4798) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____4804 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4805,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4811 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___168_4842 =
        match uu___168_4842 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____4851,uu____4852,uu____4853);
             FStar_Syntax_Syntax.sigrng = uu____4854;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____4856;
             FStar_Syntax_Syntax.sigattrs = uu____4857;_},uu____4858)
            -> FStar_Pervasives_Native.Some quals
        | uu____4865 -> FStar_Pervasives_Native.None in
      let uu____4872 =
        resolve_in_open_namespaces' env lid
          (fun uu____4880  -> FStar_Pervasives_Native.None)
          (fun uu____4884  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____4872 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____4894 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____4913 =
        FStar_List.tryFind
          (fun uu____4928  ->
             match uu____4928 with
             | (mlid,modul) ->
                 let uu____4935 = FStar_Ident.path_of_lid mlid in
                 uu____4935 = path) env.modules in
      match uu____4913 with
      | FStar_Pervasives_Native.Some (uu____4942,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___169_4974 =
        match uu___169_4974 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____4981,lbs),uu____4983);
             FStar_Syntax_Syntax.sigrng = uu____4984;
             FStar_Syntax_Syntax.sigquals = uu____4985;
             FStar_Syntax_Syntax.sigmeta = uu____4986;
             FStar_Syntax_Syntax.sigattrs = uu____4987;_},uu____4988)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____5008 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____5008
        | uu____5009 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5015  -> FStar_Pervasives_Native.None)
        (fun uu____5017  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___170_5042 =
        match uu___170_5042 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____5052);
             FStar_Syntax_Syntax.sigrng = uu____5053;
             FStar_Syntax_Syntax.sigquals = uu____5054;
             FStar_Syntax_Syntax.sigmeta = uu____5055;
             FStar_Syntax_Syntax.sigattrs = uu____5056;_},uu____5057)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5080 -> FStar_Pervasives_Native.None)
        | uu____5087 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5097  -> FStar_Pervasives_Native.None)
        (fun uu____5101  -> FStar_Pervasives_Native.None) k_global_def
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
          let uu____5144 = try_lookup_name any_val exclude_interf env lid in
          match uu____5144 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____5159 -> FStar_Pervasives_Native.None
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
      let uu____5190 = try_lookup_lid env l in
      match uu____5190 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____5204) ->
          let uu____5209 =
            let uu____5210 = FStar_Syntax_Subst.compress e in
            uu____5210.FStar_Syntax_Syntax.n in
          (match uu____5209 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5216 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___190_5232 = env in
        {
          curmodule = (uu___190_5232.curmodule);
          curmonad = (uu___190_5232.curmonad);
          modules = (uu___190_5232.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___190_5232.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___190_5232.sigaccum);
          sigmap = (uu___190_5232.sigmap);
          iface = (uu___190_5232.iface);
          admitted_iface = (uu___190_5232.admitted_iface);
          expect_typ = (uu___190_5232.expect_typ);
          docs = (uu___190_5232.docs);
          remaining_iface_decls = (uu___190_5232.remaining_iface_decls);
          syntax_only = (uu___190_5232.syntax_only)
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
      let k_global_def lid1 uu___172_5265 =
        match uu___172_5265 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5272,uu____5273,uu____5274);
             FStar_Syntax_Syntax.sigrng = uu____5275;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5277;
             FStar_Syntax_Syntax.sigattrs = uu____5278;_},uu____5279)
            ->
            let uu____5284 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___171_5288  ->
                      match uu___171_5288 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____5289 -> false)) in
            if uu____5284
            then
              let uu____5292 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____5292
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5294;
             FStar_Syntax_Syntax.sigrng = uu____5295;
             FStar_Syntax_Syntax.sigquals = uu____5296;
             FStar_Syntax_Syntax.sigmeta = uu____5297;
             FStar_Syntax_Syntax.sigattrs = uu____5298;_},uu____5299)
            ->
            let uu____5318 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____5318
        | uu____5319 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5325  -> FStar_Pervasives_Native.None)
        (fun uu____5327  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___173_5354 =
        match uu___173_5354 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5363,uu____5364,uu____5365,uu____5366,datas,uu____5368);
             FStar_Syntax_Syntax.sigrng = uu____5369;
             FStar_Syntax_Syntax.sigquals = uu____5370;
             FStar_Syntax_Syntax.sigmeta = uu____5371;
             FStar_Syntax_Syntax.sigattrs = uu____5372;_},uu____5373)
            -> FStar_Pervasives_Native.Some datas
        | uu____5388 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____5398  -> FStar_Pervasives_Native.None)
        (fun uu____5402  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit) FStar_Pervasives_Native.tuple4,Prims.unit ->
                                                                  Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____5447 =
    let uu____5448 =
      let uu____5453 =
        let uu____5456 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____5456 in
      let uu____5531 = FStar_ST.op_Bang record_cache in uu____5453 ::
        uu____5531 in
    FStar_ST.op_Colon_Equals record_cache uu____5448 in
  let pop1 uu____5677 =
    let uu____5678 =
      let uu____5683 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____5683 in
    FStar_ST.op_Colon_Equals record_cache uu____5678 in
  let peek1 uu____5831 =
    let uu____5832 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____5832 in
  let insert r =
    let uu____5911 =
      let uu____5916 = let uu____5919 = peek1 () in r :: uu____5919 in
      let uu____5922 =
        let uu____5927 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____5927 in
      uu____5916 :: uu____5922 in
    FStar_ST.op_Colon_Equals record_cache uu____5911 in
  let filter1 uu____6075 =
    let rc = peek1 () in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
    let uu____6084 =
      let uu____6089 =
        let uu____6094 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6094 in
      filtered :: uu____6089 in
    FStar_ST.op_Colon_Equals record_cache uu____6084 in
  let aux = (push1, pop1, peek1, insert) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit)
    FStar_Pervasives_Native.tuple4
  =
  let uu____6306 = record_cache_aux_with_filter in
  match uu____6306 with | (aux,uu____6350) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____6394 = record_cache_aux_with_filter in
  match uu____6394 with | (uu____6421,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____6466 = record_cache_aux in
  match uu____6466 with | (push1,uu____6488,uu____6489,uu____6490) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____6514 = record_cache_aux in
  match uu____6514 with | (uu____6535,pop1,uu____6537,uu____6538) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____6564 = record_cache_aux in
  match uu____6564 with | (uu____6587,uu____6588,peek1,uu____6590) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____6614 = record_cache_aux in
  match uu____6614 with | (uu____6635,uu____6636,uu____6637,insert) -> insert
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____6694) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___174_6710  ->
                   match uu___174_6710 with
                   | FStar_Syntax_Syntax.RecordType uu____6711 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____6720 -> true
                   | uu____6729 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___175_6751  ->
                      match uu___175_6751 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____6753,uu____6754,uu____6755,uu____6756,uu____6757);
                          FStar_Syntax_Syntax.sigrng = uu____6758;
                          FStar_Syntax_Syntax.sigquals = uu____6759;
                          FStar_Syntax_Syntax.sigmeta = uu____6760;
                          FStar_Syntax_Syntax.sigattrs = uu____6761;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____6770 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___176_6805  ->
                    match uu___176_6805 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____6809,uu____6810,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____6812;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____6814;
                        FStar_Syntax_Syntax.sigattrs = uu____6815;_} ->
                        let uu____6826 =
                          let uu____6827 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____6827 in
                        (match uu____6826 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____6833,t,uu____6835,uu____6836,uu____6837);
                             FStar_Syntax_Syntax.sigrng = uu____6838;
                             FStar_Syntax_Syntax.sigquals = uu____6839;
                             FStar_Syntax_Syntax.sigmeta = uu____6840;
                             FStar_Syntax_Syntax.sigattrs = uu____6841;_} ->
                             let uu____6850 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____6850 with
                              | (formals,uu____6864) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____6913  ->
                                            match uu____6913 with
                                            | (x,q) ->
                                                let uu____6926 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____6926
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____6983  ->
                                            match uu____6983 with
                                            | (x,q) ->
                                                let uu____6996 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____6996,
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
                                  ((let uu____7011 =
                                      let uu____7014 =
                                        FStar_ST.op_Bang new_globs in
                                      (Record_or_dc record) :: uu____7014 in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____7011);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____7155 =
                                            match uu____7155 with
                                            | (id,uu____7163) ->
                                                let modul =
                                                  let uu____7169 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____7169.FStar_Ident.str in
                                                let uu____7170 =
                                                  get_exported_id_set e modul in
                                                (match uu____7170 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____7197 =
                                                         let uu____7198 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____7198 in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____7197);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____7322 =
                                                               let uu____7323
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____7323.FStar_Ident.ident in
                                                             uu____7322.FStar_Ident.idText in
                                                           let uu____7325 =
                                                             let uu____7326 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____7326 in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____7325))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____7459 -> ())
                    | uu____7460 -> ()))
        | uu____7461 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____7478 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____7478 with
        | (ns,id) ->
            let uu____7495 = peek_record_cache () in
            FStar_Util.find_map uu____7495
              (fun record  ->
                 let uu____7501 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____7507  -> FStar_Pervasives_Native.None)
                   uu____7501) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____7509  -> Cont_ignore) (fun uu____7511  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____7517 = find_in_cache fn in
           cont_of_option Cont_ignore uu____7517)
        (fun k  -> fun uu____7523  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____7536 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7536 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7542 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____7557 = try_lookup_record_by_field_name env lid in
        match uu____7557 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7561 =
              let uu____7562 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7562 in
            let uu____7565 =
              let uu____7566 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____7566 in
            uu____7561 = uu____7565 ->
            let uu____7569 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____7573  -> Cont_ok ()) in
            (match uu____7569 with
             | Cont_ok uu____7574 -> true
             | uu____7575 -> false)
        | uu____7578 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____7595 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____7595 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7605 =
            let uu____7610 =
              let uu____7611 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____7611
                (FStar_Ident.range_of_lid fieldname) in
            (uu____7610, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____7605
      | uu____7616 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____7637  ->
    let uu____7638 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____7638
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____7659  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___177_7670  ->
      match uu___177_7670 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___178_7708 =
            match uu___178_7708 with
            | Rec_binding uu____7709 -> true
            | uu____7710 -> false in
          let this_env =
            let uu___191_7712 = env in
            let uu____7713 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___191_7712.curmodule);
              curmonad = (uu___191_7712.curmonad);
              modules = (uu___191_7712.modules);
              scope_mods = uu____7713;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___191_7712.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___191_7712.sigaccum);
              sigmap = (uu___191_7712.sigmap);
              iface = (uu___191_7712.iface);
              admitted_iface = (uu___191_7712.admitted_iface);
              expect_typ = (uu___191_7712.expect_typ);
              docs = (uu___191_7712.docs);
              remaining_iface_decls = (uu___191_7712.remaining_iface_decls);
              syntax_only = (uu___191_7712.syntax_only)
            } in
          let uu____7716 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____7716 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____7727 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___192_7744 = env in
      {
        curmodule = (uu___192_7744.curmodule);
        curmonad = (uu___192_7744.curmonad);
        modules = (uu___192_7744.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___192_7744.exported_ids);
        trans_exported_ids = (uu___192_7744.trans_exported_ids);
        includes = (uu___192_7744.includes);
        sigaccum = (uu___192_7744.sigaccum);
        sigmap = (uu___192_7744.sigmap);
        iface = (uu___192_7744.iface);
        admitted_iface = (uu___192_7744.admitted_iface);
        expect_typ = (uu___192_7744.expect_typ);
        docs = (uu___192_7744.docs);
        remaining_iface_decls = (uu___192_7744.remaining_iface_decls);
        syntax_only = (uu___192_7744.syntax_only)
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
        let uu____7799 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____7799
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
          | FStar_Pervasives_Native.Some (se,uu____7826) ->
              let uu____7831 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____7831 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____7839 =
          let uu____7840 =
            let uu____7845 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____7845, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____7840 in
        FStar_Exn.raise uu____7839 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____7854 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____7863 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____7870 -> (true, true)
          | uu____7879 -> (false, false) in
        match uu____7854 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____7885 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____7891 =
                     let uu____7892 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____7892 in
                   if uu____7891
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____7885 with
             | FStar_Pervasives_Native.Some l when
                 let uu____7897 = FStar_Options.interactive () in
                 Prims.op_Negation uu____7897 -> err1 l
             | uu____7898 ->
                 (extract_record env globals s;
                  (let uu___193_7916 = env in
                   {
                     curmodule = (uu___193_7916.curmodule);
                     curmonad = (uu___193_7916.curmonad);
                     modules = (uu___193_7916.modules);
                     scope_mods = (uu___193_7916.scope_mods);
                     exported_ids = (uu___193_7916.exported_ids);
                     trans_exported_ids = (uu___193_7916.trans_exported_ids);
                     includes = (uu___193_7916.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___193_7916.sigmap);
                     iface = (uu___193_7916.iface);
                     admitted_iface = (uu___193_7916.admitted_iface);
                     expect_typ = (uu___193_7916.expect_typ);
                     docs = (uu___193_7916.docs);
                     remaining_iface_decls =
                       (uu___193_7916.remaining_iface_decls);
                     syntax_only = (uu___193_7916.syntax_only)
                   }))) in
      let env2 =
        let uu___194_7918 = env1 in
        let uu____7919 = FStar_ST.op_Bang globals in
        {
          curmodule = (uu___194_7918.curmodule);
          curmonad = (uu___194_7918.curmonad);
          modules = (uu___194_7918.modules);
          scope_mods = uu____7919;
          exported_ids = (uu___194_7918.exported_ids);
          trans_exported_ids = (uu___194_7918.trans_exported_ids);
          includes = (uu___194_7918.includes);
          sigaccum = (uu___194_7918.sigaccum);
          sigmap = (uu___194_7918.sigmap);
          iface = (uu___194_7918.iface);
          admitted_iface = (uu___194_7918.admitted_iface);
          expect_typ = (uu___194_7918.expect_typ);
          docs = (uu___194_7918.docs);
          remaining_iface_decls = (uu___194_7918.remaining_iface_decls);
          syntax_only = (uu___194_7918.syntax_only)
        } in
      let uu____7986 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8012) ->
            let uu____8021 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____8021)
        | uu____8048 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____7986 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____8107  ->
                   match uu____8107 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____8128 =
                                  let uu____8131 = FStar_ST.op_Bang globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____8131 in
                                FStar_ST.op_Colon_Equals globals uu____8128);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____8263 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____8263.FStar_Ident.str in
                                    ((let uu____8265 =
                                        get_exported_id_set env3 modul in
                                      match uu____8265 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____8291 =
                                            let uu____8292 =
                                              FStar_ST.op_Bang
                                                my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____8292 in
                                          FStar_ST.op_Colon_Equals
                                            my_exported_ids uu____8291
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
              let uu___195_8424 = env3 in
              let uu____8425 = FStar_ST.op_Bang globals in
              {
                curmodule = (uu___195_8424.curmodule);
                curmonad = (uu___195_8424.curmonad);
                modules = (uu___195_8424.modules);
                scope_mods = uu____8425;
                exported_ids = (uu___195_8424.exported_ids);
                trans_exported_ids = (uu___195_8424.trans_exported_ids);
                includes = (uu___195_8424.includes);
                sigaccum = (uu___195_8424.sigaccum);
                sigmap = (uu___195_8424.sigmap);
                iface = (uu___195_8424.iface);
                admitted_iface = (uu___195_8424.admitted_iface);
                expect_typ = (uu___195_8424.expect_typ);
                docs = (uu___195_8424.docs);
                remaining_iface_decls = (uu___195_8424.remaining_iface_decls);
                syntax_only = (uu___195_8424.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____8500 =
        let uu____8505 = resolve_module_name env ns false in
        match uu____8505 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____8519 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____8533  ->
                      match uu____8533 with
                      | (m,uu____8539) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____8519
            then (ns, Open_namespace)
            else
              (let uu____8545 =
                 let uu____8546 =
                   let uu____8551 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____8551, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____8546 in
               FStar_Exn.raise uu____8545)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____8500 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____8569 = resolve_module_name env ns false in
      match uu____8569 with
      | FStar_Pervasives_Native.Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____8576 = current_module env1 in
              uu____8576.FStar_Ident.str in
            (let uu____8578 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____8578 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____8602 =
                   let uu____8605 = FStar_ST.op_Bang incl in ns1 ::
                     uu____8605 in
                 FStar_ST.op_Colon_Equals incl uu____8602);
            (match () with
             | () ->
                 let uu____8736 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____8736 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____8753 =
                          let uu____8770 = get_exported_id_set env1 curmod in
                          let uu____8777 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____8770, uu____8777) in
                        match uu____8753 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____8831 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____8831 in
                              let ex = cur_exports k in
                              (let uu____9086 =
                                 let uu____9087 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____9087 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____9086);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____9221 =
                                     let uu____9222 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____9222 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____9221) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____9345 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____9366 =
                        let uu____9367 =
                          let uu____9372 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____9372, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____9367 in
                      FStar_Exn.raise uu____9366))))
      | uu____9373 ->
          let uu____9376 =
            let uu____9377 =
              let uu____9382 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____9382, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____9377 in
          FStar_Exn.raise uu____9376
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____9395 = module_is_defined env l in
        if uu____9395
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____9398 =
             let uu____9399 =
               let uu____9404 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____9404, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____9399 in
           FStar_Exn.raise uu____9398)
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
            ((let uu____9423 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____9423 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____9427 =
                    let uu____9428 = FStar_Ident.string_of_lid l in
                    let uu____9429 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____9430 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____9428 uu____9429 uu____9430 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____9427);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____9447 = try_lookup_lid env l in
                (match uu____9447 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____9459 =
                         let uu____9460 = FStar_Options.interactive () in
                         Prims.op_Negation uu____9460 in
                       if uu____9459
                       then
                         let uu____9461 =
                           let uu____9462 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format1
                             "Admitting %s without a definition" uu____9462 in
                         FStar_Errors.warn (FStar_Ident.range_of_lid l)
                           uu____9461
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___196_9472 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___196_9472.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___196_9472.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___196_9472.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___196_9472.FStar_Syntax_Syntax.sigattrs)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____9473 -> ())
            | uu____9482 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9501) ->
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
                                (lid,uu____9521,uu____9522,uu____9523,uu____9524,uu____9525)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____9534 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____9537,uu____9538) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____9544,lbs),uu____9546) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____9567 =
                               let uu____9568 =
                                 let uu____9569 =
                                   let uu____9572 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____9572.FStar_Syntax_Syntax.fv_name in
                                 uu____9569.FStar_Syntax_Syntax.v in
                               uu____9568.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____9567))
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
                               let uu____9586 =
                                 let uu____9589 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____9589.FStar_Syntax_Syntax.fv_name in
                               uu____9586.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___197_9594 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___197_9594.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___197_9594.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___197_9594.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____9604 -> ()));
      (let curmod =
         let uu____9606 = current_module env in uu____9606.FStar_Ident.str in
       (let uu____9608 =
          let uu____9625 = get_exported_id_set env curmod in
          let uu____9632 = get_trans_exported_id_set env curmod in
          (uu____9625, uu____9632) in
        match uu____9608 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____9686 = cur_ex eikind in FStar_ST.op_Bang uu____9686 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____9940 =
                let uu____9941 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____9941 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____9940 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____10064 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___198_10082 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___198_10082.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___198_10082.exported_ids);
                    trans_exported_ids = (uu___198_10082.trans_exported_ids);
                    includes = (uu___198_10082.includes);
                    sigaccum = [];
                    sigmap = (uu___198_10082.sigmap);
                    iface = (uu___198_10082.iface);
                    admitted_iface = (uu___198_10082.admitted_iface);
                    expect_typ = (uu___198_10082.expect_typ);
                    docs = (uu___198_10082.docs);
                    remaining_iface_decls =
                      (uu___198_10082.remaining_iface_decls);
                    syntax_only = (uu___198_10082.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____10106 =
       let uu____10109 = FStar_ST.op_Bang stack in env :: uu____10109 in
     FStar_ST.op_Colon_Equals stack uu____10106);
    (let uu___199_10212 = env in
     let uu____10213 = FStar_Util.smap_copy (sigmap env) in
     let uu____10224 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___199_10212.curmodule);
       curmonad = (uu___199_10212.curmonad);
       modules = (uu___199_10212.modules);
       scope_mods = (uu___199_10212.scope_mods);
       exported_ids = (uu___199_10212.exported_ids);
       trans_exported_ids = (uu___199_10212.trans_exported_ids);
       includes = (uu___199_10212.includes);
       sigaccum = (uu___199_10212.sigaccum);
       sigmap = uu____10213;
       iface = (uu___199_10212.iface);
       admitted_iface = (uu___199_10212.admitted_iface);
       expect_typ = (uu___199_10212.expect_typ);
       docs = uu____10224;
       remaining_iface_decls = (uu___199_10212.remaining_iface_decls);
       syntax_only = (uu___199_10212.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____10230  ->
    let uu____10231 = FStar_ST.op_Bang stack in
    match uu____10231 with
    | env::tl1 ->
        (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10340 -> failwith "Impossible: Too many pops"
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____10356 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____10359 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____10393 = FStar_Util.smap_try_find sm' k in
              match uu____10393 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___200_10418 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___200_10418.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___200_10418.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___200_10418.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___200_10418.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____10419 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____10424 -> ()));
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
      let uu____10509 =
        let uu____10512 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____10512 in
      FStar_Util.set_elements uu____10509 in
    let fields =
      let uu____10759 =
        let uu____10762 = e Exported_id_field in FStar_ST.op_Bang uu____10762 in
      FStar_Util.set_elements uu____10759 in
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
          let uu____11039 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____11039 in
        let fields =
          let uu____11049 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____11049 in
        (fun uu___179_11054  ->
           match uu___179_11054 with
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
  'Auu____11167 .
    'Auu____11167 Prims.list FStar_Pervasives_Native.option ->
      'Auu____11167 Prims.list FStar_ST.ref
  =
  fun uu___180_11179  ->
    match uu___180_11179 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let inclusion_info: env -> FStar_Ident.lident -> module_inclusion_info =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____11214 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____11214 as_exported_ids in
      let uu____11217 = as_ids_opt env.exported_ids in
      let uu____11220 = as_ids_opt env.trans_exported_ids in
      let uu____11223 =
        let uu____11228 = FStar_Util.smap_try_find env.includes mname in
        FStar_Util.map_opt uu____11228 (fun r  -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____11217;
        mii_trans_exported_ids = uu____11220;
        mii_includes = uu____11223
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
                let convert_kind uu___181_11368 =
                  match uu___181_11368 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module in
                FStar_List.map
                  (fun uu____11380  ->
                     match uu____11380 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____11404 =
                    let uu____11409 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                    (uu____11409, Open_namespace) in
                  [uu____11404]
                else [] in
              let auto_open2 =
                FStar_List.rev
                  (FStar_List.append auto_open1 namespace_of_module) in
              (let uu____11439 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____11439);
              (match () with
               | () ->
                   ((let uu____11455 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____11455);
                    (match () with
                     | () ->
                         ((let uu____11471 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____11471);
                          (match () with
                           | () ->
                               let uu___201_11494 = env1 in
                               let uu____11495 =
                                 FStar_List.map
                                   (fun x  -> Open_module_or_namespace x)
                                   auto_open2 in
                               {
                                 curmodule =
                                   (FStar_Pervasives_Native.Some mname);
                                 curmonad = (uu___201_11494.curmonad);
                                 modules = (uu___201_11494.modules);
                                 scope_mods = uu____11495;
                                 exported_ids = (uu___201_11494.exported_ids);
                                 trans_exported_ids =
                                   (uu___201_11494.trans_exported_ids);
                                 includes = (uu___201_11494.includes);
                                 sigaccum = (uu___201_11494.sigaccum);
                                 sigmap = (env1.sigmap);
                                 iface = intf;
                                 admitted_iface = admitted;
                                 expect_typ = (uu___201_11494.expect_typ);
                                 docs = (uu___201_11494.docs);
                                 remaining_iface_decls =
                                   (uu___201_11494.remaining_iface_decls);
                                 syntax_only = (uu___201_11494.syntax_only)
                               }))))) in
            let uu____11500 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____11526  ->
                      match uu____11526 with
                      | (l,uu____11532) -> FStar_Ident.lid_equals l mname)) in
            match uu____11500 with
            | FStar_Pervasives_Native.None  ->
                let uu____11541 = prep env in (uu____11541, false)
            | FStar_Pervasives_Native.Some (uu____11542,m) ->
                ((let uu____11549 =
                    (let uu____11552 = FStar_Options.interactive () in
                     Prims.op_Negation uu____11552) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____11549
                  then
                    let uu____11553 =
                      let uu____11554 =
                        let uu____11559 =
                          FStar_Util.format1
                            "Duplicate module or interface name: %s"
                            mname.FStar_Ident.str in
                        (uu____11559, (FStar_Ident.range_of_lid mname)) in
                      FStar_Errors.Error uu____11554 in
                    FStar_Exn.raise uu____11553
                  else ());
                 (let uu____11561 =
                    let uu____11562 = push env in prep uu____11562 in
                  (uu____11561, true)))
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
          let uu___202_11572 = env in
          {
            curmodule = (uu___202_11572.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___202_11572.modules);
            scope_mods = (uu___202_11572.scope_mods);
            exported_ids = (uu___202_11572.exported_ids);
            trans_exported_ids = (uu___202_11572.trans_exported_ids);
            includes = (uu___202_11572.includes);
            sigaccum = (uu___202_11572.sigaccum);
            sigmap = (uu___202_11572.sigmap);
            iface = (uu___202_11572.iface);
            admitted_iface = (uu___202_11572.admitted_iface);
            expect_typ = (uu___202_11572.expect_typ);
            docs = (uu___202_11572.docs);
            remaining_iface_decls = (uu___202_11572.remaining_iface_decls);
            syntax_only = (uu___202_11572.syntax_only)
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
        let uu____11603 = lookup lid in
        match uu____11603 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____11616  ->
                   match uu____11616 with
                   | (lid1,uu____11622) -> FStar_Ident.text_of_lid lid1)
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
                   let uu____11627 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
                   FStar_Ident.set_lid_range uu____11627
                     (FStar_Ident.range_of_lid lid) in
                 let uu____11628 = resolve_module_name env modul true in
                 match uu____11628 with
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
    fun id  ->
      let uu____11662 = lookup id in
      match uu____11662 with
      | FStar_Pervasives_Native.None  ->
          FStar_Exn.raise
            (FStar_Errors.Error
               ((Prims.strcat "Identifier not found ["
                   (Prims.strcat id.FStar_Ident.idText "]")),
                 (id.FStar_Ident.idRange)))
      | FStar_Pervasives_Native.Some r -> r