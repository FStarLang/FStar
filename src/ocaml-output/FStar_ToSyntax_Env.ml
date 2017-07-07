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
    match projectee with | Open_module  -> true | uu____13 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____18 -> false
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
    match projectee with | Local_binding _0 -> true | uu____161 -> false
let __proj__Local_binding__item___0: scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0
let uu___is_Rec_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____175 -> false
let __proj__Rec_binding__item___0: scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____189 -> false
let __proj__Module_abbrev__item___0: scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____203 -> false
let __proj__Open_module_or_namespace__item___0:
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_def: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____217 -> false
let __proj__Top_level_def__item___0: scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0
let uu___is_Record_or_dc: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____231 -> false
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
    | uu____245 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____250 -> false
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
    match projectee with | Term_name _0 -> true | uu____962 -> false
let __proj__Term_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.typ,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____984 -> false
let __proj__Eff_name__item___0:
  foundname ->
    (FStar_Syntax_Syntax.sigelt,FStar_Ident.lident)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___176_1007 = env in
      {
        curmodule = (uu___176_1007.curmodule);
        curmonad = (uu___176_1007.curmonad);
        modules = (uu___176_1007.modules);
        scope_mods = (uu___176_1007.scope_mods);
        exported_ids = (uu___176_1007.exported_ids);
        trans_exported_ids = (uu___176_1007.trans_exported_ids);
        includes = (uu___176_1007.includes);
        sigaccum = (uu___176_1007.sigaccum);
        sigmap = (uu___176_1007.sigmap);
        iface = b;
        admitted_iface = (uu___176_1007.admitted_iface);
        expect_typ = (uu___176_1007.expect_typ);
        docs = (uu___176_1007.docs);
        remaining_iface_decls = (uu___176_1007.remaining_iface_decls);
        syntax_only = (uu___176_1007.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___177_1020 = e in
      {
        curmodule = (uu___177_1020.curmodule);
        curmonad = (uu___177_1020.curmonad);
        modules = (uu___177_1020.modules);
        scope_mods = (uu___177_1020.scope_mods);
        exported_ids = (uu___177_1020.exported_ids);
        trans_exported_ids = (uu___177_1020.trans_exported_ids);
        includes = (uu___177_1020.includes);
        sigaccum = (uu___177_1020.sigaccum);
        sigmap = (uu___177_1020.sigmap);
        iface = (uu___177_1020.iface);
        admitted_iface = b;
        expect_typ = (uu___177_1020.expect_typ);
        docs = (uu___177_1020.docs);
        remaining_iface_decls = (uu___177_1020.remaining_iface_decls);
        syntax_only = (uu___177_1020.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___178_1033 = e in
      {
        curmodule = (uu___178_1033.curmodule);
        curmonad = (uu___178_1033.curmonad);
        modules = (uu___178_1033.modules);
        scope_mods = (uu___178_1033.scope_mods);
        exported_ids = (uu___178_1033.exported_ids);
        trans_exported_ids = (uu___178_1033.trans_exported_ids);
        includes = (uu___178_1033.includes);
        sigaccum = (uu___178_1033.sigaccum);
        sigmap = (uu___178_1033.sigmap);
        iface = (uu___178_1033.iface);
        admitted_iface = (uu___178_1033.admitted_iface);
        expect_typ = b;
        docs = (uu___178_1033.docs);
        remaining_iface_decls = (uu___178_1033.remaining_iface_decls);
        syntax_only = (uu___178_1033.syntax_only)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1049 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____1049 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____1053 =
            let uu____1054 = exported_id_set Exported_id_term_type in
            FStar_ST.read uu____1054 in
          FStar_All.pipe_right uu____1053 FStar_Util.set_elements
let open_modules:
  env ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.modul)
      FStar_Pervasives_Native.tuple2 Prims.list
  = fun e  -> e.modules
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___179_1075 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___179_1075.curmonad);
        modules = (uu___179_1075.modules);
        scope_mods = (uu___179_1075.scope_mods);
        exported_ids = (uu___179_1075.exported_ids);
        trans_exported_ids = (uu___179_1075.trans_exported_ids);
        includes = (uu___179_1075.includes);
        sigaccum = (uu___179_1075.sigaccum);
        sigmap = (uu___179_1075.sigmap);
        iface = (uu___179_1075.iface);
        admitted_iface = (uu___179_1075.admitted_iface);
        expect_typ = (uu___179_1075.expect_typ);
        docs = (uu___179_1075.docs);
        remaining_iface_decls = (uu___179_1075.remaining_iface_decls);
        syntax_only = (uu___179_1075.syntax_only)
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
      let uu____1091 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____1110  ->
                match uu____1110 with
                | (m,uu____1115) -> FStar_Ident.lid_equals l m)) in
      match uu____1091 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____1124,decls) ->
          FStar_Pervasives_Native.Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____1146 =
          FStar_List.partition
            (fun uu____1163  ->
               match uu____1163 with
               | (m,uu____1168) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____1146 with
        | (uu____1171,rest) ->
            let uu___180_1189 = env in
            {
              curmodule = (uu___180_1189.curmodule);
              curmonad = (uu___180_1189.curmonad);
              modules = (uu___180_1189.modules);
              scope_mods = (uu___180_1189.scope_mods);
              exported_ids = (uu___180_1189.exported_ids);
              trans_exported_ids = (uu___180_1189.trans_exported_ids);
              includes = (uu___180_1189.includes);
              sigaccum = (uu___180_1189.sigaccum);
              sigmap = (uu___180_1189.sigmap);
              iface = (uu___180_1189.iface);
              admitted_iface = (uu___180_1189.admitted_iface);
              expect_typ = (uu___180_1189.expect_typ);
              docs = (uu___180_1189.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___180_1189.syntax_only)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____1208 = current_module env in qual uu____1208 id
      | FStar_Pervasives_Native.Some monad ->
          let uu____1210 =
            let uu____1211 = current_module env in qual uu____1211 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____1210 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___181_1224 = env in
      {
        curmodule = (uu___181_1224.curmodule);
        curmonad = (uu___181_1224.curmonad);
        modules = (uu___181_1224.modules);
        scope_mods = (uu___181_1224.scope_mods);
        exported_ids = (uu___181_1224.exported_ids);
        trans_exported_ids = (uu___181_1224.trans_exported_ids);
        includes = (uu___181_1224.includes);
        sigaccum = (uu___181_1224.sigaccum);
        sigmap = (uu___181_1224.sigmap);
        iface = (uu___181_1224.iface);
        admitted_iface = (uu___181_1224.admitted_iface);
        expect_typ = (uu___181_1224.expect_typ);
        docs = (uu___181_1224.docs);
        remaining_iface_decls = (uu___181_1224.remaining_iface_decls);
        syntax_only = b
      }
let new_sigmap uu____1234 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____1238  ->
    let uu____1239 = new_sigmap () in
    let uu____1241 = new_sigmap () in
    let uu____1243 = new_sigmap () in
    let uu____1249 = new_sigmap () in
    let uu____1255 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____1239;
      trans_exported_ids = uu____1241;
      includes = uu____1243;
      sigaccum = [];
      sigmap = uu____1249;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____1255;
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
      (fun uu____1278  ->
         match uu____1278 with
         | (m,uu____1282) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___182_1292 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___182_1292.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___183_1293 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___183_1293.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___183_1293.FStar_Syntax_Syntax.sort)
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
        (fun uu____1348  ->
           match uu____1348 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____1362 =
                   let uu____1363 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____1363 dd dq in
                 FStar_Pervasives_Native.Some uu____1362
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
  match projectee with | Cont_ok _0 -> true | uu____1396 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____1424 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____1437 -> false
let option_of_cont k_ignore uu___148_1459 =
  match uu___148_1459 with
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
        (fun uu____1512  ->
           match uu____1512 with
           | (f,uu____1517) ->
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
  fun uu___149_1558  ->
    match uu___149_1558 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___150_1614 =
    match uu___150_1614 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
          let uu____1622 = get_exported_id_set env mname in
          match uu____1622 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some mex ->
              let mexports =
                let uu____1638 = mex eikind in FStar_ST.read uu____1638 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____1645 = FStar_Util.smap_try_find env.includes mname in
          match uu____1645 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
          then let uu____1665 = qual modul id in find_in_module uu____1665
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____1668 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___151_1673  ->
    match uu___151_1673 with
    | Exported_id_field  -> true
    | uu____1674 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___152_1772 =
    match uu___152_1772 with
    | (id',uu____1774,uu____1775) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___153_1779 =
    match uu___153_1779 with
    | (id',uu____1781,uu____1782) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1785 = current_module env in FStar_Ident.ids_of_lid uu____1785 in
  let proc uu___154_1790 =
    match uu___154_1790 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,Open_module ) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____1797 = FStar_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____1797 id
    | uu____1802 -> Cont_ignore in
  let rec aux uu___155_1808 =
    match uu___155_1808 with
    | a::q ->
        let uu____1814 = proc a in
        option_of_cont (fun uu____1817  -> aux q) uu____1814
    | [] ->
        let uu____1818 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____1821  -> FStar_Pervasives_Native.None)
          uu____1818 in
  aux env.scope_mods
let found_local_binding r uu____1844 =
  match uu____1844 with
  | (id',x,mut) -> let uu____1851 = bv_to_name x r in (uu____1851, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____1893 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____1893 with
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
      let uu____1917 = unmangleOpName id in
      match uu____1917 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____1931 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1940 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1940) (fun uu____1946  -> Cont_fail)
            (fun uu____1950  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1960  -> fun uu____1961  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1970  -> fun uu____1971  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | FStar_Pervasives_Native.Some uu____2028 ->
        let lid = qualify env id in
        let uu____2030 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____2030 with
         | FStar_Pervasives_Native.Some r ->
             let uu____2043 = k_global_def lid r in
             FStar_Pervasives_Native.Some uu____2043
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None in
  match find_in_monad with
  | FStar_Pervasives_Native.Some v1 -> v1
  | FStar_Pervasives_Native.None  ->
      let lid = let uu____2056 = current_module env in qual uu____2056 id in
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | FStar_Pervasives_Native.None  -> false
       | FStar_Pervasives_Native.Some m ->
           let uu____2067 = current_module env in
           FStar_Ident.lid_equals lid uu____2067)
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
        let rec aux uu___156_2096 =
          match uu___156_2096 with
          | [] ->
              let uu____2099 = module_is_defined env lid in
              if uu____2099
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____2106 =
                  let uu____2108 = FStar_Ident.path_of_lid ns in
                  let uu____2110 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____2108 uu____2110 in
                FStar_Ident.lid_of_path uu____2106
                  (FStar_Ident.range_of_lid lid) in
              let uu____2112 = module_is_defined env new_lid in
              if uu____2112
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____2117 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____2123::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____2138 =
          let uu____2139 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____2139 in
        if uu____2138
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
           then ()
           else
             (let uu____2141 =
                let uu____2142 =
                  let uu____2145 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____2145, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____2142 in
              raise uu____2141))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____2155 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____2158 = resolve_module_name env modul_orig true in
          (match uu____2158 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____2161 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___157_2173  ->
           match uu___157_2173 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____2175 -> false) env.scope_mods
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
                 let uu____2233 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____2233
                   (FStar_Util.map_option
                      (fun uu____2260  ->
                         match uu____2260 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____2277 =
          is_full_path &&
            (let uu____2279 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____2279) in
        if uu____2277
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____2296 = aux ns_rev_prefix ns_last_id in
               (match uu____2296 with
                | FStar_Pervasives_Native.None  -> ([], ids)
                | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____2332 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____2332 with
      | (uu____2337,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____2437::uu____2438 ->
      let uu____2440 =
        let uu____2442 =
          let uu____2443 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____2443 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____2442 true in
      (match uu____2440 with
       | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some modul ->
           let uu____2446 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____2449  -> FStar_Pervasives_Native.None)
             uu____2446)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___158_2467 =
  match uu___158_2467 with
  | FStar_Pervasives_Native.Some v1 -> Cont_ok v1
  | FStar_Pervasives_Native.None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____2552 = k_global_def lid1 def in cont_of_option k uu____2552 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____2575 = k_local_binding l in
       cont_of_option Cont_fail uu____2575)
    (fun r  ->
       let uu____2580 = k_rec_binding r in
       cont_of_option Cont_fail uu____2580) (fun uu____2583  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____2590,uu____2591,uu____2592,l,uu____2594,uu____2595) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___159_2603  ->
               match uu___159_2603 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____2605,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____2612 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____2616,uu____2617,uu____2618)
        -> FStar_Pervasives_Native.None
    | uu____2619 -> FStar_Pervasives_Native.None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____2630 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____2637 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____2637
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2630 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____2658 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____2658 ns)
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
          let k_global_def source_lid uu___163_2687 =
            match uu___163_2687 with
            | (uu____2691,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____2693) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____2695 ->
                     let uu____2704 =
                       let uu____2705 =
                         let uu____2708 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____2708, false) in
                       Term_name uu____2705 in
                     FStar_Pervasives_Native.Some uu____2704
                 | FStar_Syntax_Syntax.Sig_datacon uu____2709 ->
                     let uu____2717 =
                       let uu____2718 =
                         let uu____2721 =
                           let uu____2722 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____2722 in
                         (uu____2721, false) in
                       Term_name uu____2718 in
                     FStar_Pervasives_Native.Some uu____2717
                 | FStar_Syntax_Syntax.Sig_let ((uu____2724,lbs),uu____2726)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____2735 =
                       let uu____2736 =
                         let uu____2739 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____2739, false) in
                       Term_name uu____2736 in
                     FStar_Pervasives_Native.Some uu____2735
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____2741,uu____2742) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____2745 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___160_2748  ->
                                  match uu___160_2748 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____2749 -> false))) in
                     if uu____2745
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____2753 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___161_2757  ->
                                      match uu___161_2757 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____2758 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____2761 -> true
                                      | uu____2762 -> false))) in
                         if uu____2753
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____2764 =
                         FStar_Util.find_map quals
                           (fun uu___162_2768  ->
                              match uu___162_2768 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____2771 -> FStar_Pervasives_Native.None) in
                       (match uu____2764 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name (refl_const, false))
                        | uu____2783 ->
                            let uu____2785 =
                              let uu____2786 =
                                let uu____2789 =
                                  let uu____2790 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____2790 in
                                (uu____2789, false) in
                              Term_name uu____2786 in
                            FStar_Pervasives_Native.Some uu____2785)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2795 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | uu____2802 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let uu____2814 =
              let uu____2815 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____2815 in
            FStar_Pervasives_Native.Some uu____2814 in
          let k_rec_binding uu____2825 =
            match uu____2825 with
            | (id,l,dd) ->
                let uu____2833 =
                  let uu____2834 =
                    let uu____2837 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd
                        FStar_Pervasives_Native.None in
                    (uu____2837, false) in
                  Term_name uu____2834 in
                FStar_Pervasives_Native.Some uu____2833 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2841 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2841 with
                 | FStar_Pervasives_Native.Some f ->
                     FStar_Pervasives_Native.Some (Term_name f)
                 | uu____2851 -> FStar_Pervasives_Native.None)
            | uu____2855 -> FStar_Pervasives_Native.None in
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
        let uu____2878 = try_lookup_name true exclude_interf env lid in
        match uu____2878 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____2887 -> FStar_Pervasives_Native.None
let try_lookup_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2900 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2900 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____2909 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,FStar_Syntax_Syntax.cflags Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2925 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2925 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2934;
             FStar_Syntax_Syntax.sigquals = uu____2935;
             FStar_Syntax_Syntax.sigmeta = uu____2936;
             FStar_Syntax_Syntax.sigattrs = uu____2937;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2948;
             FStar_Syntax_Syntax.sigquals = uu____2949;
             FStar_Syntax_Syntax.sigmeta = uu____2950;
             FStar_Syntax_Syntax.sigattrs = uu____2951;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____2961,uu____2962,uu____2963,uu____2964,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2966;
             FStar_Syntax_Syntax.sigquals = uu____2967;
             FStar_Syntax_Syntax.sigmeta = uu____2968;
             FStar_Syntax_Syntax.sigattrs = uu____2969;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____2981 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2997 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2997 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____3003;
             FStar_Syntax_Syntax.sigquals = uu____3004;
             FStar_Syntax_Syntax.sigmeta = uu____3005;
             FStar_Syntax_Syntax.sigattrs = uu____3006;_},uu____3007)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____3013;
             FStar_Syntax_Syntax.sigquals = uu____3014;
             FStar_Syntax_Syntax.sigmeta = uu____3015;
             FStar_Syntax_Syntax.sigattrs = uu____3016;_},uu____3017)
          -> FStar_Pervasives_Native.Some ne
      | uu____3022 -> FStar_Pervasives_Native.None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3034 = try_lookup_effect_name env lid in
      match uu____3034 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____3036 -> true
let try_lookup_root_effect_name:
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____3046 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____3046 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____3052,uu____3053,uu____3054,uu____3055);
             FStar_Syntax_Syntax.sigrng = uu____3056;
             FStar_Syntax_Syntax.sigquals = uu____3057;
             FStar_Syntax_Syntax.sigmeta = uu____3058;
             FStar_Syntax_Syntax.sigattrs = uu____3059;_},uu____3060)
          ->
          let rec aux new_name =
            let uu____3072 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____3072 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____3082) ->
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
                     (uu____3088,uu____3089,uu____3090,cmp,uu____3092) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____3096 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____3097,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____3101 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___164_3124 =
        match uu___164_3124 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____3129,uu____3130,uu____3131);
             FStar_Syntax_Syntax.sigrng = uu____3132;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____3134;
             FStar_Syntax_Syntax.sigattrs = uu____3135;_},uu____3136)
            -> FStar_Pervasives_Native.Some quals
        | uu____3140 -> FStar_Pervasives_Native.None in
      let uu____3144 =
        resolve_in_open_namespaces' env lid
          (fun uu____3149  -> FStar_Pervasives_Native.None)
          (fun uu____3152  -> FStar_Pervasives_Native.None) k_global_def in
      match uu____3144 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____3158 -> []
let try_lookup_module:
  env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
  =
  fun env  ->
    fun path  ->
      let uu____3172 =
        FStar_List.tryFind
          (fun uu____3182  ->
             match uu____3182 with
             | (mlid,modul) ->
                 let uu____3187 = FStar_Ident.path_of_lid mlid in
                 uu____3187 = path) env.modules in
      match uu____3172 with
      | FStar_Pervasives_Native.Some (uu____3191,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let try_lookup_let:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___165_3215 =
        match uu___165_3215 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____3219,lbs),uu____3221);
             FStar_Syntax_Syntax.sigrng = uu____3222;
             FStar_Syntax_Syntax.sigquals = uu____3223;
             FStar_Syntax_Syntax.sigmeta = uu____3224;
             FStar_Syntax_Syntax.sigattrs = uu____3225;_},uu____3226)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____3237 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____3237
        | uu____3238 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____3242  -> FStar_Pervasives_Native.None)
        (fun uu____3244  -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___166_3265 =
        match uu___166_3265 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____3272);
             FStar_Syntax_Syntax.sigrng = uu____3273;
             FStar_Syntax_Syntax.sigquals = uu____3274;
             FStar_Syntax_Syntax.sigmeta = uu____3275;
             FStar_Syntax_Syntax.sigattrs = uu____3276;_},uu____3277)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____3294 -> FStar_Pervasives_Native.None)
        | uu____3299 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____3307  -> FStar_Pervasives_Native.None)
        (fun uu____3311  -> FStar_Pervasives_Native.None) k_global_def
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
          let uu____3342 = try_lookup_name any_val exclude_interf env lid in
          match uu____3342 with
          | FStar_Pervasives_Native.Some (Term_name (e,mut)) ->
              FStar_Pervasives_Native.Some (e, mut)
          | uu____3351 -> FStar_Pervasives_Native.None
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
      let uu____3375 = try_lookup_lid env l in
      match uu____3375 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (e,uu____3383) ->
          let uu____3386 =
            let uu____3387 = FStar_Syntax_Subst.compress e in
            uu____3387.FStar_Syntax_Syntax.n in
          (match uu____3386 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____3392 -> FStar_Pervasives_Native.None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___184_3405 = env in
        {
          curmodule = (uu___184_3405.curmodule);
          curmonad = (uu___184_3405.curmonad);
          modules = (uu___184_3405.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___184_3405.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___184_3405.sigaccum);
          sigmap = (uu___184_3405.sigmap);
          iface = (uu___184_3405.iface);
          admitted_iface = (uu___184_3405.admitted_iface);
          expect_typ = (uu___184_3405.expect_typ);
          docs = (uu___184_3405.docs);
          remaining_iface_decls = (uu___184_3405.remaining_iface_decls);
          syntax_only = (uu___184_3405.syntax_only)
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
      let k_global_def lid1 uu___168_3433 =
        match uu___168_3433 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____3437,uu____3438,uu____3439);
             FStar_Syntax_Syntax.sigrng = uu____3440;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____3442;
             FStar_Syntax_Syntax.sigattrs = uu____3443;_},uu____3444)
            ->
            let uu____3447 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___167_3450  ->
                      match uu___167_3450 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____3451 -> false)) in
            if uu____3447
            then
              let uu____3453 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____3453
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____3455;
             FStar_Syntax_Syntax.sigrng = uu____3456;
             FStar_Syntax_Syntax.sigquals = uu____3457;
             FStar_Syntax_Syntax.sigmeta = uu____3458;
             FStar_Syntax_Syntax.sigattrs = uu____3459;_},uu____3460)
            ->
            let uu____3470 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Pervasives_Native.Some uu____3470
        | uu____3471 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____3475  -> FStar_Pervasives_Native.None)
        (fun uu____3477  -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___169_3498 =
        match uu___169_3498 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____3503,uu____3504,uu____3505,uu____3506,datas,uu____3508);
             FStar_Syntax_Syntax.sigrng = uu____3509;
             FStar_Syntax_Syntax.sigquals = uu____3510;
             FStar_Syntax_Syntax.sigmeta = uu____3511;
             FStar_Syntax_Syntax.sigattrs = uu____3512;_},uu____3513)
            -> FStar_Pervasives_Native.Some datas
        | uu____3521 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env lid
        (fun uu____3527  -> FStar_Pervasives_Native.None)
        (fun uu____3530  -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter:
  ((Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                        record_or_dc
                                                          Prims.list,
     record_or_dc -> Prims.unit,Prims.unit -> Prims.unit)
     FStar_Pervasives_Native.tuple5,Prims.unit -> Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____3564 =
    let uu____3565 =
      let uu____3568 =
        let uu____3570 = FStar_ST.read record_cache in
        FStar_List.hd uu____3570 in
      let uu____3578 = FStar_ST.read record_cache in uu____3568 :: uu____3578 in
    FStar_ST.write record_cache uu____3565 in
  let pop1 uu____3593 =
    let uu____3594 =
      let uu____3597 = FStar_ST.read record_cache in FStar_List.tl uu____3597 in
    FStar_ST.write record_cache uu____3594 in
  let peek1 uu____3613 =
    let uu____3614 = FStar_ST.read record_cache in FStar_List.hd uu____3614 in
  let insert r =
    let uu____3626 =
      let uu____3629 = let uu____3631 = peek1 () in r :: uu____3631 in
      let uu____3633 =
        let uu____3636 = FStar_ST.read record_cache in
        FStar_List.tl uu____3636 in
      uu____3629 :: uu____3633 in
    FStar_ST.write record_cache uu____3626 in
  let commit1 uu____3652 =
    let uu____3653 = FStar_ST.read record_cache in
    match uu____3653 with
    | hd1::uu____3661::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____3674 -> failwith "Impossible" in
  let filter1 uu____3680 =
    let rc = peek1 () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____3688 =
           let uu____3691 = FStar_ST.read record_cache in filtered ::
             uu____3691 in
         FStar_ST.write record_cache uu____3688) in
  let aux = (push1, pop1, peek1, insert, commit1) in (aux, filter1)
let record_cache_aux:
  (Prims.unit -> Prims.unit,Prims.unit -> Prims.unit,Prims.unit ->
                                                       record_or_dc
                                                         Prims.list,record_or_dc
                                                                    ->
                                                                    Prims.unit,
    Prims.unit -> Prims.unit) FStar_Pervasives_Native.tuple5
  =
  let uu____3765 = record_cache_aux_with_filter in
  match uu____3765 with | (aux,uu____3803) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____3843 = record_cache_aux_with_filter in
  match uu____3843 with | (uu____3866,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____3907 = record_cache_aux in
  match uu____3907 with
  | (push1,uu____3927,uu____3928,uu____3929,uu____3930) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3956 = record_cache_aux in
  match uu____3956 with
  | (uu____3975,pop1,uu____3977,uu____3978,uu____3979) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____4006 = record_cache_aux in
  match uu____4006 with
  | (uu____4026,uu____4027,peek1,uu____4029,uu____4030) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____4056 = record_cache_aux in
  match uu____4056 with
  | (uu____4075,uu____4076,uu____4077,insert,uu____4079) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____4105 = record_cache_aux in
  match uu____4105 with
  | (uu____4124,uu____4125,uu____4126,uu____4127,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____4170) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___170_4181  ->
                   match uu___170_4181 with
                   | FStar_Syntax_Syntax.RecordType uu____4182 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____4187 -> true
                   | uu____4192 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___171_4211  ->
                      match uu___171_4211 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____4213,uu____4214,uu____4215,uu____4216,uu____4217);
                          FStar_Syntax_Syntax.sigrng = uu____4218;
                          FStar_Syntax_Syntax.sigquals = uu____4219;
                          FStar_Syntax_Syntax.sigmeta = uu____4220;
                          FStar_Syntax_Syntax.sigattrs = uu____4221;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____4226 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___172_4260  ->
                    match uu___172_4260 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____4264,uu____4265,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____4267;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____4269;
                        FStar_Syntax_Syntax.sigattrs = uu____4270;_} ->
                        let uu____4276 =
                          let uu____4277 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____4277 in
                        (match uu____4276 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____4281,t,uu____4283,uu____4284,uu____4285);
                             FStar_Syntax_Syntax.sigrng = uu____4286;
                             FStar_Syntax_Syntax.sigquals = uu____4287;
                             FStar_Syntax_Syntax.sigmeta = uu____4288;
                             FStar_Syntax_Syntax.sigattrs = uu____4289;_} ->
                             let uu____4294 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____4294 with
                              | (formals,uu____4303) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____4333  ->
                                            match uu____4333 with
                                            | (x,q) ->
                                                let uu____4341 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____4341
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____4376  ->
                                            match uu____4376 with
                                            | (x,q) ->
                                                let uu____4385 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____4385,
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
                                  ((let uu____4397 =
                                      let uu____4399 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____4399 in
                                    FStar_ST.write new_globs uu____4397);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____4415 =
                                            match uu____4415 with
                                            | (id,uu____4421) ->
                                                let modul =
                                                  let uu____4427 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____4427.FStar_Ident.str in
                                                let uu____4428 =
                                                  get_exported_id_set e modul in
                                                (match uu____4428 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____4444 =
                                                         let uu____4445 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____4445 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____4444);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____4452 =
                                                               let uu____4453
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____4453.FStar_Ident.ident in
                                                             uu____4452.FStar_Ident.idText in
                                                           let uu____4455 =
                                                             let uu____4456 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____4456 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____4455))
                                                 | FStar_Pervasives_Native.None
                                                      -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____4469 -> ())
                    | uu____4470 -> ()))
        | uu____4471 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____4486 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____4486 with
        | (ns,id) ->
            let uu____4496 = peek_record_cache () in
            FStar_Util.find_map uu____4496
              (fun record  ->
                 let uu____4501 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont
                   (fun uu____4506  -> FStar_Pervasives_Native.None)
                   uu____4501) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____4508  -> Cont_ignore) (fun uu____4510  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____4516 = find_in_cache fn in
           cont_of_option Cont_ignore uu____4516)
        (fun k  -> fun uu____4521  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option =
  fun env  ->
    fun fieldname  ->
      let uu____4532 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____4532 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____4536 -> FStar_Pervasives_Native.None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____4550 = try_lookup_record_by_field_name env lid in
        match uu____4550 with
        | FStar_Pervasives_Native.Some record' when
            let uu____4553 =
              let uu____4554 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____4554 in
            let uu____4556 =
              let uu____4557 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____4557 in
            uu____4553 = uu____4556 ->
            let uu____4559 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____4562  -> Cont_ok ()) in
            (match uu____4559 with
             | Cont_ok uu____4563 -> true
             | uu____4564 -> false)
        | uu____4566 -> false
let try_lookup_dc_by_field_name:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____4579 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____4579 with
      | FStar_Pervasives_Native.Some r ->
          let uu____4585 =
            let uu____4588 =
              let uu____4589 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____4589
                (FStar_Ident.range_of_lid fieldname) in
            (uu____4588, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____4585
      | uu____4592 -> FStar_Pervasives_Native.None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____4602  ->
    let uu____4603 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____4603
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____4615  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___173_4624  ->
      match uu___173_4624 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___174_4648 =
            match uu___174_4648 with
            | Rec_binding uu____4649 -> true
            | uu____4650 -> false in
          let this_env =
            let uu___185_4652 = env in
            let uu____4653 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___185_4652.curmodule);
              curmonad = (uu___185_4652.curmonad);
              modules = (uu___185_4652.modules);
              scope_mods = uu____4653;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___185_4652.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___185_4652.sigaccum);
              sigmap = (uu___185_4652.sigmap);
              iface = (uu___185_4652.iface);
              admitted_iface = (uu___185_4652.admitted_iface);
              expect_typ = (uu___185_4652.expect_typ);
              docs = (uu___185_4652.docs);
              remaining_iface_decls = (uu___185_4652.remaining_iface_decls);
              syntax_only = (uu___185_4652.syntax_only)
            } in
          let uu____4655 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____4655 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____4661 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___186_4674 = env in
      {
        curmodule = (uu___186_4674.curmodule);
        curmonad = (uu___186_4674.curmonad);
        modules = (uu___186_4674.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___186_4674.exported_ids);
        trans_exported_ids = (uu___186_4674.trans_exported_ids);
        includes = (uu___186_4674.includes);
        sigaccum = (uu___186_4674.sigaccum);
        sigmap = (uu___186_4674.sigmap);
        iface = (uu___186_4674.iface);
        admitted_iface = (uu___186_4674.admitted_iface);
        expect_typ = (uu___186_4674.expect_typ);
        docs = (uu___186_4674.docs);
        remaining_iface_decls = (uu___186_4674.remaining_iface_decls);
        syntax_only = (uu___186_4674.syntax_only)
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
        let uu____4723 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____4723
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
          | FStar_Pervasives_Native.Some (se,uu____4745) ->
              let uu____4748 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____4748 with
               | FStar_Pervasives_Native.Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | FStar_Pervasives_Native.None  -> "<unknown>")
          | FStar_Pervasives_Native.None  -> "<unknown>" in
        let uu____4753 =
          let uu____4754 =
            let uu____4757 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____4757, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____4754 in
        raise uu____4753 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____4764 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____4769 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____4773 -> (true, true)
          | uu____4778 -> (false, false) in
        match uu____4764 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____4783 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____4788 =
                     let uu____4789 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____4789 in
                   if uu____4788
                   then FStar_Pervasives_Native.Some l
                   else FStar_Pervasives_Native.None) in
            (match uu____4783 with
             | FStar_Pervasives_Native.Some l when
                 let uu____4793 = FStar_Options.interactive () in
                 Prims.op_Negation uu____4793 -> err1 l
             | uu____4794 ->
                 (extract_record env globals s;
                  (let uu___187_4799 = env in
                   {
                     curmodule = (uu___187_4799.curmodule);
                     curmonad = (uu___187_4799.curmonad);
                     modules = (uu___187_4799.modules);
                     scope_mods = (uu___187_4799.scope_mods);
                     exported_ids = (uu___187_4799.exported_ids);
                     trans_exported_ids = (uu___187_4799.trans_exported_ids);
                     includes = (uu___187_4799.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___187_4799.sigmap);
                     iface = (uu___187_4799.iface);
                     admitted_iface = (uu___187_4799.admitted_iface);
                     expect_typ = (uu___187_4799.expect_typ);
                     docs = (uu___187_4799.docs);
                     remaining_iface_decls =
                       (uu___187_4799.remaining_iface_decls);
                     syntax_only = (uu___187_4799.syntax_only)
                   }))) in
      let env2 =
        let uu___188_4801 = env1 in
        let uu____4802 = FStar_ST.read globals in
        {
          curmodule = (uu___188_4801.curmodule);
          curmonad = (uu___188_4801.curmonad);
          modules = (uu___188_4801.modules);
          scope_mods = uu____4802;
          exported_ids = (uu___188_4801.exported_ids);
          trans_exported_ids = (uu___188_4801.trans_exported_ids);
          includes = (uu___188_4801.includes);
          sigaccum = (uu___188_4801.sigaccum);
          sigmap = (uu___188_4801.sigmap);
          iface = (uu___188_4801.iface);
          admitted_iface = (uu___188_4801.admitted_iface);
          expect_typ = (uu___188_4801.expect_typ);
          docs = (uu___188_4801.docs);
          remaining_iface_decls = (uu___188_4801.remaining_iface_decls);
          syntax_only = (uu___188_4801.syntax_only)
        } in
      let uu____4807 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4821) ->
            let uu____4826 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____4826)
        | uu____4841 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____4807 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____4874  ->
                   match uu____4874 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____4889 =
                                  let uu____4891 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____4891 in
                                FStar_ST.write globals uu____4889);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____4900 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____4900.FStar_Ident.str in
                                    ((let uu____4902 =
                                        get_exported_id_set env3 modul in
                                      match uu____4902 with
                                      | FStar_Pervasives_Native.Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____4917 =
                                            let uu____4918 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____4918 in
                                          FStar_ST.write my_exported_ids
                                            uu____4917
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
              let uu___189_4930 = env3 in
              let uu____4931 = FStar_ST.read globals in
              {
                curmodule = (uu___189_4930.curmodule);
                curmonad = (uu___189_4930.curmonad);
                modules = (uu___189_4930.modules);
                scope_mods = uu____4931;
                exported_ids = (uu___189_4930.exported_ids);
                trans_exported_ids = (uu___189_4930.trans_exported_ids);
                includes = (uu___189_4930.includes);
                sigaccum = (uu___189_4930.sigaccum);
                sigmap = (uu___189_4930.sigmap);
                iface = (uu___189_4930.iface);
                admitted_iface = (uu___189_4930.admitted_iface);
                expect_typ = (uu___189_4930.expect_typ);
                docs = (uu___189_4930.docs);
                remaining_iface_decls = (uu___189_4930.remaining_iface_decls);
                syntax_only = (uu___189_4930.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____4944 =
        let uu____4947 = resolve_module_name env ns false in
        match uu____4947 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules in
            let uu____4955 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____4964  ->
                      match uu____4964 with
                      | (m,uu____4968) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____4955
            then (ns, Open_namespace)
            else
              (let uu____4972 =
                 let uu____4973 =
                   let uu____4976 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____4976, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____4973 in
               raise uu____4972)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____4944 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____4992 = resolve_module_name env ns false in
      match uu____4992 with
      | FStar_Pervasives_Native.Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____4998 = current_module env1 in
              uu____4998.FStar_Ident.str in
            (let uu____5000 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____5000 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____5013 =
                   let uu____5015 = FStar_ST.read incl in ns1 :: uu____5015 in
                 FStar_ST.write incl uu____5013);
            (match () with
             | () ->
                 let uu____5023 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____5023 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____5036 =
                          let uu____5047 = get_exported_id_set env1 curmod in
                          let uu____5052 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____5047, uu____5052) in
                        match uu____5036 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____5092 = ns_trans_exports k in
                                FStar_ST.read uu____5092 in
                              let ex = cur_exports k in
                              (let uu____5101 =
                                 let uu____5102 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____5102 ns_ex in
                               FStar_ST.write ex uu____5101);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____5112 =
                                     let uu____5113 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____5113 ns_ex in
                                   FStar_ST.write trans_ex uu____5112) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____5119 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5133 =
                        let uu____5134 =
                          let uu____5137 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____5137, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____5134 in
                      raise uu____5133))))
      | uu____5138 ->
          let uu____5140 =
            let uu____5141 =
              let uu____5144 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____5144, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____5141 in
          raise uu____5140
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____5157 = module_is_defined env l in
        if uu____5157
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____5160 =
             let uu____5161 =
               let uu____5164 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____5164, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____5161 in
           raise uu____5160)
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
            ((let uu____5181 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____5181 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____5184 =
                    let uu____5185 = FStar_Ident.string_of_lid l in
                    let uu____5186 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____5187 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____5185 uu____5186 uu____5187 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____5184);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____5204 = try_lookup_lid env l in
                (match uu____5204 with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____5211 =
                         let uu____5212 = FStar_Options.interactive () in
                         Prims.op_Negation uu____5212 in
                       if uu____5211
                       then
                         let uu____5213 =
                           let uu____5214 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____5215 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____5214 uu____5215 in
                         FStar_Util.print_string uu____5213
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___190_5222 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___190_5222.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___190_5222.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___190_5222.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___190_5222.FStar_Syntax_Syntax.sigattrs)
                           }), false)))
                 | FStar_Pervasives_Native.Some uu____5223 -> ())
            | uu____5228 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5246) ->
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
                                (lid,uu____5261,uu____5262,uu____5263,uu____5264,uu____5265)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____5270 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____5273,uu____5274) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____5278,lbs),uu____5280) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____5293 =
                               let uu____5294 =
                                 let uu____5295 =
                                   let uu____5297 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____5297.FStar_Syntax_Syntax.fv_name in
                                 uu____5295.FStar_Syntax_Syntax.v in
                               uu____5294.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____5293))
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
                               let uu____5308 =
                                 let uu____5310 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____5310.FStar_Syntax_Syntax.fv_name in
                               uu____5308.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___191_5314 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___191_5314.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___191_5314.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___191_5314.FStar_Syntax_Syntax.sigattrs)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____5321 -> ()));
      (let curmod =
         let uu____5323 = current_module env in uu____5323.FStar_Ident.str in
       (let uu____5325 =
          let uu____5336 = get_exported_id_set env curmod in
          let uu____5341 = get_trans_exported_id_set env curmod in
          (uu____5336, uu____5341) in
        match uu____5325 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____5381 = cur_ex eikind in FStar_ST.read uu____5381 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____5389 =
                let uu____5390 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____5390 in
              FStar_ST.write cur_trans_ex_set_ref uu____5389 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____5396 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___192_5408 = env in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___192_5408.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___192_5408.exported_ids);
                    trans_exported_ids = (uu___192_5408.trans_exported_ids);
                    includes = (uu___192_5408.includes);
                    sigaccum = [];
                    sigmap = (uu___192_5408.sigmap);
                    iface = (uu___192_5408.iface);
                    admitted_iface = (uu___192_5408.admitted_iface);
                    expect_typ = (uu___192_5408.expect_typ);
                    docs = (uu___192_5408.docs);
                    remaining_iface_decls =
                      (uu___192_5408.remaining_iface_decls);
                    syntax_only = (uu___192_5408.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____5422 =
       let uu____5424 = FStar_ST.read stack in env :: uu____5424 in
     FStar_ST.write stack uu____5422);
    (let uu___193_5432 = env in
     let uu____5433 = FStar_Util.smap_copy (sigmap env) in
     let uu____5439 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___193_5432.curmodule);
       curmonad = (uu___193_5432.curmonad);
       modules = (uu___193_5432.modules);
       scope_mods = (uu___193_5432.scope_mods);
       exported_ids = (uu___193_5432.exported_ids);
       trans_exported_ids = (uu___193_5432.trans_exported_ids);
       includes = (uu___193_5432.includes);
       sigaccum = (uu___193_5432.sigaccum);
       sigmap = uu____5433;
       iface = (uu___193_5432.iface);
       admitted_iface = (uu___193_5432.admitted_iface);
       expect_typ = (uu___193_5432.expect_typ);
       docs = uu____5439;
       remaining_iface_decls = (uu___193_5432.remaining_iface_decls);
       syntax_only = (uu___193_5432.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____5444  ->
    let uu____5445 = FStar_ST.read stack in
    match uu____5445 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____5458 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____5465 = FStar_ST.read stack in
     match uu____5465 with
     | uu____5470::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____5477 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____5486  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____5500 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____5502 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____5525 = FStar_Util.smap_try_find sm' k in
              match uu____5525 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___194_5541 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___194_5541.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___194_5541.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___194_5541.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___194_5541.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____5542 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____5545 -> ()));
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
              let convert_kind uu___175_5593 =
                match uu___175_5593 with
                | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                | FStar_Parser_Dep.Open_module  -> Open_module in
              FStar_List.map
                (fun uu____5601  ->
                   match uu____5601 with
                   | (lid,kind) -> (lid, (convert_kind kind))) auto_open in
            let namespace_of_module =
              if
                (FStar_List.length mname.FStar_Ident.ns) >
                  (Prims.parse_int "0")
              then
                let uu____5621 =
                  let uu____5624 =
                    FStar_Ident.lid_of_ids mname.FStar_Ident.ns in
                  (uu____5624, Open_namespace) in
                [uu____5621]
              else [] in
            let auto_open2 =
              FStar_List.rev
                (FStar_List.append auto_open1 namespace_of_module) in
            (let uu____5641 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____5641);
            (match () with
             | () ->
                 ((let uu____5646 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____5646);
                  (match () with
                   | () ->
                       ((let uu____5651 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____5651);
                        (match () with
                         | () ->
                             let uu___195_5660 = env1 in
                             let uu____5661 =
                               FStar_List.map
                                 (fun x  -> Open_module_or_namespace x)
                                 auto_open2 in
                             {
                               curmodule =
                                 (FStar_Pervasives_Native.Some mname);
                               curmonad = (uu___195_5660.curmonad);
                               modules = (uu___195_5660.modules);
                               scope_mods = uu____5661;
                               exported_ids = (uu___195_5660.exported_ids);
                               trans_exported_ids =
                                 (uu___195_5660.trans_exported_ids);
                               includes = (uu___195_5660.includes);
                               sigaccum = (uu___195_5660.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___195_5660.expect_typ);
                               docs = (uu___195_5660.docs);
                               remaining_iface_decls =
                                 (uu___195_5660.remaining_iface_decls);
                               syntax_only = (uu___195_5660.syntax_only)
                             }))))) in
          let uu____5665 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____5680  ->
                    match uu____5680 with
                    | (l,uu____5684) -> FStar_Ident.lid_equals l mname)) in
          match uu____5665 with
          | FStar_Pervasives_Native.None  ->
              let uu____5689 = prep env in (uu____5689, false)
          | FStar_Pervasives_Native.Some (uu____5690,m) ->
              ((let uu____5695 =
                  (let uu____5698 = FStar_Options.interactive () in
                   Prims.op_Negation uu____5698) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____5695
                then
                  let uu____5699 =
                    let uu____5700 =
                      let uu____5703 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____5703, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____5700 in
                  raise uu____5699
                else ());
               (let uu____5705 = let uu____5706 = push env in prep uu____5706 in
                (uu____5705, true)))
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
          let uu___196_5716 = env in
          {
            curmodule = (uu___196_5716.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___196_5716.modules);
            scope_mods = (uu___196_5716.scope_mods);
            exported_ids = (uu___196_5716.exported_ids);
            trans_exported_ids = (uu___196_5716.trans_exported_ids);
            includes = (uu___196_5716.includes);
            sigaccum = (uu___196_5716.sigaccum);
            sigmap = (uu___196_5716.sigmap);
            iface = (uu___196_5716.iface);
            admitted_iface = (uu___196_5716.admitted_iface);
            expect_typ = (uu___196_5716.expect_typ);
            docs = (uu___196_5716.docs);
            remaining_iface_decls = (uu___196_5716.remaining_iface_decls);
            syntax_only = (uu___196_5716.syntax_only)
          }
let fail_or env lookup lid =
  let uu____5745 = lookup lid in
  match uu____5745 with
  | FStar_Pervasives_Native.None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____5754  ->
             match uu____5754 with
             | (lid1,uu____5758) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____5767 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____5767
               (FStar_Ident.range_of_lid lid) in
           let uu____5768 = resolve_module_name env modul true in
           match uu____5768 with
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
  let uu____5799 = lookup id in
  match uu____5799 with
  | FStar_Pervasives_Native.None  ->
      raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | FStar_Pervasives_Native.Some r -> r