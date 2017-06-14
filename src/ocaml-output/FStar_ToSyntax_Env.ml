open Prims
type local_binding = (FStar_Ident.ident* FStar_Syntax_Syntax.bv* Prims.bool)
type rec_binding =
  (FStar_Ident.ident* FStar_Ident.lid* FStar_Syntax_Syntax.delta_depth)
type module_abbrev = (FStar_Ident.ident* FStar_Ident.lident)
type open_kind =
  | Open_module
  | Open_namespace
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____12 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____16 -> false
type open_module_or_namespace = (FStar_Ident.lident* open_kind)
type record_or_dc =
  {
  typename: FStar_Ident.lident;
  constrname: FStar_Ident.ident;
  parms: FStar_Syntax_Syntax.binders;
  fields: (FStar_Ident.ident* FStar_Syntax_Syntax.typ) Prims.list;
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
  record_or_dc -> (FStar_Ident.ident* FStar_Syntax_Syntax.typ) Prims.list =
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
    match projectee with | Local_binding _0 -> true | uu____152 -> false
let __proj__Local_binding__item___0: scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0
let uu___is_Rec_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____164 -> false
let __proj__Rec_binding__item___0: scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____176 -> false
let __proj__Module_abbrev__item___0: scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____188 -> false
let __proj__Open_module_or_namespace__item___0:
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_def: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____200 -> false
let __proj__Top_level_def__item___0: scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0
let uu___is_Record_or_dc: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____212 -> false
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
    | uu____224 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____228 -> false
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref
type env =
  {
  curmodule: FStar_Ident.lident option;
  curmonad: FStar_Ident.ident option;
  modules: (FStar_Ident.lident* FStar_Syntax_Syntax.modul) Prims.list;
  scope_mods: scope_mod Prims.list;
  exported_ids: exported_id_set FStar_Util.smap;
  trans_exported_ids: exported_id_set FStar_Util.smap;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap;
  sigaccum: FStar_Syntax_Syntax.sigelts;
  sigmap: (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap;
  iface: Prims.bool;
  admitted_iface: Prims.bool;
  expect_typ: Prims.bool;
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap;
  remaining_iface_decls:
    (FStar_Ident.lident* FStar_Parser_AST.decl Prims.list) Prims.list;
  syntax_only: Prims.bool;}
let __proj__Mkenv__item__curmodule: env -> FStar_Ident.lident option =
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
let __proj__Mkenv__item__curmonad: env -> FStar_Ident.ident option =
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
  env -> (FStar_Ident.lident* FStar_Syntax_Syntax.modul) Prims.list =
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
  env -> (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap =
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
  env -> (FStar_Ident.lident* FStar_Parser_AST.decl Prims.list) Prims.list =
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
  | Term_name of (FStar_Syntax_Syntax.typ* Prims.bool)
  | Eff_name of (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident)
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____924 -> false
let __proj__Term_name__item___0:
  foundname -> (FStar_Syntax_Syntax.typ* Prims.bool) =
  fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____944 -> false
let __proj__Eff_name__item___0:
  foundname -> (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___173_964 = env in
      {
        curmodule = (uu___173_964.curmodule);
        curmonad = (uu___173_964.curmonad);
        modules = (uu___173_964.modules);
        scope_mods = (uu___173_964.scope_mods);
        exported_ids = (uu___173_964.exported_ids);
        trans_exported_ids = (uu___173_964.trans_exported_ids);
        includes = (uu___173_964.includes);
        sigaccum = (uu___173_964.sigaccum);
        sigmap = (uu___173_964.sigmap);
        iface = b;
        admitted_iface = (uu___173_964.admitted_iface);
        expect_typ = (uu___173_964.expect_typ);
        docs = (uu___173_964.docs);
        remaining_iface_decls = (uu___173_964.remaining_iface_decls);
        syntax_only = (uu___173_964.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___174_974 = e in
      {
        curmodule = (uu___174_974.curmodule);
        curmonad = (uu___174_974.curmonad);
        modules = (uu___174_974.modules);
        scope_mods = (uu___174_974.scope_mods);
        exported_ids = (uu___174_974.exported_ids);
        trans_exported_ids = (uu___174_974.trans_exported_ids);
        includes = (uu___174_974.includes);
        sigaccum = (uu___174_974.sigaccum);
        sigmap = (uu___174_974.sigmap);
        iface = (uu___174_974.iface);
        admitted_iface = b;
        expect_typ = (uu___174_974.expect_typ);
        docs = (uu___174_974.docs);
        remaining_iface_decls = (uu___174_974.remaining_iface_decls);
        syntax_only = (uu___174_974.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___175_984 = e in
      {
        curmodule = (uu___175_984.curmodule);
        curmonad = (uu___175_984.curmonad);
        modules = (uu___175_984.modules);
        scope_mods = (uu___175_984.scope_mods);
        exported_ids = (uu___175_984.exported_ids);
        trans_exported_ids = (uu___175_984.trans_exported_ids);
        includes = (uu___175_984.includes);
        sigaccum = (uu___175_984.sigaccum);
        sigmap = (uu___175_984.sigmap);
        iface = (uu___175_984.iface);
        admitted_iface = (uu___175_984.admitted_iface);
        expect_typ = b;
        docs = (uu___175_984.docs);
        remaining_iface_decls = (uu___175_984.remaining_iface_decls);
        syntax_only = (uu___175_984.syntax_only)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____997 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____997 with
      | None  -> []
      | Some exported_id_set ->
          let uu____1001 =
            let uu____1002 = exported_id_set Exported_id_term_type in
            FStar_ST.read uu____1002 in
          FStar_All.pipe_right uu____1001 FStar_Util.set_elements
let open_modules:
  env -> (FStar_Ident.lident* FStar_Syntax_Syntax.modul) Prims.list =
  fun e  -> e.modules
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___176_1020 = e in
      {
        curmodule = (Some l);
        curmonad = (uu___176_1020.curmonad);
        modules = (uu___176_1020.modules);
        scope_mods = (uu___176_1020.scope_mods);
        exported_ids = (uu___176_1020.exported_ids);
        trans_exported_ids = (uu___176_1020.trans_exported_ids);
        includes = (uu___176_1020.includes);
        sigaccum = (uu___176_1020.sigaccum);
        sigmap = (uu___176_1020.sigmap);
        iface = (uu___176_1020.iface);
        admitted_iface = (uu___176_1020.admitted_iface);
        expect_typ = (uu___176_1020.expect_typ);
        docs = (uu___176_1020.docs);
        remaining_iface_decls = (uu___176_1020.remaining_iface_decls);
        syntax_only = (uu___176_1020.syntax_only)
      }
let current_module: env -> FStar_Ident.lident =
  fun env  ->
    match env.curmodule with
    | None  -> failwith "Unset current module"
    | Some m -> m
let iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list option =
  fun env  ->
    fun l  ->
      let uu____1033 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____1049  ->
                match uu____1049 with
                | (m,uu____1054) -> FStar_Ident.lid_equals l m)) in
      match uu____1033 with
      | None  -> None
      | Some (uu____1063,decls) -> Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____1082 =
          FStar_List.partition
            (fun uu____1096  ->
               match uu____1096 with
               | (m,uu____1101) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____1082 with
        | (uu____1104,rest) ->
            let uu___177_1122 = env in
            {
              curmodule = (uu___177_1122.curmodule);
              curmonad = (uu___177_1122.curmonad);
              modules = (uu___177_1122.modules);
              scope_mods = (uu___177_1122.scope_mods);
              exported_ids = (uu___177_1122.exported_ids);
              trans_exported_ids = (uu___177_1122.trans_exported_ids);
              includes = (uu___177_1122.includes);
              sigaccum = (uu___177_1122.sigaccum);
              sigmap = (uu___177_1122.sigmap);
              iface = (uu___177_1122.iface);
              admitted_iface = (uu___177_1122.admitted_iface);
              expect_typ = (uu___177_1122.expect_typ);
              docs = (uu___177_1122.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___177_1122.syntax_only)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | None  -> let uu____1137 = current_module env in qual uu____1137 id
      | Some monad ->
          let uu____1139 =
            let uu____1140 = current_module env in qual uu____1140 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____1139 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___178_1150 = env in
      {
        curmodule = (uu___178_1150.curmodule);
        curmonad = (uu___178_1150.curmonad);
        modules = (uu___178_1150.modules);
        scope_mods = (uu___178_1150.scope_mods);
        exported_ids = (uu___178_1150.exported_ids);
        trans_exported_ids = (uu___178_1150.trans_exported_ids);
        includes = (uu___178_1150.includes);
        sigaccum = (uu___178_1150.sigaccum);
        sigmap = (uu___178_1150.sigmap);
        iface = (uu___178_1150.iface);
        admitted_iface = (uu___178_1150.admitted_iface);
        expect_typ = (uu___178_1150.expect_typ);
        docs = (uu___178_1150.docs);
        remaining_iface_decls = (uu___178_1150.remaining_iface_decls);
        syntax_only = b
      }
let new_sigmap uu____1158 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____1161  ->
    let uu____1162 = new_sigmap () in
    let uu____1164 = new_sigmap () in
    let uu____1166 = new_sigmap () in
    let uu____1172 = new_sigmap () in
    let uu____1178 = new_sigmap () in
    {
      curmodule = None;
      curmonad = None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____1162;
      trans_exported_ids = uu____1164;
      includes = uu____1166;
      sigaccum = [];
      sigmap = uu____1172;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____1178;
      remaining_iface_decls = [];
      syntax_only = false
    }
let sigmap: env -> (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap =
  fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____1196  ->
         match uu____1196 with
         | (m,uu____1200) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___179_1208 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___179_1208.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___180_1209 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___180_1209.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___180_1209.FStar_Syntax_Syntax.sort)
      }
let bv_to_name:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)
let unmangleMap:
  (Prims.string* Prims.string* FStar_Syntax_Syntax.delta_depth*
    FStar_Syntax_Syntax.fv_qual option) Prims.list
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None)]
let unmangleOpName:
  FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) option =
  fun id  ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____1255  ->
           match uu____1255 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____1269 =
                   let uu____1270 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____1270 dd dq in
                 Some uu____1269
               else None) in
    match t with | Some v1 -> Some (v1, false) | None  -> None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____1301 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____1325 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____1336 -> false
let option_of_cont k_ignore uu___146_1355 =
  match uu___146_1355 with
  | Cont_ok a -> Some a
  | Cont_fail  -> None
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
        (fun uu____1400  ->
           match uu____1400 with
           | (f,uu____1405) ->
               if id.FStar_Ident.idText = f.FStar_Ident.idText
               then Some record
               else None) in
    match find1 with | Some r -> cont r | None  -> Cont_ignore
  else Cont_ignore
let get_exported_id_set: env -> Prims.string -> exported_id_set option =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname
let get_trans_exported_id_set: env -> Prims.string -> exported_id_set option
  =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname
let string_of_exported_id_kind: exported_id_kind -> Prims.string =
  fun uu___147_1441  ->
    match uu___147_1441 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___148_1490 =
    match uu___148_1490 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
          let uu____1498 = get_exported_id_set env mname in
          match uu____1498 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____1514 = mex eikind in FStar_ST.read uu____1514 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____1521 = FStar_Util.smap_try_find env.includes mname in
          match uu____1521 with
          | None  -> []
          | Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
          then let uu____1541 = qual modul id in find_in_module uu____1541
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____1544 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___149_1548  ->
    match uu___149_1548 with
    | Exported_id_field  -> true
    | uu____1549 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___150_1638 =
    match uu___150_1638 with
    | (id',uu____1640,uu____1641) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___151_1645 =
    match uu___151_1645 with
    | (id',uu____1647,uu____1648) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1651 = current_module env in FStar_Ident.ids_of_lid uu____1651 in
  let proc uu___152_1656 =
    match uu___152_1656 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____1661) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____1664 = FStar_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____1664 id
    | uu____1667 -> Cont_ignore in
  let rec aux uu___153_1673 =
    match uu___153_1673 with
    | a::q ->
        let uu____1679 = proc a in
        option_of_cont (fun uu____1681  -> aux q) uu____1679
    | [] ->
        let uu____1682 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____1684  -> None) uu____1682 in
  aux env.scope_mods
let found_local_binding r uu____1703 =
  match uu____1703 with
  | (id',x,mut) -> let uu____1710 = bv_to_name x r in (uu____1710, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____1747 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____1747 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found
let try_lookup_id:
  env -> FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) option =
  fun env  ->
    fun id  ->
      let uu____1769 = unmangleOpName id in
      match uu____1769 with
      | Some f -> Some f
      | uu____1783 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1790 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1790) (fun uu____1795  -> Cont_fail)
            (fun uu____1798  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1805  -> fun uu____1806  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1813  -> fun uu____1814  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1866 ->
        let lid = qualify env id in
        let uu____1868 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____1868 with
         | Some r -> let uu____1881 = k_global_def lid r in Some uu____1881
         | None  -> None)
    | None  -> None in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1894 = current_module env in qual uu____1894 id in
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
           let uu____1903 = current_module env in
           FStar_Ident.lid_equals lid uu____1903)
        ||
        (FStar_List.existsb (fun x  -> FStar_Ident.lid_equals lid (fst x))
           env.modules)
let resolve_module_name:
  env -> FStar_Ident.lident -> Prims.bool -> FStar_Ident.lident option =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
        let rec aux uu___154_1928 =
          match uu___154_1928 with
          | [] ->
              let uu____1931 = module_is_defined env lid in
              if uu____1931 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1938 =
                  let uu____1940 = FStar_Ident.path_of_lid ns in
                  let uu____1942 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1940 uu____1942 in
                FStar_Ident.lid_of_path uu____1938
                  (FStar_Ident.range_of_lid lid) in
              let uu____1944 = module_is_defined env new_lid in
              if uu____1944 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1949 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1955::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____1967 =
          let uu____1968 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____1968 in
        if uu____1967
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Syntax_Const.prims_lid
           then ()
           else
             (let uu____1970 =
                let uu____1971 =
                  let uu____1974 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____1974, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____1971 in
              raise uu____1970))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____1982 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____1985 = resolve_module_name env modul_orig true in
          (match uu____1985 with
           | Some modul_res -> fail_if_curmodule env modul_orig modul_res
           | uu____1988 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___155_1996  ->
           match uu___155_1996 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1998 -> false) env.scope_mods
let shorten_module_path:
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list* FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun ids  ->
      fun is_full_path  ->
        let rec aux revns id =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id in
          if namespace_is_open env lid
          then Some ((FStar_List.rev (id :: revns)), [])
          else
            (match revns with
             | [] -> None
             | ns_last_id::rev_ns_prefix ->
                 let uu____2053 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____2053
                   (FStar_Util.map_option
                      (fun uu____2077  ->
                         match uu____2077 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____2094 =
          is_full_path &&
            (let uu____2095 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____2095) in
        if uu____2094
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____2112 = aux ns_rev_prefix ns_last_id in
               (match uu____2112 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____2146 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____2146 with
      | (uu____2151,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____2242::uu____2243 ->
      let uu____2245 =
        let uu____2247 =
          let uu____2248 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____2248 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____2247 true in
      (match uu____2245 with
       | None  -> None
       | Some modul ->
           let uu____2251 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____2253  -> None) uu____2251)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___156_2268 =
  match uu___156_2268 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____2347 = k_global_def lid1 def in cont_of_option k uu____2347 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____2368 = k_local_binding l in
       cont_of_option Cont_fail uu____2368)
    (fun r  ->
       let uu____2371 = k_rec_binding r in
       cont_of_option Cont_fail uu____2371) (fun uu____2373  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____2379,uu____2380,uu____2381,l,uu____2383,uu____2384) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___157_2389  ->
               match uu___157_2389 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____2391,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____2398 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____2402,uu____2403,uu____2404)
        -> None
    | uu____2405 -> None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____2414 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____2418 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____2418 then Some fv else None) in
      FStar_All.pipe_right uu____2414 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____2436 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____2436 ns)
let try_lookup_name:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> foundname option =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___161_2461 =
            match uu___161_2461 with
            | (uu____2465,true ) when exclude_interf -> None
            | (se,uu____2467) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____2469 ->
                     let uu____2478 =
                       let uu____2479 =
                         let uu____2482 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____2482, false) in
                       Term_name uu____2479 in
                     Some uu____2478
                 | FStar_Syntax_Syntax.Sig_datacon uu____2483 ->
                     let uu____2491 =
                       let uu____2492 =
                         let uu____2495 =
                           let uu____2496 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____2496 in
                         (uu____2495, false) in
                       Term_name uu____2492 in
                     Some uu____2491
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____2498,lbs),uu____2500,uu____2501) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____2512 =
                       let uu____2513 =
                         let uu____2516 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____2516, false) in
                       Term_name uu____2513 in
                     Some uu____2512
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____2518,uu____2519) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____2522 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___158_2524  ->
                                  match uu___158_2524 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____2525 -> false))) in
                     if uu____2522
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____2529 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___159_2531  ->
                                      match uu___159_2531 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____2532 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____2535 -> true
                                      | uu____2536 -> false))) in
                         if uu____2529
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____2538 =
                         FStar_Util.find_map quals
                           (fun uu___160_2540  ->
                              match uu___160_2540 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____2543 -> None) in
                       (match uu____2538 with
                        | Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
                        | uu____2555 ->
                            let uu____2557 =
                              let uu____2558 =
                                let uu____2561 =
                                  let uu____2562 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____2562 in
                                (uu____2561, false) in
                              Term_name uu____2558 in
                            Some uu____2557)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2567 ->
                     Some (Eff_name (se, source_lid))
                 | uu____2574 -> None) in
          let k_local_binding r =
            let uu____2586 =
              let uu____2587 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____2587 in
            Some uu____2586 in
          let k_rec_binding uu____2597 =
            match uu____2597 with
            | (id,l,dd) ->
                let uu____2605 =
                  let uu____2606 =
                    let uu____2609 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____2609, false) in
                  Term_name uu____2606 in
                Some uu____2605 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2613 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2613 with
                 | Some f -> Some (Term_name f)
                 | uu____2623 -> None)
            | uu____2627 -> None in
          match found_unmangled with
          | None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
let try_lookup_effect_name':
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident) option
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____2647 = try_lookup_name true exclude_interf env lid in
        match uu____2647 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____2656 -> None
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2667 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2667 with | Some (o,l1) -> Some l1 | uu____2676 -> None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list) option
  =
  fun env  ->
    fun l  ->
      let uu____2690 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2690 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2699;
             FStar_Syntax_Syntax.sigquals = uu____2700;
             FStar_Syntax_Syntax.sigmeta = uu____2701;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2711;
             FStar_Syntax_Syntax.sigquals = uu____2712;
             FStar_Syntax_Syntax.sigmeta = uu____2713;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____2722,uu____2723,uu____2724,uu____2725,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2727;
             FStar_Syntax_Syntax.sigquals = uu____2728;
             FStar_Syntax_Syntax.sigmeta = uu____2729;_},l1)
          -> Some (l1, cattributes)
      | uu____2740 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl option =
  fun env  ->
    fun l  ->
      let uu____2754 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2754 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2760;
             FStar_Syntax_Syntax.sigquals = uu____2761;
             FStar_Syntax_Syntax.sigmeta = uu____2762;_},uu____2763)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2768;
             FStar_Syntax_Syntax.sigquals = uu____2769;
             FStar_Syntax_Syntax.sigmeta = uu____2770;_},uu____2771)
          -> Some ne
      | uu____2775 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2785 = try_lookup_effect_name env lid in
      match uu____2785 with | None  -> false | Some uu____2787 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2795 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2795 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____2801,uu____2802,uu____2803,uu____2804);
             FStar_Syntax_Syntax.sigrng = uu____2805;
             FStar_Syntax_Syntax.sigquals = uu____2806;
             FStar_Syntax_Syntax.sigmeta = uu____2807;_},uu____2808)
          ->
          let rec aux new_name =
            let uu____2819 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2819 with
            | None  -> None
            | Some (s,uu____2829) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____2835,uu____2836,uu____2837,cmp,uu____2839) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2843 -> None) in
          aux l'
      | Some (uu____2844,l') -> Some l'
      | uu____2848 -> None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___162_2869 =
        match uu___162_2869 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2874,uu____2875,uu____2876);
             FStar_Syntax_Syntax.sigrng = uu____2877;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2879;_},uu____2880)
            -> Some quals
        | uu____2883 -> None in
      let uu____2887 =
        resolve_in_open_namespaces' env lid (fun uu____2891  -> None)
          (fun uu____2893  -> None) k_global_def in
      match uu____2887 with | Some quals -> quals | uu____2899 -> []
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul option =
  fun env  ->
    fun path  ->
      let uu____2911 =
        FStar_List.tryFind
          (fun uu____2917  ->
             match uu____2917 with
             | (mlid,modul) ->
                 let uu____2922 = FStar_Ident.path_of_lid mlid in
                 uu____2922 = path) env.modules in
      match uu____2911 with
      | Some (uu____2926,modul) -> Some modul
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___163_2948 =
        match uu___163_2948 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2952,lbs),uu____2954,uu____2955);
             FStar_Syntax_Syntax.sigrng = uu____2956;
             FStar_Syntax_Syntax.sigquals = uu____2957;
             FStar_Syntax_Syntax.sigmeta = uu____2958;_},uu____2959)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2971 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2971
        | uu____2972 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2975  -> None)
        (fun uu____2976  -> None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___164_2995 =
        match uu___164_2995 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____3002,uu____3003);
             FStar_Syntax_Syntax.sigrng = uu____3004;
             FStar_Syntax_Syntax.sigquals = uu____3005;
             FStar_Syntax_Syntax.sigmeta = uu____3006;_},uu____3007)
            ->
            FStar_Util.find_map (snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____3023 -> None)
        | uu____3028 -> None in
      resolve_in_open_namespaces' env lid (fun uu____3035  -> None)
        (fun uu____3038  -> None) k_global_def
let empty_include_smap:
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = new_sigmap ()
let empty_exported_id_smap: exported_id_set FStar_Util.smap = new_sigmap ()
let try_lookup_lid':
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let uu____3065 = try_lookup_name any_val exclude_interf env lid in
          match uu____3065 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____3074 -> None
let try_lookup_lid:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____3094 = try_lookup_lid env l in
      match uu____3094 with
      | None  -> None
      | Some (e,uu____3102) ->
          let uu____3105 =
            let uu____3106 = FStar_Syntax_Subst.compress e in
            uu____3106.FStar_Syntax_Syntax.n in
          (match uu____3105 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____3115 -> None)
let try_lookup_lid_no_resolve:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___181_3126 = env in
        {
          curmodule = (uu___181_3126.curmodule);
          curmonad = (uu___181_3126.curmonad);
          modules = (uu___181_3126.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___181_3126.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___181_3126.sigaccum);
          sigmap = (uu___181_3126.sigmap);
          iface = (uu___181_3126.iface);
          admitted_iface = (uu___181_3126.admitted_iface);
          expect_typ = (uu___181_3126.expect_typ);
          docs = (uu___181_3126.docs);
          remaining_iface_decls = (uu___181_3126.remaining_iface_decls);
          syntax_only = (uu___181_3126.syntax_only)
        } in
      try_lookup_lid env' l
let try_lookup_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___166_3150 =
        match uu___166_3150 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____3154,uu____3155,uu____3156);
             FStar_Syntax_Syntax.sigrng = uu____3157;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____3159;_},uu____3160)
            ->
            let uu____3162 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___165_3164  ->
                      match uu___165_3164 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____3165 -> false)) in
            if uu____3162
            then
              let uu____3167 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____3167
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____3169;
             FStar_Syntax_Syntax.sigrng = uu____3170;
             FStar_Syntax_Syntax.sigquals = uu____3171;
             FStar_Syntax_Syntax.sigmeta = uu____3172;_},uu____3173)
            ->
            let uu____3182 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____3182
        | uu____3183 -> None in
      resolve_in_open_namespaces' env lid (fun uu____3186  -> None)
        (fun uu____3187  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___167_3206 =
        match uu___167_3206 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____3211,uu____3212,uu____3213,uu____3214,datas,uu____3216);
             FStar_Syntax_Syntax.sigrng = uu____3217;
             FStar_Syntax_Syntax.sigquals = uu____3218;
             FStar_Syntax_Syntax.sigmeta = uu____3219;_},uu____3220)
            -> Some datas
        | uu____3227 -> None in
      resolve_in_open_namespaces' env lid (fun uu____3232  -> None)
        (fun uu____3234  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____3268 =
    let uu____3269 =
      let uu____3272 =
        let uu____3274 = FStar_ST.read record_cache in
        FStar_List.hd uu____3274 in
      let uu____3282 = FStar_ST.read record_cache in uu____3272 :: uu____3282 in
    FStar_ST.write record_cache uu____3269 in
  let pop1 uu____3297 =
    let uu____3298 =
      let uu____3301 = FStar_ST.read record_cache in FStar_List.tl uu____3301 in
    FStar_ST.write record_cache uu____3298 in
  let peek uu____3317 =
    let uu____3318 = FStar_ST.read record_cache in FStar_List.hd uu____3318 in
  let insert r =
    let uu____3330 =
      let uu____3333 = let uu____3335 = peek () in r :: uu____3335 in
      let uu____3337 =
        let uu____3340 = FStar_ST.read record_cache in
        FStar_List.tl uu____3340 in
      uu____3333 :: uu____3337 in
    FStar_ST.write record_cache uu____3330 in
  let commit1 uu____3356 =
    let uu____3357 = FStar_ST.read record_cache in
    match uu____3357 with
    | hd1::uu____3365::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____3378 -> failwith "Impossible" in
  let filter1 uu____3384 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____3391 =
           let uu____3394 = FStar_ST.read record_cache in filtered ::
             uu____3394 in
         FStar_ST.write record_cache uu____3391) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____3468 = record_cache_aux_with_filter in
  match uu____3468 with | (aux,uu____3506) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____3545 = record_cache_aux_with_filter in
  match uu____3545 with | (uu____3568,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____3608 = record_cache_aux in
  match uu____3608 with
  | (push1,uu____3628,uu____3629,uu____3630,uu____3631) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3656 = record_cache_aux in
  match uu____3656 with
  | (uu____3675,pop1,uu____3677,uu____3678,uu____3679) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____3705 = record_cache_aux in
  match uu____3705 with
  | (uu____3725,uu____3726,peek,uu____3728,uu____3729) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____3754 = record_cache_aux in
  match uu____3754 with
  | (uu____3773,uu____3774,uu____3775,insert,uu____3777) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____3802 = record_cache_aux in
  match uu____3802 with
  | (uu____3821,uu____3822,uu____3823,uu____3824,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3864) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___168_3873  ->
                   match uu___168_3873 with
                   | FStar_Syntax_Syntax.RecordType uu____3874 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____3879 -> true
                   | uu____3884 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___169_3892  ->
                      match uu___169_3892 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3894,uu____3895,uu____3896,uu____3897,uu____3898);
                          FStar_Syntax_Syntax.sigrng = uu____3899;
                          FStar_Syntax_Syntax.sigquals = uu____3900;
                          FStar_Syntax_Syntax.sigmeta = uu____3901;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3905 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___170_3907  ->
                    match uu___170_3907 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____3911,uu____3912,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____3914;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____3916;_} ->
                        let uu____3921 =
                          let uu____3922 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3922 in
                        (match uu____3921 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3926,t,uu____3928,uu____3929,uu____3930);
                             FStar_Syntax_Syntax.sigrng = uu____3931;
                             FStar_Syntax_Syntax.sigquals = uu____3932;
                             FStar_Syntax_Syntax.sigmeta = uu____3933;_} ->
                             let uu____3937 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3937 with
                              | (formals,uu____3946) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3972  ->
                                            match uu____3972 with
                                            | (x,q) ->
                                                let uu____3980 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3980
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____4011  ->
                                            match uu____4011 with
                                            | (x,q) ->
                                                let uu____4020 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____4020,
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
                                  ((let uu____4032 =
                                      let uu____4034 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____4034 in
                                    FStar_ST.write new_globs uu____4032);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____4050 =
                                            match uu____4050 with
                                            | (id,uu____4056) ->
                                                let modul =
                                                  let uu____4062 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____4062.FStar_Ident.str in
                                                let uu____4063 =
                                                  get_exported_id_set e modul in
                                                (match uu____4063 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____4079 =
                                                         let uu____4080 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____4080 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____4079);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____4087 =
                                                               let uu____4088
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____4088.FStar_Ident.ident in
                                                             uu____4087.FStar_Ident.idText in
                                                           let uu____4090 =
                                                             let uu____4091 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____4091 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____4090))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____4104 -> ())
                    | uu____4105 -> ()))
        | uu____4106 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____4119 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____4119 with
        | (ns,id) ->
            let uu____4129 = peek_record_cache () in
            FStar_Util.find_map uu____4129
              (fun record  ->
                 let uu____4132 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____4135  -> None) uu____4132) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____4136  -> Cont_ignore) (fun uu____4137  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____4140 = find_in_cache fn in
           cont_of_option Cont_ignore uu____4140)
        (fun k  -> fun uu____4143  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let uu____4152 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____4152 with
      | Some r when r.is_record -> Some r
      | uu____4156 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____4167 = try_lookup_record_by_field_name env lid in
        match uu____4167 with
        | Some record' when
            let uu____4170 =
              let uu____4171 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____4171 in
            let uu____4173 =
              let uu____4174 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____4174 in
            uu____4170 = uu____4173 ->
            let uu____4176 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____4178  -> Cont_ok ()) in
            (match uu____4176 with
             | Cont_ok uu____4179 -> true
             | uu____4180 -> false)
        | uu____4182 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) option =
  fun env  ->
    fun fieldname  ->
      let uu____4193 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____4193 with
      | Some r ->
          let uu____4199 =
            let uu____4202 =
              let uu____4203 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____4203
                (FStar_Ident.range_of_lid fieldname) in
            (uu____4202, (r.is_record)) in
          Some uu____4199
      | uu____4206 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____4215  ->
    let uu____4216 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____4216
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____4227  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___171_4236  ->
      match uu___171_4236 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___172_4256 =
            match uu___172_4256 with
            | Rec_binding uu____4257 -> true
            | uu____4258 -> false in
          let this_env =
            let uu___182_4260 = env in
            let uu____4261 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___182_4260.curmodule);
              curmonad = (uu___182_4260.curmonad);
              modules = (uu___182_4260.modules);
              scope_mods = uu____4261;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___182_4260.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___182_4260.sigaccum);
              sigmap = (uu___182_4260.sigmap);
              iface = (uu___182_4260.iface);
              admitted_iface = (uu___182_4260.admitted_iface);
              expect_typ = (uu___182_4260.expect_typ);
              docs = (uu___182_4260.docs);
              remaining_iface_decls = (uu___182_4260.remaining_iface_decls);
              syntax_only = (uu___182_4260.syntax_only)
            } in
          let uu____4263 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____4263 with | None  -> true | Some uu____4269 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___183_4280 = env in
      {
        curmodule = (uu___183_4280.curmodule);
        curmonad = (uu___183_4280.curmonad);
        modules = (uu___183_4280.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___183_4280.exported_ids);
        trans_exported_ids = (uu___183_4280.trans_exported_ids);
        includes = (uu___183_4280.includes);
        sigaccum = (uu___183_4280.sigaccum);
        sigmap = (uu___183_4280.sigmap);
        iface = (uu___183_4280.iface);
        admitted_iface = (uu___183_4280.admitted_iface);
        expect_typ = (uu___183_4280.expect_typ);
        docs = (uu___183_4280.docs);
        remaining_iface_decls = (uu___183_4280.remaining_iface_decls);
        syntax_only = (uu___183_4280.syntax_only)
      }
let push_bv':
  env -> FStar_Ident.ident -> Prims.bool -> (env* FStar_Syntax_Syntax.bv) =
  fun env  ->
    fun x  ->
      fun is_mutable  ->
        let bv =
          FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
            (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun in
        ((push_scope_mod env (Local_binding (x, bv, is_mutable))), bv)
let push_bv_mutable:
  env -> FStar_Ident.ident -> (env* FStar_Syntax_Syntax.bv) =
  fun env  -> fun x  -> push_bv' env x true
let push_bv: env -> FStar_Ident.ident -> (env* FStar_Syntax_Syntax.bv) =
  fun env  -> fun x  -> push_bv' env x false
let push_top_level_rec_binding:
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x in
        let uu____4319 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____4319
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
          | Some (se,uu____4339) ->
              let uu____4342 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____4342 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____4347 =
          let uu____4348 =
            let uu____4351 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____4351, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____4348 in
        raise uu____4347 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____4358 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____4363 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____4369 -> (true, true)
          | uu____4374 -> (false, false) in
        match uu____4358 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____4379 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____4382 =
                     let uu____4383 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____4383 in
                   if uu____4382 then Some l else None) in
            (match uu____4379 with
             | Some l when
                 let uu____4387 = FStar_Options.interactive () in
                 Prims.op_Negation uu____4387 -> err1 l
             | uu____4388 ->
                 (extract_record env globals s;
                  (let uu___184_4393 = env in
                   {
                     curmodule = (uu___184_4393.curmodule);
                     curmonad = (uu___184_4393.curmonad);
                     modules = (uu___184_4393.modules);
                     scope_mods = (uu___184_4393.scope_mods);
                     exported_ids = (uu___184_4393.exported_ids);
                     trans_exported_ids = (uu___184_4393.trans_exported_ids);
                     includes = (uu___184_4393.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___184_4393.sigmap);
                     iface = (uu___184_4393.iface);
                     admitted_iface = (uu___184_4393.admitted_iface);
                     expect_typ = (uu___184_4393.expect_typ);
                     docs = (uu___184_4393.docs);
                     remaining_iface_decls =
                       (uu___184_4393.remaining_iface_decls);
                     syntax_only = (uu___184_4393.syntax_only)
                   }))) in
      let env2 =
        let uu___185_4395 = env1 in
        let uu____4396 = FStar_ST.read globals in
        {
          curmodule = (uu___185_4395.curmodule);
          curmonad = (uu___185_4395.curmonad);
          modules = (uu___185_4395.modules);
          scope_mods = uu____4396;
          exported_ids = (uu___185_4395.exported_ids);
          trans_exported_ids = (uu___185_4395.trans_exported_ids);
          includes = (uu___185_4395.includes);
          sigaccum = (uu___185_4395.sigaccum);
          sigmap = (uu___185_4395.sigmap);
          iface = (uu___185_4395.iface);
          admitted_iface = (uu___185_4395.admitted_iface);
          expect_typ = (uu___185_4395.expect_typ);
          docs = (uu___185_4395.docs);
          remaining_iface_decls = (uu___185_4395.remaining_iface_decls);
          syntax_only = (uu___185_4395.syntax_only)
        } in
      let uu____4401 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4415) ->
            let uu____4420 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____4420)
        | uu____4434 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____4401 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____4464  ->
                   match uu____4464 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____4475 =
                                  let uu____4477 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____4477 in
                                FStar_ST.write globals uu____4475);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____4486 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____4486.FStar_Ident.str in
                                    ((let uu____4488 =
                                        get_exported_id_set env3 modul in
                                      match uu____4488 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____4503 =
                                            let uu____4504 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____4504 in
                                          FStar_ST.write my_exported_ids
                                            uu____4503
                                      | None  -> ());
                                     (match () with
                                      | () ->
                                          FStar_Util.smap_add (sigmap env3)
                                            lid.FStar_Ident.str
                                            (se,
                                              (env3.iface &&
                                                 (Prims.op_Negation
                                                    env3.admitted_iface))))))))));
           (let env4 =
              let uu___186_4516 = env3 in
              let uu____4517 = FStar_ST.read globals in
              {
                curmodule = (uu___186_4516.curmodule);
                curmonad = (uu___186_4516.curmonad);
                modules = (uu___186_4516.modules);
                scope_mods = uu____4517;
                exported_ids = (uu___186_4516.exported_ids);
                trans_exported_ids = (uu___186_4516.trans_exported_ids);
                includes = (uu___186_4516.includes);
                sigaccum = (uu___186_4516.sigaccum);
                sigmap = (uu___186_4516.sigmap);
                iface = (uu___186_4516.iface);
                admitted_iface = (uu___186_4516.admitted_iface);
                expect_typ = (uu___186_4516.expect_typ);
                docs = (uu___186_4516.docs);
                remaining_iface_decls = (uu___186_4516.remaining_iface_decls);
                syntax_only = (uu___186_4516.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____4528 =
        let uu____4531 = resolve_module_name env ns false in
        match uu____4531 with
        | None  ->
            let modules = env.modules in
            let uu____4539 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____4545  ->
                      match uu____4545 with
                      | (m,uu____4549) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____4539
            then (ns, Open_namespace)
            else
              (let uu____4553 =
                 let uu____4554 =
                   let uu____4557 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____4557, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____4554 in
               raise uu____4553)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____4528 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____4571 = resolve_module_name env ns false in
      match uu____4571 with
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____4577 = current_module env1 in
              uu____4577.FStar_Ident.str in
            (let uu____4579 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____4579 with
             | None  -> ()
             | Some incl ->
                 let uu____4592 =
                   let uu____4594 = FStar_ST.read incl in ns1 :: uu____4594 in
                 FStar_ST.write incl uu____4592);
            (match () with
             | () ->
                 let uu____4602 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____4602 with
                  | Some ns_trans_exports ->
                      ((let uu____4615 =
                          let uu____4626 = get_exported_id_set env1 curmod in
                          let uu____4631 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____4626, uu____4631) in
                        match uu____4615 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____4671 = ns_trans_exports k in
                                FStar_ST.read uu____4671 in
                              let ex = cur_exports k in
                              (let uu____4680 =
                                 let uu____4681 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____4681 ns_ex in
                               FStar_ST.write ex uu____4680);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____4691 =
                                     let uu____4692 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____4692 ns_ex in
                                   FStar_ST.write trans_ex uu____4691) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____4698 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____4712 =
                        let uu____4713 =
                          let uu____4716 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____4716, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____4713 in
                      raise uu____4712))))
      | uu____4717 ->
          let uu____4719 =
            let uu____4720 =
              let uu____4723 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____4723, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____4720 in
          raise uu____4719
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____4733 = module_is_defined env l in
        if uu____4733
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____4736 =
             let uu____4737 =
               let uu____4740 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____4740, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____4737 in
           raise uu____4736)
let push_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____4754 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____4754 with
              | None  -> ()
              | Some old_doc ->
                  let uu____4757 =
                    let uu____4758 = FStar_Ident.string_of_lid l in
                    let uu____4759 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____4760 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____4758 uu____4759 uu____4760 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____4757);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____4769 = try_lookup_lid env l in
                (match uu____4769 with
                 | None  ->
                     ((let uu____4776 =
                         let uu____4777 = FStar_Options.interactive () in
                         Prims.op_Negation uu____4777 in
                       if uu____4776
                       then
                         let uu____4778 =
                           let uu____4779 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____4780 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____4779 uu____4780 in
                         FStar_Util.print_string uu____4778
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___187_4786 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___187_4786.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___187_4786.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___187_4786.FStar_Syntax_Syntax.sigmeta)
                           }), false)))
                 | Some uu____4787 -> ())
            | uu____4792 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4804) ->
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
                                (lid,uu____4812,uu____4813,uu____4814,uu____4815,uu____4816)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4821 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4824,uu____4825) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4829,lbs),uu____4831,uu____4832) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4845 =
                               let uu____4846 =
                                 let uu____4847 =
                                   let uu____4852 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4852.FStar_Syntax_Syntax.fv_name in
                                 uu____4847.FStar_Syntax_Syntax.v in
                               uu____4846.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4845))
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
                               let uu____4862 =
                                 let uu____4867 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4867.FStar_Syntax_Syntax.fv_name in
                               uu____4862.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___188_4874 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___188_4874.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___188_4874.FStar_Syntax_Syntax.sigmeta)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4881 -> ()));
      (let curmod =
         let uu____4883 = current_module env in uu____4883.FStar_Ident.str in
       (let uu____4885 =
          let uu____4896 = get_exported_id_set env curmod in
          let uu____4901 = get_trans_exported_id_set env curmod in
          (uu____4896, uu____4901) in
        match uu____4885 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4941 = cur_ex eikind in FStar_ST.read uu____4941 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4949 =
                let uu____4950 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4950 in
              FStar_ST.write cur_trans_ex_set_ref uu____4949 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4956 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___189_4968 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___189_4968.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___189_4968.exported_ids);
                    trans_exported_ids = (uu___189_4968.trans_exported_ids);
                    includes = (uu___189_4968.includes);
                    sigaccum = [];
                    sigmap = (uu___189_4968.sigmap);
                    iface = (uu___189_4968.iface);
                    admitted_iface = (uu___189_4968.admitted_iface);
                    expect_typ = (uu___189_4968.expect_typ);
                    docs = (uu___189_4968.docs);
                    remaining_iface_decls =
                      (uu___189_4968.remaining_iface_decls);
                    syntax_only = (uu___189_4968.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4981 =
       let uu____4983 = FStar_ST.read stack in env :: uu____4983 in
     FStar_ST.write stack uu____4981);
    (let uu___190_4991 = env in
     let uu____4992 = FStar_Util.smap_copy (sigmap env) in
     let uu____4998 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___190_4991.curmodule);
       curmonad = (uu___190_4991.curmonad);
       modules = (uu___190_4991.modules);
       scope_mods = (uu___190_4991.scope_mods);
       exported_ids = (uu___190_4991.exported_ids);
       trans_exported_ids = (uu___190_4991.trans_exported_ids);
       includes = (uu___190_4991.includes);
       sigaccum = (uu___190_4991.sigaccum);
       sigmap = uu____4992;
       iface = (uu___190_4991.iface);
       admitted_iface = (uu___190_4991.admitted_iface);
       expect_typ = (uu___190_4991.expect_typ);
       docs = uu____4998;
       remaining_iface_decls = (uu___190_4991.remaining_iface_decls);
       syntax_only = (uu___190_4991.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____5002  ->
    let uu____5003 = FStar_ST.read stack in
    match uu____5003 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____5016 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____5022 = FStar_ST.read stack in
     match uu____5022 with
     | uu____5027::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____5034 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____5041  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____5053 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____5055 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____5073 = FStar_Util.smap_try_find sm' k in
              match uu____5073 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___191_5089 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___191_5089.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___191_5089.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___191_5089.FStar_Syntax_Syntax.sigmeta)
                          }
                      | uu____5090 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____5093 -> ()));
      env1
let finish_module_or_interface: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
      then check_admits env
      else ();
      finish env modul
let prepare_module_or_interface:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> (env* Prims.bool)
  =
  fun intf  ->
    fun admitted  ->
      fun env  ->
        fun mname  ->
          let prep env1 =
            let open_ns =
              if FStar_Ident.lid_equals mname FStar_Parser_Const.prims_lid
              then []
              else
                if
                  FStar_Util.starts_with "FStar."
                    (FStar_Ident.text_of_lid mname)
                then
                  [FStar_Parser_Const.prims_lid;
                  FStar_Parser_Const.pervasives_lid;
                  FStar_Parser_Const.fstar_ns_lid]
                else
                  [FStar_Parser_Const.prims_lid;
                  FStar_Parser_Const.pervasives_lid;
                  FStar_Parser_Const.st_lid;
                  FStar_Parser_Const.all_lid;
                  FStar_Parser_Const.fstar_ns_lid] in
            let open_ns1 =
              if
                (FStar_List.length mname.FStar_Ident.ns) <>
                  (Prims.parse_int "0")
              then
                let ns = FStar_Ident.lid_of_ids mname.FStar_Ident.ns in ns ::
                  open_ns
              else open_ns in
            (let uu____5139 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____5139);
            (match () with
             | () ->
                 ((let uu____5144 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____5144);
                  (match () with
                   | () ->
                       ((let uu____5149 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____5149);
                        (match () with
                         | () ->
                             let uu___192_5158 = env1 in
                             let uu____5159 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___192_5158.curmonad);
                               modules = (uu___192_5158.modules);
                               scope_mods = uu____5159;
                               exported_ids = (uu___192_5158.exported_ids);
                               trans_exported_ids =
                                 (uu___192_5158.trans_exported_ids);
                               includes = (uu___192_5158.includes);
                               sigaccum = (uu___192_5158.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___192_5158.expect_typ);
                               docs = (uu___192_5158.docs);
                               remaining_iface_decls =
                                 (uu___192_5158.remaining_iface_decls);
                               syntax_only = (uu___192_5158.syntax_only)
                             }))))) in
          let uu____5162 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____5174  ->
                    match uu____5174 with
                    | (l,uu____5178) -> FStar_Ident.lid_equals l mname)) in
          match uu____5162 with
          | None  -> let uu____5183 = prep env in (uu____5183, false)
          | Some (uu____5184,m) ->
              ((let uu____5189 =
                  (let uu____5190 = FStar_Options.interactive () in
                   Prims.op_Negation uu____5190) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____5189
                then
                  let uu____5191 =
                    let uu____5192 =
                      let uu____5195 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____5195, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____5192 in
                  raise uu____5191
                else ());
               (let uu____5197 = let uu____5198 = push env in prep uu____5198 in
                (uu____5197, true)))
let enter_monad_scope: env -> FStar_Ident.ident -> env =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | Some mname' ->
          raise
            (FStar_Errors.Error
               ((Prims.strcat "Trying to define monad "
                   (Prims.strcat mname.FStar_Ident.idText
                      (Prims.strcat ", but already in monad scope "
                         mname'.FStar_Ident.idText))),
                 (mname.FStar_Ident.idRange)))
      | None  ->
          let uu___193_5206 = env in
          {
            curmodule = (uu___193_5206.curmodule);
            curmonad = (Some mname);
            modules = (uu___193_5206.modules);
            scope_mods = (uu___193_5206.scope_mods);
            exported_ids = (uu___193_5206.exported_ids);
            trans_exported_ids = (uu___193_5206.trans_exported_ids);
            includes = (uu___193_5206.includes);
            sigaccum = (uu___193_5206.sigaccum);
            sigmap = (uu___193_5206.sigmap);
            iface = (uu___193_5206.iface);
            admitted_iface = (uu___193_5206.admitted_iface);
            expect_typ = (uu___193_5206.expect_typ);
            docs = (uu___193_5206.docs);
            remaining_iface_decls = (uu___193_5206.remaining_iface_decls);
            syntax_only = (uu___193_5206.syntax_only)
          }
let fail_or env lookup lid =
  let uu____5231 = lookup lid in
  match uu____5231 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____5237  ->
             match uu____5237 with
             | (lid1,uu____5241) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____5250 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____5250
               (FStar_Ident.range_of_lid lid) in
           let uu____5251 = resolve_module_name env modul true in
           match uu____5251 with
           | None  ->
               let opened_modules1 = FStar_String.concat ", " opened_modules in
               FStar_Util.format3
                 "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str opened_modules1
           | Some modul' when
               Prims.op_Negation
                 (FStar_List.existsb (fun m  -> m = modul'.FStar_Ident.str)
                    opened_modules)
               ->
               let opened_modules1 = FStar_String.concat ", " opened_modules in
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 opened_modules1
           | Some modul' ->
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, definition %s not found"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 (lid.FStar_Ident.ident).FStar_Ident.idText) in
      raise (FStar_Errors.Error (msg1, (FStar_Ident.range_of_lid lid)))
  | Some r -> r
let fail_or2 lookup id =
  let uu____5278 = lookup id in
  match uu____5278 with
  | None  ->
      raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r