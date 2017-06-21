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
    match projectee with | Open_module  -> true | uu____13 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____18 -> false
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
    match projectee with | Term_name _0 -> true | uu____962 -> false
let __proj__Term_name__item___0:
  foundname -> (FStar_Syntax_Syntax.typ* Prims.bool) =
  fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____984 -> false
let __proj__Eff_name__item___0:
  foundname -> (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___174_1007 = env in
      {
        curmodule = (uu___174_1007.curmodule);
        curmonad = (uu___174_1007.curmonad);
        modules = (uu___174_1007.modules);
        scope_mods = (uu___174_1007.scope_mods);
        exported_ids = (uu___174_1007.exported_ids);
        trans_exported_ids = (uu___174_1007.trans_exported_ids);
        includes = (uu___174_1007.includes);
        sigaccum = (uu___174_1007.sigaccum);
        sigmap = (uu___174_1007.sigmap);
        iface = b;
        admitted_iface = (uu___174_1007.admitted_iface);
        expect_typ = (uu___174_1007.expect_typ);
        docs = (uu___174_1007.docs);
        remaining_iface_decls = (uu___174_1007.remaining_iface_decls);
        syntax_only = (uu___174_1007.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___175_1020 = e in
      {
        curmodule = (uu___175_1020.curmodule);
        curmonad = (uu___175_1020.curmonad);
        modules = (uu___175_1020.modules);
        scope_mods = (uu___175_1020.scope_mods);
        exported_ids = (uu___175_1020.exported_ids);
        trans_exported_ids = (uu___175_1020.trans_exported_ids);
        includes = (uu___175_1020.includes);
        sigaccum = (uu___175_1020.sigaccum);
        sigmap = (uu___175_1020.sigmap);
        iface = (uu___175_1020.iface);
        admitted_iface = b;
        expect_typ = (uu___175_1020.expect_typ);
        docs = (uu___175_1020.docs);
        remaining_iface_decls = (uu___175_1020.remaining_iface_decls);
        syntax_only = (uu___175_1020.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___176_1033 = e in
      {
        curmodule = (uu___176_1033.curmodule);
        curmonad = (uu___176_1033.curmonad);
        modules = (uu___176_1033.modules);
        scope_mods = (uu___176_1033.scope_mods);
        exported_ids = (uu___176_1033.exported_ids);
        trans_exported_ids = (uu___176_1033.trans_exported_ids);
        includes = (uu___176_1033.includes);
        sigaccum = (uu___176_1033.sigaccum);
        sigmap = (uu___176_1033.sigmap);
        iface = (uu___176_1033.iface);
        admitted_iface = (uu___176_1033.admitted_iface);
        expect_typ = b;
        docs = (uu___176_1033.docs);
        remaining_iface_decls = (uu___176_1033.remaining_iface_decls);
        syntax_only = (uu___176_1033.syntax_only)
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
      | None  -> []
      | Some exported_id_set ->
          let uu____1053 =
            let uu____1054 = exported_id_set Exported_id_term_type in
            FStar_ST.read uu____1054 in
          FStar_All.pipe_right uu____1053 FStar_Util.set_elements
let open_modules:
  env -> (FStar_Ident.lident* FStar_Syntax_Syntax.modul) Prims.list =
  fun e  -> e.modules
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___177_1075 = e in
      {
        curmodule = (Some l);
        curmonad = (uu___177_1075.curmonad);
        modules = (uu___177_1075.modules);
        scope_mods = (uu___177_1075.scope_mods);
        exported_ids = (uu___177_1075.exported_ids);
        trans_exported_ids = (uu___177_1075.trans_exported_ids);
        includes = (uu___177_1075.includes);
        sigaccum = (uu___177_1075.sigaccum);
        sigmap = (uu___177_1075.sigmap);
        iface = (uu___177_1075.iface);
        admitted_iface = (uu___177_1075.admitted_iface);
        expect_typ = (uu___177_1075.expect_typ);
        docs = (uu___177_1075.docs);
        remaining_iface_decls = (uu___177_1075.remaining_iface_decls);
        syntax_only = (uu___177_1075.syntax_only)
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
      let uu____1091 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
<<<<<<< HEAD
             (fun uu____509  ->
                match uu____509 with
                | (m,uu____514) -> FStar_Ident.lid_equals l m)) in
      match uu____490 with
      | None  -> None
      | Some (uu____523,decls) -> Some decls
=======
             (fun uu____1107  ->
                match uu____1107 with
                | (m,uu____1112) -> FStar_Ident.lid_equals l m)) in
      match uu____1091 with
      | None  -> None
      | Some (uu____1121,decls) -> Some decls
>>>>>>> origin/guido_tactics
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
<<<<<<< HEAD
        let uu____542 =
          FStar_List.partition
            (fun uu____559  ->
               match uu____559 with
               | (m,uu____564) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____542 with
        | (uu____567,rest) ->
            let uu___176_585 = env in
            {
              curmodule = (uu___176_585.curmodule);
              curmonad = (uu___176_585.curmonad);
              modules = (uu___176_585.modules);
              scope_mods = (uu___176_585.scope_mods);
              exported_ids = (uu___176_585.exported_ids);
              trans_exported_ids = (uu___176_585.trans_exported_ids);
              includes = (uu___176_585.includes);
              sigaccum = (uu___176_585.sigaccum);
              sigmap = (uu___176_585.sigmap);
              iface = (uu___176_585.iface);
              admitted_iface = (uu___176_585.admitted_iface);
              expect_typ = (uu___176_585.expect_typ);
              docs = (uu___176_585.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___176_585.syntax_only)
=======
        let uu____1143 =
          FStar_List.partition
            (fun uu____1157  ->
               match uu____1157 with
               | (m,uu____1162) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____1143 with
        | (uu____1165,rest) ->
            let uu___178_1183 = env in
            {
              curmodule = (uu___178_1183.curmodule);
              curmonad = (uu___178_1183.curmonad);
              modules = (uu___178_1183.modules);
              scope_mods = (uu___178_1183.scope_mods);
              exported_ids = (uu___178_1183.exported_ids);
              trans_exported_ids = (uu___178_1183.trans_exported_ids);
              includes = (uu___178_1183.includes);
              sigaccum = (uu___178_1183.sigaccum);
              sigmap = (uu___178_1183.sigmap);
              iface = (uu___178_1183.iface);
              admitted_iface = (uu___178_1183.admitted_iface);
              expect_typ = (uu___178_1183.expect_typ);
              docs = (uu___178_1183.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___178_1183.syntax_only)
>>>>>>> origin/guido_tactics
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
<<<<<<< HEAD
      | None  -> let uu____600 = current_module env in qual uu____600 id
      | Some monad ->
          let uu____602 =
            let uu____603 = current_module env in qual uu____603 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____602 id
=======
      | None  -> let uu____1202 = current_module env in qual uu____1202 id
      | Some monad ->
          let uu____1204 =
            let uu____1205 = current_module env in qual uu____1205 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____1204 id
>>>>>>> origin/guido_tactics
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
<<<<<<< HEAD
      let uu___177_613 = env in
      {
        curmodule = (uu___177_613.curmodule);
        curmonad = (uu___177_613.curmonad);
        modules = (uu___177_613.modules);
        scope_mods = (uu___177_613.scope_mods);
        exported_ids = (uu___177_613.exported_ids);
        trans_exported_ids = (uu___177_613.trans_exported_ids);
        includes = (uu___177_613.includes);
        sigaccum = (uu___177_613.sigaccum);
        sigmap = (uu___177_613.sigmap);
        iface = (uu___177_613.iface);
        admitted_iface = (uu___177_613.admitted_iface);
        expect_typ = (uu___177_613.expect_typ);
        docs = (uu___177_613.docs);
        remaining_iface_decls = (uu___177_613.remaining_iface_decls);
        syntax_only = b
      }
let new_sigmap uu____621 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____624  ->
    let uu____625 = new_sigmap () in
    let uu____627 = new_sigmap () in
    let uu____629 = new_sigmap () in
    let uu____635 = new_sigmap () in
    let uu____641 = new_sigmap () in
=======
      let uu___179_1218 = env in
      {
        curmodule = (uu___179_1218.curmodule);
        curmonad = (uu___179_1218.curmonad);
        modules = (uu___179_1218.modules);
        scope_mods = (uu___179_1218.scope_mods);
        exported_ids = (uu___179_1218.exported_ids);
        trans_exported_ids = (uu___179_1218.trans_exported_ids);
        includes = (uu___179_1218.includes);
        sigaccum = (uu___179_1218.sigaccum);
        sigmap = (uu___179_1218.sigmap);
        iface = (uu___179_1218.iface);
        admitted_iface = (uu___179_1218.admitted_iface);
        expect_typ = (uu___179_1218.expect_typ);
        docs = (uu___179_1218.docs);
        remaining_iface_decls = (uu___179_1218.remaining_iface_decls);
        syntax_only = b
      }
let new_sigmap uu____1228 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____1232  ->
    let uu____1233 = new_sigmap () in
    let uu____1235 = new_sigmap () in
    let uu____1237 = new_sigmap () in
    let uu____1243 = new_sigmap () in
    let uu____1249 = new_sigmap () in
>>>>>>> origin/guido_tactics
    {
      curmodule = None;
      curmonad = None;
      modules = [];
      scope_mods = [];
<<<<<<< HEAD
      exported_ids = uu____625;
      trans_exported_ids = uu____627;
      includes = uu____629;
      sigaccum = [];
      sigmap = uu____635;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____641;
=======
      exported_ids = uu____1233;
      trans_exported_ids = uu____1235;
      includes = uu____1237;
      sigaccum = [];
      sigmap = uu____1243;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____1249;
>>>>>>> origin/guido_tactics
      remaining_iface_decls = [];
      syntax_only = false
    }
let sigmap: env -> (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap =
  fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
<<<<<<< HEAD
      (fun uu____662  ->
         match uu____662 with
         | (m,uu____666) ->
=======
      (fun uu____1269  ->
         match uu____1269 with
         | (m,uu____1273) ->
>>>>>>> origin/guido_tactics
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
<<<<<<< HEAD
        let uu___178_674 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___178_674.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___179_675 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___179_675.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___179_675.FStar_Syntax_Syntax.sort)
=======
        let uu___180_1283 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___180_1283.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___181_1284 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___181_1284.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___181_1284.FStar_Syntax_Syntax.sort)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        (fun uu____727  ->
           match uu____727 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____741 =
                   let uu____742 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____742 dd dq in
                 Some uu____741
=======
        (fun uu____1333  ->
           match uu____1333 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____1347 =
                   let uu____1348 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____1348 dd dq in
                 Some uu____1347
>>>>>>> origin/guido_tactics
               else None) in
    match t with | Some v1 -> Some (v1, false) | None  -> None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore
let uu___is_Cont_ok projectee =
<<<<<<< HEAD
  match projectee with | Cont_ok _0 -> true | uu____773 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____797 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____808 -> false
let option_of_cont k_ignore uu___145_827 =
  match uu___145_827 with
=======
  match projectee with | Cont_ok _0 -> true | uu____1381 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____1409 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____1422 -> false
let option_of_cont k_ignore uu___147_1444 =
  match uu___147_1444 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        (fun uu____875  ->
           match uu____875 with
           | (f,uu____880) ->
=======
        (fun uu____1494  ->
           match uu____1494 with
           | (f,uu____1499) ->
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
  fun uu___146_916  ->
    match uu___146_916 with
=======
  fun uu___148_1540  ->
    match uu___148_1540 with
>>>>>>> origin/guido_tactics
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
<<<<<<< HEAD
  let rec aux uu___147_965 =
    match uu___147_965 with
=======
  let rec aux uu___149_1596 =
    match uu___149_1596 with
>>>>>>> origin/guido_tactics
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
<<<<<<< HEAD
          let uu____973 = get_exported_id_set env mname in
          match uu____973 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____989 = mex eikind in FStar_ST.read uu____989 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____996 = FStar_Util.smap_try_find env.includes mname in
          match uu____996 with
=======
          let uu____1604 = get_exported_id_set env mname in
          match uu____1604 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____1620 = mex eikind in FStar_ST.read uu____1620 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____1627 = FStar_Util.smap_try_find env.includes mname in
          match uu____1627 with
>>>>>>> origin/guido_tactics
          | None  -> []
          | Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
<<<<<<< HEAD
          then let uu____1016 = qual modul id in find_in_module uu____1016
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____1019 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___148_1023  ->
    match uu___148_1023 with
    | Exported_id_field  -> true
    | uu____1024 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___149_1113 =
    match uu___149_1113 with
    | (id',uu____1115,uu____1116) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___150_1120 =
    match uu___150_1120 with
    | (id',uu____1122,uu____1123) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1126 = current_module env in FStar_Ident.ids_of_lid uu____1126 in
  let proc uu___151_1131 =
    match uu___151_1131 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____1136) ->
=======
          then let uu____1647 = qual modul id in find_in_module uu____1647
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____1650 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___150_1655  ->
    match uu___150_1655 with
    | Exported_id_field  -> true
    | uu____1656 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___151_1754 =
    match uu___151_1754 with
    | (id',uu____1756,uu____1757) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___152_1761 =
    match uu___152_1761 with
    | (id',uu____1763,uu____1764) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1767 = current_module env in FStar_Ident.ids_of_lid uu____1767 in
  let proc uu___153_1772 =
    match uu___153_1772 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____1777) ->
>>>>>>> origin/guido_tactics
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
<<<<<<< HEAD
        let uu____1139 = FStar_Ident.lid_of_ids curmod_ns in
=======
        let uu____1780 = FStar_Ident.lid_of_ids curmod_ns in
>>>>>>> origin/guido_tactics
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
<<<<<<< HEAD
          env uu____1139 id
    | uu____1144 -> Cont_ignore in
  let rec aux uu___152_1150 =
    match uu___152_1150 with
    | a::q ->
        let uu____1156 = proc a in
        option_of_cont (fun uu____1159  -> aux q) uu____1156
    | [] ->
        let uu____1160 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____1163  -> None) uu____1160 in
  aux env.scope_mods
let found_local_binding r uu____1182 =
  match uu____1182 with
  | (id',x,mut) -> let uu____1189 = bv_to_name x r in (uu____1189, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____1226 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____1226 with
=======
          env uu____1780 id
    | uu____1783 -> Cont_ignore in
  let rec aux uu___154_1789 =
    match uu___154_1789 with
    | a::q ->
        let uu____1795 = proc a in
        option_of_cont (fun uu____1797  -> aux q) uu____1795
    | [] ->
        let uu____1798 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____1800  -> None) uu____1798 in
  aux env.scope_mods
let found_local_binding r uu____1823 =
  match uu____1823 with
  | (id',x,mut) -> let uu____1830 = bv_to_name x r in (uu____1830, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____1872 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____1872 with
>>>>>>> origin/guido_tactics
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found
let try_lookup_id:
  env -> FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) option =
  fun env  ->
    fun id  ->
<<<<<<< HEAD
      let uu____1248 = unmangleOpName id in
      match uu____1248 with
      | Some f -> Some f
      | uu____1262 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1271 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1271) (fun uu____1277  -> Cont_fail)
            (fun uu____1281  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1291  -> fun uu____1292  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1301  -> fun uu____1302  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1354 ->
        let lid = qualify env id in
        let uu____1356 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____1356 with
         | Some r -> let uu____1369 = k_global_def lid r in Some uu____1369
=======
      let uu____1896 = unmangleOpName id in
      match uu____1896 with
      | Some f -> Some f
      | uu____1910 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1917 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1917) (fun uu____1922  -> Cont_fail)
            (fun uu____1925  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1932  -> fun uu____1933  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1940  -> fun uu____1941  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1998 ->
        let lid = qualify env id in
        let uu____2000 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____2000 with
         | Some r -> let uu____2013 = k_global_def lid r in Some uu____2013
>>>>>>> origin/guido_tactics
         | None  -> None)
    | None  -> None in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
<<<<<<< HEAD
      let lid = let uu____1382 = current_module env in qual uu____1382 id in
=======
      let lid = let uu____2026 = current_module env in qual uu____2026 id in
>>>>>>> origin/guido_tactics
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
<<<<<<< HEAD
           let uu____1391 = current_module env in
           FStar_Ident.lid_equals lid uu____1391)
=======
           let uu____2037 = current_module env in
           FStar_Ident.lid_equals lid uu____2037)
>>>>>>> origin/guido_tactics
        ||
        (FStar_List.existsb (fun x  -> FStar_Ident.lid_equals lid (fst x))
           env.modules)
let resolve_module_name:
  env -> FStar_Ident.lident -> Prims.bool -> FStar_Ident.lident option =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
<<<<<<< HEAD
        let rec aux uu___153_1416 =
          match uu___153_1416 with
          | [] ->
              let uu____1419 = module_is_defined env lid in
              if uu____1419 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1426 =
                  let uu____1428 = FStar_Ident.path_of_lid ns in
                  let uu____1430 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1428 uu____1430 in
                FStar_Ident.lid_of_path uu____1426
                  (FStar_Ident.range_of_lid lid) in
              let uu____1432 = module_is_defined env new_lid in
              if uu____1432 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1437 when
=======
        let rec aux uu___155_2065 =
          match uu___155_2065 with
          | [] ->
              let uu____2068 = module_is_defined env lid in
              if uu____2068 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____2075 =
                  let uu____2077 = FStar_Ident.path_of_lid ns in
                  let uu____2079 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____2077 uu____2079 in
                FStar_Ident.lid_of_path uu____2075
                  (FStar_Ident.range_of_lid lid) in
              let uu____2081 = module_is_defined env new_lid in
              if uu____2081 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____2086 when
>>>>>>> origin/guido_tactics
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
<<<<<<< HEAD
          | uu____1441::q -> aux q in
=======
          | uu____2092::q -> aux q in
>>>>>>> origin/guido_tactics
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
<<<<<<< HEAD
        let uu____1453 =
          let uu____1454 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____1454 in
        if uu____1453
=======
        let uu____2107 =
          let uu____2108 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____2108 in
        if uu____2107
>>>>>>> origin/guido_tactics
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Syntax_Const.prims_lid
           then ()
           else
<<<<<<< HEAD
             (let uu____1456 =
                let uu____1457 =
                  let uu____1460 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____1460, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____1457 in
              raise uu____1456))
=======
             (let uu____2110 =
                let uu____2111 =
                  let uu____2114 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____2114, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____2111 in
              raise uu____2110))
>>>>>>> origin/guido_tactics
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
<<<<<<< HEAD
      | uu____1468 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____1471 = resolve_module_name env modul_orig true in
          (match uu____1471 with
           | Some modul_res -> fail_if_curmodule env modul_orig modul_res
           | uu____1474 -> ())
=======
      | uu____2124 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____2127 = resolve_module_name env modul_orig true in
          (match uu____2127 with
           | Some modul_res -> fail_if_curmodule env modul_orig modul_res
           | uu____2130 -> ())
>>>>>>> origin/guido_tactics
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
<<<<<<< HEAD
        (fun uu___154_1484  ->
           match uu___154_1484 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1486 -> false) env.scope_mods
=======
        (fun uu___156_2140  ->
           match uu___156_2140 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____2142 -> false) env.scope_mods
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                 let uu____1541 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____1541
                   (FStar_Util.map_option
                      (fun uu____1568  ->
                         match uu____1568 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____1585 =
          is_full_path &&
            (let uu____1587 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____1587) in
        if uu____1585
=======
                 let uu____2200 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____2200
                   (FStar_Util.map_option
                      (fun uu____2224  ->
                         match uu____2224 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____2241 =
          is_full_path &&
            (let uu____2242 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____2242) in
        if uu____2241
>>>>>>> origin/guido_tactics
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
<<<<<<< HEAD
               let uu____1604 = aux ns_rev_prefix ns_last_id in
               (match uu____1604 with
=======
               let uu____2259 = aux ns_rev_prefix ns_last_id in
               (match uu____2259 with
>>>>>>> origin/guido_tactics
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
<<<<<<< HEAD
      let uu____1638 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____1638 with
      | (uu____1643,short) ->
=======
      let uu____2295 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____2295 with
      | (uu____2300,short) ->
>>>>>>> origin/guido_tactics
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
<<<<<<< HEAD
  | uu____1734::uu____1735 ->
      let uu____1737 =
        let uu____1739 =
          let uu____1740 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____1740 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____1739 true in
      (match uu____1737 with
       | None  -> None
       | Some modul ->
           let uu____1743 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____1746  -> None) uu____1743)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___155_1761 =
  match uu___155_1761 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1840 = k_global_def lid1 def in cont_of_option k uu____1840 in
=======
  | uu____2400::uu____2401 ->
      let uu____2403 =
        let uu____2405 =
          let uu____2406 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____2406 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____2405 true in
      (match uu____2403 with
       | None  -> None
       | Some modul ->
           let uu____2409 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____2411  -> None) uu____2409)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___157_2429 =
  match uu___157_2429 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____2514 = k_global_def lid1 def in cont_of_option k uu____2514 in
>>>>>>> origin/guido_tactics
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
<<<<<<< HEAD
       let uu____1863 = k_local_binding l in
       cont_of_option Cont_fail uu____1863)
    (fun r  ->
       let uu____1868 = k_rec_binding r in
       cont_of_option Cont_fail uu____1868) (fun uu____1871  -> Cont_ignore)
=======
       let uu____2535 = k_local_binding l in
       cont_of_option Cont_fail uu____2535)
    (fun r  ->
       let uu____2538 = k_rec_binding r in
       cont_of_option Cont_fail uu____2538) (fun uu____2540  -> Cont_ignore)
>>>>>>> origin/guido_tactics
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
<<<<<<< HEAD
        (uu____1877,uu____1878,uu____1879,l,uu____1881,uu____1882) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___156_1890  ->
               match uu___156_1890 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1892,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1899 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____1903,uu____1904,uu____1905)
        -> None
    | uu____1906 -> None
=======
        (uu____2547,uu____2548,uu____2549,l,uu____2551,uu____2552) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___158_2557  ->
               match uu___158_2557 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____2559,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____2566 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____2570,uu____2571,uu____2572)
        -> None
    | uu____2573 -> None
>>>>>>> origin/guido_tactics
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
<<<<<<< HEAD
      let uu____1915 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____1922 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____1922 then Some fv else None) in
      FStar_All.pipe_right uu____1915 FStar_Util.must
=======
      let uu____2584 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____2588 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____2588 then Some fv else None) in
      FStar_All.pipe_right uu____2584 FStar_Util.must
>>>>>>> origin/guido_tactics
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
<<<<<<< HEAD
        (let uu____1937 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____1937 ns)
=======
        (let uu____2608 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____2608 ns)
>>>>>>> origin/guido_tactics
let try_lookup_name:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> foundname option =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
<<<<<<< HEAD
          let k_global_def source_lid uu___160_1962 =
            match uu___160_1962 with
            | (uu____1966,true ) when exclude_interf -> None
            | (se,uu____1968) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1970 ->
                     let uu____1979 =
                       let uu____1980 =
                         let uu____1983 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____1983, false) in
                       Term_name uu____1980 in
                     Some uu____1979
                 | FStar_Syntax_Syntax.Sig_datacon uu____1984 ->
                     let uu____1992 =
                       let uu____1993 =
                         let uu____1996 =
                           let uu____1997 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1997 in
                         (uu____1996, false) in
                       Term_name uu____1993 in
                     Some uu____1992
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1999,lbs),uu____2001,uu____2002) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____2013 =
                       let uu____2014 =
                         let uu____2017 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____2017, false) in
                       Term_name uu____2014 in
                     Some uu____2013
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____2019,uu____2020) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____2023 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___157_2026  ->
                                  match uu___157_2026 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____2027 -> false))) in
                     if uu____2023
=======
          let k_global_def source_lid uu___162_2637 =
            match uu___162_2637 with
            | (uu____2641,true ) when exclude_interf -> None
            | (se,uu____2643) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____2645 ->
                     let uu____2654 =
                       let uu____2655 =
                         let uu____2658 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____2658, false) in
                       Term_name uu____2655 in
                     Some uu____2654
                 | FStar_Syntax_Syntax.Sig_datacon uu____2659 ->
                     let uu____2667 =
                       let uu____2668 =
                         let uu____2671 =
                           let uu____2672 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____2672 in
                         (uu____2671, false) in
                       Term_name uu____2668 in
                     Some uu____2667
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____2674,lbs),uu____2676,uu____2677) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____2688 =
                       let uu____2689 =
                         let uu____2692 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____2692, false) in
                       Term_name uu____2689 in
                     Some uu____2688
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____2694,uu____2695) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____2698 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___159_2700  ->
                                  match uu___159_2700 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____2701 -> false))) in
                     if uu____2698
>>>>>>> origin/guido_tactics
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
<<<<<<< HEAD
                         let uu____2031 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___158_2035  ->
                                         match uu___158_2035 with
                                         | FStar_Syntax_Syntax.Projector
                                             uu____2036 -> true
                                         | FStar_Syntax_Syntax.Discriminator
                                             uu____2039 -> true
                                         | uu____2040 -> false)))) in
                         if uu____2031
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____2042 =
                         FStar_Util.find_map quals
                           (fun uu___159_2046  ->
                              match uu___159_2046 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____2049 -> None) in
                       (match uu____2042 with
=======
                         let uu____2705 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___160_2707  ->
                                      match uu___160_2707 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____2708 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____2711 -> true
                                      | uu____2712 -> false))) in
                         if uu____2705
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____2714 =
                         FStar_Util.find_map quals
                           (fun uu___161_2716  ->
                              match uu___161_2716 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____2719 -> None) in
                       (match uu____2714 with
>>>>>>> origin/guido_tactics
                        | Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
<<<<<<< HEAD
                        | uu____2061 ->
                            let uu____2063 =
                              let uu____2064 =
                                let uu____2067 =
                                  let uu____2068 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____2068 in
                                (uu____2067, false) in
                              Term_name uu____2064 in
                            Some uu____2063)
=======
                        | uu____2731 ->
                            let uu____2733 =
                              let uu____2734 =
                                let uu____2737 =
                                  let uu____2738 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____2738 in
                                (uu____2737, false) in
                              Term_name uu____2734 in
                            Some uu____2733)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2073 ->
                     Some (Eff_name (se, source_lid))
                 | uu____2080 -> None) in
          let k_local_binding r =
            let uu____2092 =
              let uu____2093 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____2093 in
            Some uu____2092 in
          let k_rec_binding uu____2103 =
            match uu____2103 with
            | (id,l,dd) ->
                let uu____2111 =
                  let uu____2112 =
                    let uu____2115 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____2115, false) in
                  Term_name uu____2112 in
                Some uu____2111 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2119 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2119 with
                 | Some f -> Some (Term_name f)
                 | uu____2129 -> None)
            | uu____2133 -> None in
=======
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2743 ->
                     Some (Eff_name (se, source_lid))
                 | uu____2750 -> None) in
          let k_local_binding r =
            let uu____2762 =
              let uu____2763 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____2763 in
            Some uu____2762 in
          let k_rec_binding uu____2773 =
            match uu____2773 with
            | (id,l,dd) ->
                let uu____2781 =
                  let uu____2782 =
                    let uu____2785 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____2785, false) in
                  Term_name uu____2782 in
                Some uu____2781 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2789 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2789 with
                 | Some f -> Some (Term_name f)
                 | uu____2799 -> None)
            | uu____2803 -> None in
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        let uu____2153 = try_lookup_name true exclude_interf env lid in
        match uu____2153 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____2162 -> None
=======
        let uu____2826 = try_lookup_name true exclude_interf env lid in
        match uu____2826 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____2835 -> None
>>>>>>> origin/guido_tactics
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
<<<<<<< HEAD
      let uu____2173 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2173 with | Some (o,l1) -> Some l1 | uu____2182 -> None
=======
      let uu____2848 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2848 with | Some (o,l1) -> Some l1 | uu____2857 -> None
>>>>>>> origin/guido_tactics
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list) option
  =
  fun env  ->
    fun l  ->
<<<<<<< HEAD
      let uu____2196 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2196 with
=======
      let uu____2873 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2873 with
>>>>>>> origin/guido_tactics
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
<<<<<<< HEAD
             FStar_Syntax_Syntax.sigrng = uu____2205;
             FStar_Syntax_Syntax.sigquals = uu____2206;
             FStar_Syntax_Syntax.sigmeta = uu____2207;_},l1)
=======
             FStar_Syntax_Syntax.sigrng = uu____2882;
             FStar_Syntax_Syntax.sigquals = uu____2883;
             FStar_Syntax_Syntax.sigmeta = uu____2884;_},l1)
>>>>>>> origin/guido_tactics
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
<<<<<<< HEAD
             FStar_Syntax_Syntax.sigrng = uu____2217;
             FStar_Syntax_Syntax.sigquals = uu____2218;
             FStar_Syntax_Syntax.sigmeta = uu____2219;_},l1)
=======
             FStar_Syntax_Syntax.sigrng = uu____2894;
             FStar_Syntax_Syntax.sigquals = uu____2895;
             FStar_Syntax_Syntax.sigmeta = uu____2896;_},l1)
>>>>>>> origin/guido_tactics
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
<<<<<<< HEAD
               (uu____2228,uu____2229,uu____2230,uu____2231,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2233;
             FStar_Syntax_Syntax.sigquals = uu____2234;
             FStar_Syntax_Syntax.sigmeta = uu____2235;_},l1)
          -> Some (l1, cattributes)
      | uu____2246 -> None
=======
               (uu____2905,uu____2906,uu____2907,uu____2908,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2910;
             FStar_Syntax_Syntax.sigquals = uu____2911;
             FStar_Syntax_Syntax.sigmeta = uu____2912;_},l1)
          -> Some (l1, cattributes)
      | uu____2923 -> None
>>>>>>> origin/guido_tactics
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl option =
  fun env  ->
    fun l  ->
<<<<<<< HEAD
      let uu____2260 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2260 with
=======
      let uu____2939 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2939 with
>>>>>>> origin/guido_tactics
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
<<<<<<< HEAD
             FStar_Syntax_Syntax.sigrng = uu____2266;
             FStar_Syntax_Syntax.sigquals = uu____2267;
             FStar_Syntax_Syntax.sigmeta = uu____2268;_},uu____2269)
=======
             FStar_Syntax_Syntax.sigrng = uu____2945;
             FStar_Syntax_Syntax.sigquals = uu____2946;
             FStar_Syntax_Syntax.sigmeta = uu____2947;_},uu____2948)
>>>>>>> origin/guido_tactics
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
<<<<<<< HEAD
             FStar_Syntax_Syntax.sigrng = uu____2274;
             FStar_Syntax_Syntax.sigquals = uu____2275;
             FStar_Syntax_Syntax.sigmeta = uu____2276;_},uu____2277)
          -> Some ne
      | uu____2281 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2291 = try_lookup_effect_name env lid in
      match uu____2291 with | None  -> false | Some uu____2293 -> true
=======
             FStar_Syntax_Syntax.sigrng = uu____2953;
             FStar_Syntax_Syntax.sigquals = uu____2954;
             FStar_Syntax_Syntax.sigmeta = uu____2955;_},uu____2956)
          -> Some ne
      | uu____2960 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2972 = try_lookup_effect_name env lid in
      match uu____2972 with | None  -> false | Some uu____2974 -> true
>>>>>>> origin/guido_tactics
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
<<<<<<< HEAD
      let uu____2301 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2301 with
=======
      let uu____2984 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2984 with
>>>>>>> origin/guido_tactics
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
<<<<<<< HEAD
               (l',uu____2307,uu____2308,uu____2309,uu____2310);
             FStar_Syntax_Syntax.sigrng = uu____2311;
             FStar_Syntax_Syntax.sigquals = uu____2312;
             FStar_Syntax_Syntax.sigmeta = uu____2313;_},uu____2314)
          ->
          let rec aux new_name =
            let uu____2325 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2325 with
            | None  -> None
            | Some (s,uu____2335) ->
=======
               (l',uu____2990,uu____2991,uu____2992,uu____2993);
             FStar_Syntax_Syntax.sigrng = uu____2994;
             FStar_Syntax_Syntax.sigquals = uu____2995;
             FStar_Syntax_Syntax.sigmeta = uu____2996;_},uu____2997)
          ->
          let rec aux new_name =
            let uu____3008 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____3008 with
            | None  -> None
            | Some (s,uu____3018) ->
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                     (uu____2341,uu____2342,uu____2343,cmp,uu____2345) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2349 -> None) in
          aux l'
      | Some (uu____2350,l') -> Some l'
      | uu____2354 -> None
=======
                     (uu____3024,uu____3025,uu____3026,cmp,uu____3028) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____3032 -> None) in
          aux l'
      | Some (uu____3033,l') -> Some l'
      | uu____3037 -> None
>>>>>>> origin/guido_tactics
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
<<<<<<< HEAD
      let k_global_def lid1 uu___161_2375 =
        match uu___161_2375 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2380,uu____2381,uu____2382);
             FStar_Syntax_Syntax.sigrng = uu____2383;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2385;_},uu____2386)
            -> Some quals
        | uu____2389 -> None in
      let uu____2393 =
        resolve_in_open_namespaces' env lid (fun uu____2398  -> None)
          (fun uu____2401  -> None) k_global_def in
      match uu____2393 with | Some quals -> quals | uu____2407 -> []
=======
      let k_global_def lid1 uu___163_3060 =
        match uu___163_3060 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____3065,uu____3066,uu____3067);
             FStar_Syntax_Syntax.sigrng = uu____3068;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____3070;_},uu____3071)
            -> Some quals
        | uu____3074 -> None in
      let uu____3078 =
        resolve_in_open_namespaces' env lid (fun uu____3082  -> None)
          (fun uu____3084  -> None) k_global_def in
      match uu____3078 with | Some quals -> quals | uu____3090 -> []
>>>>>>> origin/guido_tactics
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul option =
  fun env  ->
    fun path  ->
<<<<<<< HEAD
      let uu____2419 =
        FStar_List.tryFind
          (fun uu____2429  ->
             match uu____2429 with
             | (mlid,modul) ->
                 let uu____2434 = FStar_Ident.path_of_lid mlid in
                 uu____2434 = path) env.modules in
      match uu____2419 with
      | Some (uu____2438,modul) -> Some modul
=======
      let uu____3104 =
        FStar_List.tryFind
          (fun uu____3110  ->
             match uu____3110 with
             | (mlid,modul) ->
                 let uu____3115 = FStar_Ident.path_of_lid mlid in
                 uu____3115 = path) env.modules in
      match uu____3104 with
      | Some (uu____3119,modul) -> Some modul
>>>>>>> origin/guido_tactics
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term option =
  fun env  ->
    fun lid  ->
<<<<<<< HEAD
      let k_global_def lid1 uu___162_2460 =
        match uu___162_2460 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2464,lbs),uu____2466,uu____2467);
             FStar_Syntax_Syntax.sigrng = uu____2468;
             FStar_Syntax_Syntax.sigquals = uu____2469;
             FStar_Syntax_Syntax.sigmeta = uu____2470;_},uu____2471)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2483 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2483
        | uu____2484 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2488  -> None)
        (fun uu____2490  -> None) k_global_def
=======
      let k_global_def lid1 uu___164_3143 =
        match uu___164_3143 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____3147,lbs),uu____3149,uu____3150);
             FStar_Syntax_Syntax.sigrng = uu____3151;
             FStar_Syntax_Syntax.sigquals = uu____3152;
             FStar_Syntax_Syntax.sigmeta = uu____3153;_},uu____3154)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____3166 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____3166
        | uu____3167 -> None in
      resolve_in_open_namespaces' env lid (fun uu____3170  -> None)
        (fun uu____3171  -> None) k_global_def
>>>>>>> origin/guido_tactics
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax option
  =
  fun env  ->
    fun lid  ->
<<<<<<< HEAD
      let k_global_def lid1 uu___163_2509 =
        match uu___163_2509 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2516,uu____2517);
             FStar_Syntax_Syntax.sigrng = uu____2518;
             FStar_Syntax_Syntax.sigquals = uu____2519;
             FStar_Syntax_Syntax.sigmeta = uu____2520;_},uu____2521)
=======
      let k_global_def lid1 uu___165_3192 =
        match uu___165_3192 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____3199,uu____3200);
             FStar_Syntax_Syntax.sigrng = uu____3201;
             FStar_Syntax_Syntax.sigquals = uu____3202;
             FStar_Syntax_Syntax.sigmeta = uu____3203;_},uu____3204)
>>>>>>> origin/guido_tactics
            ->
            FStar_Util.find_map (snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
<<<<<<< HEAD
                 | uu____2539 -> None)
        | uu____2544 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2552  -> None)
        (fun uu____2556  -> None) k_global_def
=======
                 | uu____3220 -> None)
        | uu____3225 -> None in
      resolve_in_open_namespaces' env lid (fun uu____3232  -> None)
        (fun uu____3235  -> None) k_global_def
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
          let uu____2583 = try_lookup_name any_val exclude_interf env lid in
          match uu____2583 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2592 -> None
=======
          let uu____3266 = try_lookup_name any_val exclude_interf env lid in
          match uu____3266 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____3275 -> None
>>>>>>> origin/guido_tactics
let try_lookup_lid:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
<<<<<<< HEAD
      let uu____2612 = try_lookup_lid env l in
      match uu____2612 with
      | None  -> None
      | Some (e,uu____2620) ->
          let uu____2623 =
            let uu____2624 = FStar_Syntax_Subst.compress e in
            uu____2624.FStar_Syntax_Syntax.n in
          (match uu____2623 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2629 -> None)
=======
      let uu____3299 = try_lookup_lid env l in
      match uu____3299 with
      | None  -> None
      | Some (e,uu____3307) ->
          let uu____3310 =
            let uu____3311 = FStar_Syntax_Subst.compress e in
            uu____3311.FStar_Syntax_Syntax.n in
          (match uu____3310 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____3320 -> None)
>>>>>>> origin/guido_tactics
let try_lookup_lid_no_resolve:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  =
  fun env  ->
    fun l  ->
      let env' =
<<<<<<< HEAD
        let uu___180_2640 = env in
        {
          curmodule = (uu___180_2640.curmodule);
          curmonad = (uu___180_2640.curmonad);
          modules = (uu___180_2640.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___180_2640.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___180_2640.sigaccum);
          sigmap = (uu___180_2640.sigmap);
          iface = (uu___180_2640.iface);
          admitted_iface = (uu___180_2640.admitted_iface);
          expect_typ = (uu___180_2640.expect_typ);
          docs = (uu___180_2640.docs);
          remaining_iface_decls = (uu___180_2640.remaining_iface_decls);
          syntax_only = (uu___180_2640.syntax_only)
=======
        let uu___182_3333 = env in
        {
          curmodule = (uu___182_3333.curmodule);
          curmonad = (uu___182_3333.curmonad);
          modules = (uu___182_3333.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___182_3333.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___182_3333.sigaccum);
          sigmap = (uu___182_3333.sigmap);
          iface = (uu___182_3333.iface);
          admitted_iface = (uu___182_3333.admitted_iface);
          expect_typ = (uu___182_3333.expect_typ);
          docs = (uu___182_3333.docs);
          remaining_iface_decls = (uu___182_3333.remaining_iface_decls);
          syntax_only = (uu___182_3333.syntax_only)
>>>>>>> origin/guido_tactics
        } in
      try_lookup_lid env' l
let try_lookup_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv option =
  fun env  ->
    fun lid  ->
<<<<<<< HEAD
      let k_global_def lid1 uu___165_2664 =
        match uu___165_2664 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2668,uu____2669,uu____2670);
             FStar_Syntax_Syntax.sigrng = uu____2671;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2673;_},uu____2674)
            ->
            let uu____2676 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___164_2679  ->
                      match uu___164_2679 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2680 -> false)) in
            if uu____2676
            then
              let uu____2682 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2682
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2684;
             FStar_Syntax_Syntax.sigrng = uu____2685;
             FStar_Syntax_Syntax.sigquals = uu____2686;
             FStar_Syntax_Syntax.sigmeta = uu____2687;_},uu____2688)
            ->
            let uu____2697 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2697
        | uu____2698 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2702  -> None)
        (fun uu____2704  -> None) k_global_def
=======
      let k_global_def lid1 uu___167_3361 =
        match uu___167_3361 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____3365,uu____3366,uu____3367);
             FStar_Syntax_Syntax.sigrng = uu____3368;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____3370;_},uu____3371)
            ->
            let uu____3373 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___166_3375  ->
                      match uu___166_3375 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____3376 -> false)) in
            if uu____3373
            then
              let uu____3378 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____3378
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____3380;
             FStar_Syntax_Syntax.sigrng = uu____3381;
             FStar_Syntax_Syntax.sigquals = uu____3382;
             FStar_Syntax_Syntax.sigmeta = uu____3383;_},uu____3384)
            ->
            let uu____3393 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____3393
        | uu____3394 -> None in
      resolve_in_open_namespaces' env lid (fun uu____3397  -> None)
        (fun uu____3398  -> None) k_global_def
>>>>>>> origin/guido_tactics
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list option =
  fun env  ->
    fun lid  ->
<<<<<<< HEAD
      let k_global_def lid1 uu___166_2723 =
        match uu___166_2723 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2728,uu____2729,uu____2730,uu____2731,datas,uu____2733);
             FStar_Syntax_Syntax.sigrng = uu____2734;
             FStar_Syntax_Syntax.sigquals = uu____2735;
             FStar_Syntax_Syntax.sigmeta = uu____2736;_},uu____2737)
            -> Some datas
        | uu____2744 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2750  -> None)
        (fun uu____2753  -> None) k_global_def
=======
      let k_global_def lid1 uu___168_3419 =
        match uu___168_3419 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____3424,uu____3425,uu____3426,uu____3427,datas,uu____3429);
             FStar_Syntax_Syntax.sigrng = uu____3430;
             FStar_Syntax_Syntax.sigquals = uu____3431;
             FStar_Syntax_Syntax.sigmeta = uu____3432;_},uu____3433)
            -> Some datas
        | uu____3440 -> None in
      resolve_in_open_namespaces' env lid (fun uu____3445  -> None)
        (fun uu____3447  -> None) k_global_def
>>>>>>> origin/guido_tactics
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
<<<<<<< HEAD
  let push1 uu____2787 =
    let uu____2788 =
      let uu____2791 =
        let uu____2793 = FStar_ST.read record_cache in
        FStar_List.hd uu____2793 in
      let uu____2801 = FStar_ST.read record_cache in uu____2791 :: uu____2801 in
    FStar_ST.write record_cache uu____2788 in
  let pop1 uu____2816 =
    let uu____2817 =
      let uu____2820 = FStar_ST.read record_cache in FStar_List.tl uu____2820 in
    FStar_ST.write record_cache uu____2817 in
  let peek uu____2836 =
    let uu____2837 = FStar_ST.read record_cache in FStar_List.hd uu____2837 in
  let insert r =
    let uu____2849 =
      let uu____2852 = let uu____2854 = peek () in r :: uu____2854 in
      let uu____2856 =
        let uu____2859 = FStar_ST.read record_cache in
        FStar_List.tl uu____2859 in
      uu____2852 :: uu____2856 in
    FStar_ST.write record_cache uu____2849 in
  let commit1 uu____2875 =
    let uu____2876 = FStar_ST.read record_cache in
    match uu____2876 with
    | hd1::uu____2884::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2897 -> failwith "Impossible" in
  let filter1 uu____2903 =
    let rc = peek () in
=======
  let push1 uu____3481 =
    let uu____3482 =
      let uu____3485 =
        let uu____3487 = FStar_ST.read record_cache in
        FStar_List.hd uu____3487 in
      let uu____3495 = FStar_ST.read record_cache in uu____3485 :: uu____3495 in
    FStar_ST.write record_cache uu____3482 in
  let pop1 uu____3510 =
    let uu____3511 =
      let uu____3514 = FStar_ST.read record_cache in FStar_List.tl uu____3514 in
    FStar_ST.write record_cache uu____3511 in
  let peek1 uu____3530 =
    let uu____3531 = FStar_ST.read record_cache in FStar_List.hd uu____3531 in
  let insert r =
    let uu____3543 =
      let uu____3546 = let uu____3548 = peek1 () in r :: uu____3548 in
      let uu____3550 =
        let uu____3553 = FStar_ST.read record_cache in
        FStar_List.tl uu____3553 in
      uu____3546 :: uu____3550 in
    FStar_ST.write record_cache uu____3543 in
  let commit1 uu____3569 =
    let uu____3570 = FStar_ST.read record_cache in
    match uu____3570 with
    | hd1::uu____3578::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____3591 -> failwith "Impossible" in
  let filter1 uu____3597 =
    let rc = peek1 () in
>>>>>>> origin/guido_tactics
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
<<<<<<< HEAD
         let uu____2911 =
           let uu____2914 = FStar_ST.read record_cache in filtered ::
             uu____2914 in
         FStar_ST.write record_cache uu____2911) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
=======
         let uu____3604 =
           let uu____3607 = FStar_ST.read record_cache in filtered ::
             uu____3607 in
         FStar_ST.write record_cache uu____3604) in
  let aux = (push1, pop1, peek1, insert, commit1) in (aux, filter1)
>>>>>>> origin/guido_tactics
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
<<<<<<< HEAD
  let uu____2988 = record_cache_aux_with_filter in
  match uu____2988 with | (aux,uu____3026) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____3065 = record_cache_aux_with_filter in
  match uu____3065 with | (uu____3088,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____3128 = record_cache_aux in
  match uu____3128 with
  | (push1,uu____3148,uu____3149,uu____3150,uu____3151) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3176 = record_cache_aux in
  match uu____3176 with
  | (uu____3195,pop1,uu____3197,uu____3198,uu____3199) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____3225 = record_cache_aux in
  match uu____3225 with
  | (uu____3245,uu____3246,peek,uu____3248,uu____3249) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____3274 = record_cache_aux in
  match uu____3274 with
  | (uu____3293,uu____3294,uu____3295,insert,uu____3297) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____3322 = record_cache_aux in
  match uu____3322 with
  | (uu____3341,uu____3342,uu____3343,uu____3344,commit1) -> commit1
=======
  let uu____3681 = record_cache_aux_with_filter in
  match uu____3681 with | (aux,uu____3719) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____3759 = record_cache_aux_with_filter in
  match uu____3759 with | (uu____3782,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____3823 = record_cache_aux in
  match uu____3823 with
  | (push1,uu____3843,uu____3844,uu____3845,uu____3846) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3872 = record_cache_aux in
  match uu____3872 with
  | (uu____3891,pop1,uu____3893,uu____3894,uu____3895) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____3922 = record_cache_aux in
  match uu____3922 with
  | (uu____3942,uu____3943,peek1,uu____3945,uu____3946) -> peek1
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____3972 = record_cache_aux in
  match uu____3972 with
  | (uu____3991,uu____3992,uu____3993,insert,uu____3995) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____4021 = record_cache_aux in
  match uu____4021 with
  | (uu____4040,uu____4041,uu____4042,uu____4043,commit1) -> commit1
>>>>>>> origin/guido_tactics
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
<<<<<<< HEAD
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3384) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___167_3395  ->
                   match uu___167_3395 with
                   | FStar_Syntax_Syntax.RecordType uu____3396 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____3401 -> true
                   | uu____3406 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___168_3424  ->
                      match uu___168_3424 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3426,uu____3427,uu____3428,uu____3429,uu____3430);
                          FStar_Syntax_Syntax.sigrng = uu____3431;
                          FStar_Syntax_Syntax.sigquals = uu____3432;
                          FStar_Syntax_Syntax.sigmeta = uu____3433;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3437 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___169_3469  ->
                    match uu___169_3469 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____3473,uu____3474,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____3476;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____3478;_} ->
                        let uu____3483 =
                          let uu____3484 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3484 in
                        (match uu____3483 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3488,t,uu____3490,uu____3491,uu____3492);
                             FStar_Syntax_Syntax.sigrng = uu____3493;
                             FStar_Syntax_Syntax.sigquals = uu____3494;
                             FStar_Syntax_Syntax.sigmeta = uu____3495;_} ->
                             let uu____3499 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3499 with
                              | (formals,uu____3508) ->
=======
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____4086) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___169_4095  ->
                   match uu___169_4095 with
                   | FStar_Syntax_Syntax.RecordType uu____4096 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____4101 -> true
                   | uu____4106 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___170_4114  ->
                      match uu___170_4114 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____4116,uu____4117,uu____4118,uu____4119,uu____4120);
                          FStar_Syntax_Syntax.sigrng = uu____4121;
                          FStar_Syntax_Syntax.sigquals = uu____4122;
                          FStar_Syntax_Syntax.sigmeta = uu____4123;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____4127 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___171_4129  ->
                    match uu___171_4129 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____4133,uu____4134,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____4136;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____4138;_} ->
                        let uu____4143 =
                          let uu____4144 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____4144 in
                        (match uu____4143 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____4148,t,uu____4150,uu____4151,uu____4152);
                             FStar_Syntax_Syntax.sigrng = uu____4153;
                             FStar_Syntax_Syntax.sigquals = uu____4154;
                             FStar_Syntax_Syntax.sigmeta = uu____4155;_} ->
                             let uu____4159 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____4159 with
                              | (formals,uu____4168) ->
>>>>>>> origin/guido_tactics
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
<<<<<<< HEAD
                                         (fun uu____3538  ->
                                            match uu____3538 with
                                            | (x,q) ->
                                                let uu____3546 =
=======
                                         (fun uu____4194  ->
                                            match uu____4194 with
                                            | (x,q) ->
                                                let uu____4202 =
>>>>>>> origin/guido_tactics
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
<<<<<<< HEAD
                                                if uu____3546
=======
                                                if uu____4202
>>>>>>> origin/guido_tactics
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
<<<<<<< HEAD
                                         (fun uu____3581  ->
                                            match uu____3581 with
                                            | (x,q) ->
                                                let uu____3590 =
=======
                                         (fun uu____4233  ->
                                            match uu____4233 with
                                            | (x,q) ->
                                                let uu____4242 =
>>>>>>> origin/guido_tactics
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
<<<<<<< HEAD
                                                (uu____3590,
=======
                                                (uu____4242,
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                  ((let uu____3602 =
                                      let uu____3604 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3604 in
                                    FStar_ST.write new_globs uu____3602);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3620 =
                                            match uu____3620 with
                                            | (id,uu____3626) ->
                                                let modul =
                                                  let uu____3632 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3632.FStar_Ident.str in
                                                let uu____3633 =
                                                  get_exported_id_set e modul in
                                                (match uu____3633 with
=======
                                  ((let uu____4254 =
                                      let uu____4256 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____4256 in
                                    FStar_ST.write new_globs uu____4254);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____4272 =
                                            match uu____4272 with
                                            | (id,uu____4278) ->
                                                let modul =
                                                  let uu____4284 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____4284.FStar_Ident.str in
                                                let uu____4285 =
                                                  get_exported_id_set e modul in
                                                (match uu____4285 with
>>>>>>> origin/guido_tactics
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
<<<<<<< HEAD
                                                     ((let uu____3649 =
                                                         let uu____3650 =
=======
                                                     ((let uu____4301 =
                                                         let uu____4302 =
>>>>>>> origin/guido_tactics
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
<<<<<<< HEAD
                                                           uu____3650 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3649);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3657 =
                                                               let uu____3658
=======
                                                           uu____4302 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____4301);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____4309 =
                                                               let uu____4310
>>>>>>> origin/guido_tactics
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
<<<<<<< HEAD
                                                               uu____3658.FStar_Ident.ident in
                                                             uu____3657.FStar_Ident.idText in
                                                           let uu____3660 =
                                                             let uu____3661 =
=======
                                                               uu____4310.FStar_Ident.ident in
                                                             uu____4309.FStar_Ident.idText in
                                                           let uu____4312 =
                                                             let uu____4313 =
>>>>>>> origin/guido_tactics
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
<<<<<<< HEAD
                                                               uu____3661 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3660))
=======
                                                               uu____4313 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____4312))
>>>>>>> origin/guido_tactics
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
<<<<<<< HEAD
                         | uu____3674 -> ())
                    | uu____3675 -> ()))
        | uu____3676 -> ()
=======
                         | uu____4326 -> ())
                    | uu____4327 -> ()))
        | uu____4328 -> ()
>>>>>>> origin/guido_tactics
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
<<<<<<< HEAD
        let uu____3689 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3689 with
        | (ns,id) ->
            let uu____3699 = peek_record_cache () in
            FStar_Util.find_map uu____3699
              (fun record  ->
                 let uu____3704 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3709  -> None) uu____3704) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3711  -> Cont_ignore) (fun uu____3713  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3719 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3719)
        (fun k  -> fun uu____3724  -> k)
=======
        let uu____4343 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____4343 with
        | (ns,id) ->
            let uu____4353 = peek_record_cache () in
            FStar_Util.find_map uu____4353
              (fun record  ->
                 let uu____4356 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____4359  -> None) uu____4356) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____4360  -> Cont_ignore) (fun uu____4361  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____4364 = find_in_cache fn in
           cont_of_option Cont_ignore uu____4364)
        (fun k  -> fun uu____4367  -> k)
>>>>>>> origin/guido_tactics
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
<<<<<<< HEAD
      let uu____3733 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3733 with
      | Some r when r.is_record -> Some r
      | uu____3737 -> None
=======
      let uu____4378 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____4378 with
      | Some r when r.is_record -> Some r
      | uu____4382 -> None
>>>>>>> origin/guido_tactics
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
<<<<<<< HEAD
        let uu____3748 = try_lookup_record_by_field_name env lid in
        match uu____3748 with
        | Some record' when
            let uu____3751 =
              let uu____3752 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3752 in
            let uu____3754 =
              let uu____3755 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3755 in
            uu____3751 = uu____3754 ->
            let uu____3757 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3760  -> Cont_ok ()) in
            (match uu____3757 with
             | Cont_ok uu____3761 -> true
             | uu____3762 -> false)
        | uu____3764 -> false
=======
        let uu____4396 = try_lookup_record_by_field_name env lid in
        match uu____4396 with
        | Some record' when
            let uu____4399 =
              let uu____4400 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____4400 in
            let uu____4402 =
              let uu____4403 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____4403 in
            uu____4399 = uu____4402 ->
            let uu____4405 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____4407  -> Cont_ok ()) in
            (match uu____4405 with
             | Cont_ok uu____4408 -> true
             | uu____4409 -> false)
        | uu____4411 -> false
>>>>>>> origin/guido_tactics
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) option =
  fun env  ->
    fun fieldname  ->
<<<<<<< HEAD
      let uu____3775 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3775 with
      | Some r ->
          let uu____3781 =
            let uu____3784 =
              let uu____3785 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3785
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3784, (r.is_record)) in
          Some uu____3781
      | uu____3788 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3797  ->
    let uu____3798 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3798
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3809  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___170_3818  ->
      match uu___170_3818 with
=======
      let uu____4424 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____4424 with
      | Some r ->
          let uu____4430 =
            let uu____4433 =
              let uu____4434 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____4434
                (FStar_Ident.range_of_lid fieldname) in
            (uu____4433, (r.is_record)) in
          Some uu____4430
      | uu____4437 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____4447  ->
    let uu____4448 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____4448
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____4460  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___172_4469  ->
      match uu___172_4469 with
>>>>>>> origin/guido_tactics
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
<<<<<<< HEAD
          let filter_scope_mods uu___171_3838 =
            match uu___171_3838 with
            | Rec_binding uu____3839 -> true
            | uu____3840 -> false in
          let this_env =
            let uu___181_3842 = env in
            let uu____3843 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___181_3842.curmodule);
              curmonad = (uu___181_3842.curmonad);
              modules = (uu___181_3842.modules);
              scope_mods = uu____3843;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___181_3842.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___181_3842.sigaccum);
              sigmap = (uu___181_3842.sigmap);
              iface = (uu___181_3842.iface);
              admitted_iface = (uu___181_3842.admitted_iface);
              expect_typ = (uu___181_3842.expect_typ);
              docs = (uu___181_3842.docs);
              remaining_iface_decls = (uu___181_3842.remaining_iface_decls);
              syntax_only = (uu___181_3842.syntax_only)
            } in
          let uu____3845 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3845 with | None  -> true | Some uu____3851 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___182_3862 = env in
      {
        curmodule = (uu___182_3862.curmodule);
        curmonad = (uu___182_3862.curmonad);
        modules = (uu___182_3862.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___182_3862.exported_ids);
        trans_exported_ids = (uu___182_3862.trans_exported_ids);
        includes = (uu___182_3862.includes);
        sigaccum = (uu___182_3862.sigaccum);
        sigmap = (uu___182_3862.sigmap);
        iface = (uu___182_3862.iface);
        admitted_iface = (uu___182_3862.admitted_iface);
        expect_typ = (uu___182_3862.expect_typ);
        docs = (uu___182_3862.docs);
        remaining_iface_decls = (uu___182_3862.remaining_iface_decls);
        syntax_only = (uu___182_3862.syntax_only)
=======
          let filter_scope_mods uu___173_4493 =
            match uu___173_4493 with
            | Rec_binding uu____4494 -> true
            | uu____4495 -> false in
          let this_env =
            let uu___183_4497 = env in
            let uu____4498 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___183_4497.curmodule);
              curmonad = (uu___183_4497.curmonad);
              modules = (uu___183_4497.modules);
              scope_mods = uu____4498;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___183_4497.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___183_4497.sigaccum);
              sigmap = (uu___183_4497.sigmap);
              iface = (uu___183_4497.iface);
              admitted_iface = (uu___183_4497.admitted_iface);
              expect_typ = (uu___183_4497.expect_typ);
              docs = (uu___183_4497.docs);
              remaining_iface_decls = (uu___183_4497.remaining_iface_decls);
              syntax_only = (uu___183_4497.syntax_only)
            } in
          let uu____4500 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____4500 with | None  -> true | Some uu____4506 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___184_4519 = env in
      {
        curmodule = (uu___184_4519.curmodule);
        curmonad = (uu___184_4519.curmonad);
        modules = (uu___184_4519.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___184_4519.exported_ids);
        trans_exported_ids = (uu___184_4519.trans_exported_ids);
        includes = (uu___184_4519.includes);
        sigaccum = (uu___184_4519.sigaccum);
        sigmap = (uu___184_4519.sigmap);
        iface = (uu___184_4519.iface);
        admitted_iface = (uu___184_4519.admitted_iface);
        expect_typ = (uu___184_4519.expect_typ);
        docs = (uu___184_4519.docs);
        remaining_iface_decls = (uu___184_4519.remaining_iface_decls);
        syntax_only = (uu___184_4519.syntax_only)
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        let uu____3901 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____3901
=======
        let uu____4568 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____4568
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
          | Some (se,uu____3921) ->
              let uu____3924 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____3924 with
=======
          | Some (se,uu____4590) ->
              let uu____4593 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____4593 with
>>>>>>> origin/guido_tactics
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
<<<<<<< HEAD
        let uu____3929 =
          let uu____3930 =
            let uu____3933 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____3933, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____3930 in
        raise uu____3929 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____3940 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3945 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3951 -> (true, true)
          | uu____3956 -> (false, false) in
        match uu____3940 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____3961 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3966 =
                     let uu____3967 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____3967 in
                   if uu____3966 then Some l else None) in
            (match uu____3961 with
             | Some l when
                 let uu____3971 = FStar_Options.interactive () in
                 Prims.op_Negation uu____3971 -> err1 l
             | uu____3972 ->
                 (extract_record env globals s;
                  (let uu___183_3977 = env in
                   {
                     curmodule = (uu___183_3977.curmodule);
                     curmonad = (uu___183_3977.curmonad);
                     modules = (uu___183_3977.modules);
                     scope_mods = (uu___183_3977.scope_mods);
                     exported_ids = (uu___183_3977.exported_ids);
                     trans_exported_ids = (uu___183_3977.trans_exported_ids);
                     includes = (uu___183_3977.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___183_3977.sigmap);
                     iface = (uu___183_3977.iface);
                     admitted_iface = (uu___183_3977.admitted_iface);
                     expect_typ = (uu___183_3977.expect_typ);
                     docs = (uu___183_3977.docs);
                     remaining_iface_decls =
                       (uu___183_3977.remaining_iface_decls);
                     syntax_only = (uu___183_3977.syntax_only)
                   }))) in
      let env2 =
        let uu___184_3979 = env1 in
        let uu____3980 = FStar_ST.read globals in
        {
          curmodule = (uu___184_3979.curmodule);
          curmonad = (uu___184_3979.curmonad);
          modules = (uu___184_3979.modules);
          scope_mods = uu____3980;
          exported_ids = (uu___184_3979.exported_ids);
          trans_exported_ids = (uu___184_3979.trans_exported_ids);
          includes = (uu___184_3979.includes);
          sigaccum = (uu___184_3979.sigaccum);
          sigmap = (uu___184_3979.sigmap);
          iface = (uu___184_3979.iface);
          admitted_iface = (uu___184_3979.admitted_iface);
          expect_typ = (uu___184_3979.expect_typ);
          docs = (uu___184_3979.docs);
          remaining_iface_decls = (uu___184_3979.remaining_iface_decls);
          syntax_only = (uu___184_3979.syntax_only)
        } in
      let uu____3985 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3999) ->
            let uu____4004 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____4004)
        | uu____4019 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____3985 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____4052  ->
                   match uu____4052 with
=======
        let uu____4598 =
          let uu____4599 =
            let uu____4602 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____4602, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____4599 in
        raise uu____4598 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____4609 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____4614 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____4620 -> (true, true)
          | uu____4625 -> (false, false) in
        match uu____4609 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____4630 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____4633 =
                     let uu____4634 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____4634 in
                   if uu____4633 then Some l else None) in
            (match uu____4630 with
             | Some l when
                 let uu____4638 = FStar_Options.interactive () in
                 Prims.op_Negation uu____4638 -> err1 l
             | uu____4639 ->
                 (extract_record env globals s;
                  (let uu___185_4644 = env in
                   {
                     curmodule = (uu___185_4644.curmodule);
                     curmonad = (uu___185_4644.curmonad);
                     modules = (uu___185_4644.modules);
                     scope_mods = (uu___185_4644.scope_mods);
                     exported_ids = (uu___185_4644.exported_ids);
                     trans_exported_ids = (uu___185_4644.trans_exported_ids);
                     includes = (uu___185_4644.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___185_4644.sigmap);
                     iface = (uu___185_4644.iface);
                     admitted_iface = (uu___185_4644.admitted_iface);
                     expect_typ = (uu___185_4644.expect_typ);
                     docs = (uu___185_4644.docs);
                     remaining_iface_decls =
                       (uu___185_4644.remaining_iface_decls);
                     syntax_only = (uu___185_4644.syntax_only)
                   }))) in
      let env2 =
        let uu___186_4646 = env1 in
        let uu____4647 = FStar_ST.read globals in
        {
          curmodule = (uu___186_4646.curmodule);
          curmonad = (uu___186_4646.curmonad);
          modules = (uu___186_4646.modules);
          scope_mods = uu____4647;
          exported_ids = (uu___186_4646.exported_ids);
          trans_exported_ids = (uu___186_4646.trans_exported_ids);
          includes = (uu___186_4646.includes);
          sigaccum = (uu___186_4646.sigaccum);
          sigmap = (uu___186_4646.sigmap);
          iface = (uu___186_4646.iface);
          admitted_iface = (uu___186_4646.admitted_iface);
          expect_typ = (uu___186_4646.expect_typ);
          docs = (uu___186_4646.docs);
          remaining_iface_decls = (uu___186_4646.remaining_iface_decls);
          syntax_only = (uu___186_4646.syntax_only)
        } in
      let uu____4652 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4666) ->
            let uu____4671 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____4671)
        | uu____4685 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____4652 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____4715  ->
                   match uu____4715 with
>>>>>>> origin/guido_tactics
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
<<<<<<< HEAD
                               (let uu____4067 =
                                  let uu____4069 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____4069 in
                                FStar_ST.write globals uu____4067);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____4078 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____4078.FStar_Ident.str in
                                    ((let uu____4080 =
                                        get_exported_id_set env3 modul in
                                      match uu____4080 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____4095 =
                                            let uu____4096 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____4096 in
                                          FStar_ST.write my_exported_ids
                                            uu____4095
=======
                               (let uu____4726 =
                                  let uu____4728 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____4728 in
                                FStar_ST.write globals uu____4726);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____4737 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____4737.FStar_Ident.str in
                                    ((let uu____4739 =
                                        get_exported_id_set env3 modul in
                                      match uu____4739 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____4754 =
                                            let uu____4755 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____4755 in
                                          FStar_ST.write my_exported_ids
                                            uu____4754
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
              let uu___185_4108 = env3 in
              let uu____4109 = FStar_ST.read globals in
              {
                curmodule = (uu___185_4108.curmodule);
                curmonad = (uu___185_4108.curmonad);
                modules = (uu___185_4108.modules);
                scope_mods = uu____4109;
                exported_ids = (uu___185_4108.exported_ids);
                trans_exported_ids = (uu___185_4108.trans_exported_ids);
                includes = (uu___185_4108.includes);
                sigaccum = (uu___185_4108.sigaccum);
                sigmap = (uu___185_4108.sigmap);
                iface = (uu___185_4108.iface);
                admitted_iface = (uu___185_4108.admitted_iface);
                expect_typ = (uu___185_4108.expect_typ);
                docs = (uu___185_4108.docs);
                remaining_iface_decls = (uu___185_4108.remaining_iface_decls);
                syntax_only = (uu___185_4108.syntax_only)
=======
              let uu___187_4767 = env3 in
              let uu____4768 = FStar_ST.read globals in
              {
                curmodule = (uu___187_4767.curmodule);
                curmonad = (uu___187_4767.curmonad);
                modules = (uu___187_4767.modules);
                scope_mods = uu____4768;
                exported_ids = (uu___187_4767.exported_ids);
                trans_exported_ids = (uu___187_4767.trans_exported_ids);
                includes = (uu___187_4767.includes);
                sigaccum = (uu___187_4767.sigaccum);
                sigmap = (uu___187_4767.sigmap);
                iface = (uu___187_4767.iface);
                admitted_iface = (uu___187_4767.admitted_iface);
                expect_typ = (uu___187_4767.expect_typ);
                docs = (uu___187_4767.docs);
                remaining_iface_decls = (uu___187_4767.remaining_iface_decls);
                syntax_only = (uu___187_4767.syntax_only)
>>>>>>> origin/guido_tactics
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
<<<<<<< HEAD
      let uu____4120 =
        let uu____4123 = resolve_module_name env ns false in
        match uu____4123 with
        | None  ->
            let modules = env.modules in
            let uu____4131 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____4140  ->
                      match uu____4140 with
                      | (m,uu____4144) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____4131
            then (ns, Open_namespace)
            else
              (let uu____4148 =
                 let uu____4149 =
                   let uu____4152 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____4152, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____4149 in
               raise uu____4148)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____4120 with
=======
      let uu____4781 =
        let uu____4784 = resolve_module_name env ns false in
        match uu____4784 with
        | None  ->
            let modules = env.modules in
            let uu____4792 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____4798  ->
                      match uu____4798 with
                      | (m,uu____4802) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____4792
            then (ns, Open_namespace)
            else
              (let uu____4806 =
                 let uu____4807 =
                   let uu____4810 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____4810, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____4807 in
               raise uu____4806)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____4781 with
>>>>>>> origin/guido_tactics
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
<<<<<<< HEAD
      let uu____4166 = resolve_module_name env ns false in
      match uu____4166 with
=======
      let uu____4826 = resolve_module_name env ns false in
      match uu____4826 with
>>>>>>> origin/guido_tactics
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
<<<<<<< HEAD
              let uu____4172 = current_module env1 in
              uu____4172.FStar_Ident.str in
            (let uu____4174 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____4174 with
             | None  -> ()
             | Some incl ->
                 let uu____4187 =
                   let uu____4189 = FStar_ST.read incl in ns1 :: uu____4189 in
                 FStar_ST.write incl uu____4187);
            (match () with
             | () ->
                 let uu____4197 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____4197 with
                  | Some ns_trans_exports ->
                      ((let uu____4210 =
                          let uu____4221 = get_exported_id_set env1 curmod in
                          let uu____4226 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____4221, uu____4226) in
                        match uu____4210 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____4266 = ns_trans_exports k in
                                FStar_ST.read uu____4266 in
                              let ex = cur_exports k in
                              (let uu____4275 =
                                 let uu____4276 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____4276 ns_ex in
                               FStar_ST.write ex uu____4275);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____4286 =
                                     let uu____4287 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____4287 ns_ex in
                                   FStar_ST.write trans_ex uu____4286) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____4293 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____4307 =
                        let uu____4308 =
                          let uu____4311 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____4311, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____4308 in
                      raise uu____4307))))
      | uu____4312 ->
          let uu____4314 =
            let uu____4315 =
              let uu____4318 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____4318, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____4315 in
          raise uu____4314
=======
              let uu____4832 = current_module env1 in
              uu____4832.FStar_Ident.str in
            (let uu____4834 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____4834 with
             | None  -> ()
             | Some incl ->
                 let uu____4847 =
                   let uu____4849 = FStar_ST.read incl in ns1 :: uu____4849 in
                 FStar_ST.write incl uu____4847);
            (match () with
             | () ->
                 let uu____4857 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____4857 with
                  | Some ns_trans_exports ->
                      ((let uu____4870 =
                          let uu____4881 = get_exported_id_set env1 curmod in
                          let uu____4886 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____4881, uu____4886) in
                        match uu____4870 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____4926 = ns_trans_exports k in
                                FStar_ST.read uu____4926 in
                              let ex = cur_exports k in
                              (let uu____4935 =
                                 let uu____4936 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____4936 ns_ex in
                               FStar_ST.write ex uu____4935);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____4946 =
                                     let uu____4947 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____4947 ns_ex in
                                   FStar_ST.write trans_ex uu____4946) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____4953 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____4967 =
                        let uu____4968 =
                          let uu____4971 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____4971, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____4968 in
                      raise uu____4967))))
      | uu____4972 ->
          let uu____4974 =
            let uu____4975 =
              let uu____4978 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____4978, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____4975 in
          raise uu____4974
>>>>>>> origin/guido_tactics
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
<<<<<<< HEAD
        let uu____4328 = module_is_defined env l in
        if uu____4328
=======
        let uu____4991 = module_is_defined env l in
        if uu____4991
>>>>>>> origin/guido_tactics
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
<<<<<<< HEAD
          (let uu____4331 =
             let uu____4332 =
               let uu____4335 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____4335, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____4332 in
           raise uu____4331)
=======
          (let uu____4994 =
             let uu____4995 =
               let uu____4998 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____4998, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____4995 in
           raise uu____4994)
>>>>>>> origin/guido_tactics
let push_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
<<<<<<< HEAD
            ((let uu____4349 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____4349 with
              | None  -> ()
              | Some old_doc ->
                  let uu____4352 =
                    let uu____4353 = FStar_Ident.string_of_lid l in
                    let uu____4354 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____4355 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____4353 uu____4354 uu____4355 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____4352);
=======
            ((let uu____5015 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____5015 with
              | None  -> ()
              | Some old_doc ->
                  let uu____5018 =
                    let uu____5019 = FStar_Ident.string_of_lid l in
                    let uu____5020 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____5021 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____5019 uu____5020 uu____5021 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____5018);
>>>>>>> origin/guido_tactics
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
<<<<<<< HEAD
                let uu____4371 = try_lookup_lid env l in
                (match uu____4371 with
                 | None  ->
                     ((let uu____4378 =
                         let uu____4379 = FStar_Options.interactive () in
                         Prims.op_Negation uu____4379 in
                       if uu____4378
                       then
                         let uu____4380 =
                           let uu____4381 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____4382 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____4381 uu____4382 in
                         FStar_Util.print_string uu____4380
=======
                let uu____5031 = try_lookup_lid env l in
                (match uu____5031 with
                 | None  ->
                     ((let uu____5038 =
                         let uu____5039 = FStar_Options.interactive () in
                         Prims.op_Negation uu____5039 in
                       if uu____5038
                       then
                         let uu____5040 =
                           let uu____5041 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____5042 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____5041 uu____5042 in
                         FStar_Util.print_string uu____5040
>>>>>>> origin/guido_tactics
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
<<<<<<< HEAD
                         ((let uu___186_4389 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___186_4389.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___186_4389.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___186_4389.FStar_Syntax_Syntax.sigmeta)
                           }), false)))
                 | Some uu____4390 -> ())
            | uu____4395 -> ()))
=======
                         ((let uu___188_5048 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___188_5048.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___188_5048.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___188_5048.FStar_Syntax_Syntax.sigmeta)
                           }), false)))
                 | Some uu____5049 -> ())
            | uu____5054 -> ()))
>>>>>>> origin/guido_tactics
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
<<<<<<< HEAD
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4411) ->
=======
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____5068) ->
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                                (lid,uu____4426,uu____4427,uu____4428,uu____4429,uu____4430)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4435 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4438,uu____4439) ->
=======
                                (lid,uu____5076,uu____5077,uu____5078,uu____5079,uu____5080)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____5085 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____5088,uu____5089) ->
>>>>>>> origin/guido_tactics
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
<<<<<<< HEAD
                  ((uu____4443,lbs),uu____4445,uu____4446) ->
=======
                  ((uu____5093,lbs),uu____5095,uu____5096) ->
>>>>>>> origin/guido_tactics
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
<<<<<<< HEAD
                             let uu____4461 =
                               let uu____4462 =
                                 let uu____4463 =
                                   let uu____4465 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4465.FStar_Syntax_Syntax.fv_name in
                                 uu____4463.FStar_Syntax_Syntax.v in
                               uu____4462.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4461))
=======
                             let uu____5109 =
                               let uu____5110 =
                                 let uu____5111 =
                                   let uu____5116 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____5116.FStar_Syntax_Syntax.fv_name in
                                 uu____5111.FStar_Syntax_Syntax.v in
                               uu____5110.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____5109))
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                               let uu____4476 =
                                 let uu____4478 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4478.FStar_Syntax_Syntax.fv_name in
                               uu____4476.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___187_4482 = se in
=======
                               let uu____5126 =
                                 let uu____5131 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____5131.FStar_Syntax_Syntax.fv_name in
                               uu____5126.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___189_5138 = se in
>>>>>>> origin/guido_tactics
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                                   (uu___187_4482.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___187_4482.FStar_Syntax_Syntax.sigmeta)
=======
                                   (uu___189_5138.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___189_5138.FStar_Syntax_Syntax.sigmeta)
>>>>>>> origin/guido_tactics
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
<<<<<<< HEAD
              | uu____4489 -> ()));
      (let curmod =
         let uu____4491 = current_module env in uu____4491.FStar_Ident.str in
       (let uu____4493 =
          let uu____4504 = get_exported_id_set env curmod in
          let uu____4509 = get_trans_exported_id_set env curmod in
          (uu____4504, uu____4509) in
        match uu____4493 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4549 = cur_ex eikind in FStar_ST.read uu____4549 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4557 =
                let uu____4558 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4558 in
              FStar_ST.write cur_trans_ex_set_ref uu____4557 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4564 -> ());
=======
              | uu____5145 -> ()));
      (let curmod =
         let uu____5147 = current_module env in uu____5147.FStar_Ident.str in
       (let uu____5149 =
          let uu____5160 = get_exported_id_set env curmod in
          let uu____5165 = get_trans_exported_id_set env curmod in
          (uu____5160, uu____5165) in
        match uu____5149 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____5205 = cur_ex eikind in FStar_ST.read uu____5205 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____5213 =
                let uu____5214 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____5214 in
              FStar_ST.write cur_trans_ex_set_ref uu____5213 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____5220 -> ());
>>>>>>> origin/guido_tactics
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
<<<<<<< HEAD
                  let uu___188_4576 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___188_4576.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___188_4576.exported_ids);
                    trans_exported_ids = (uu___188_4576.trans_exported_ids);
                    includes = (uu___188_4576.includes);
                    sigaccum = [];
                    sigmap = (uu___188_4576.sigmap);
                    iface = (uu___188_4576.iface);
                    admitted_iface = (uu___188_4576.admitted_iface);
                    expect_typ = (uu___188_4576.expect_typ);
                    docs = (uu___188_4576.docs);
                    remaining_iface_decls =
                      (uu___188_4576.remaining_iface_decls);
                    syntax_only = (uu___188_4576.syntax_only)
=======
                  let uu___190_5232 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___190_5232.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___190_5232.exported_ids);
                    trans_exported_ids = (uu___190_5232.trans_exported_ids);
                    includes = (uu___190_5232.includes);
                    sigaccum = [];
                    sigmap = (uu___190_5232.sigmap);
                    iface = (uu___190_5232.iface);
                    admitted_iface = (uu___190_5232.admitted_iface);
                    expect_typ = (uu___190_5232.expect_typ);
                    docs = (uu___190_5232.docs);
                    remaining_iface_decls =
                      (uu___190_5232.remaining_iface_decls);
                    syntax_only = (uu___190_5232.syntax_only)
>>>>>>> origin/guido_tactics
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
<<<<<<< HEAD
    (let uu____4589 =
       let uu____4591 = FStar_ST.read stack in env :: uu____4591 in
     FStar_ST.write stack uu____4589);
    (let uu___189_4599 = env in
     let uu____4600 = FStar_Util.smap_copy (sigmap env) in
     let uu____4606 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___189_4599.curmodule);
       curmonad = (uu___189_4599.curmonad);
       modules = (uu___189_4599.modules);
       scope_mods = (uu___189_4599.scope_mods);
       exported_ids = (uu___189_4599.exported_ids);
       trans_exported_ids = (uu___189_4599.trans_exported_ids);
       includes = (uu___189_4599.includes);
       sigaccum = (uu___189_4599.sigaccum);
       sigmap = uu____4600;
       iface = (uu___189_4599.iface);
       admitted_iface = (uu___189_4599.admitted_iface);
       expect_typ = (uu___189_4599.expect_typ);
       docs = uu____4606;
       remaining_iface_decls = (uu___189_4599.remaining_iface_decls);
       syntax_only = (uu___189_4599.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____4610  ->
    let uu____4611 = FStar_ST.read stack in
    match uu____4611 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4624 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4630 = FStar_ST.read stack in
     match uu____4630 with
     | uu____4635::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4642 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4649  -> pop ()
=======
    (let uu____5246 =
       let uu____5248 = FStar_ST.read stack in env :: uu____5248 in
     FStar_ST.write stack uu____5246);
    (let uu___191_5256 = env in
     let uu____5257 = FStar_Util.smap_copy (sigmap env) in
     let uu____5263 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___191_5256.curmodule);
       curmonad = (uu___191_5256.curmonad);
       modules = (uu___191_5256.modules);
       scope_mods = (uu___191_5256.scope_mods);
       exported_ids = (uu___191_5256.exported_ids);
       trans_exported_ids = (uu___191_5256.trans_exported_ids);
       includes = (uu___191_5256.includes);
       sigaccum = (uu___191_5256.sigaccum);
       sigmap = uu____5257;
       iface = (uu___191_5256.iface);
       admitted_iface = (uu___191_5256.admitted_iface);
       expect_typ = (uu___191_5256.expect_typ);
       docs = uu____5263;
       remaining_iface_decls = (uu___191_5256.remaining_iface_decls);
       syntax_only = (uu___191_5256.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____5268  ->
    let uu____5269 = FStar_ST.read stack in
    match uu____5269 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____5282 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____5289 = FStar_ST.read stack in
     match uu____5289 with
     | uu____5294::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____5301 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____5310  -> pop ()
>>>>>>> origin/guido_tactics
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
<<<<<<< HEAD
        | l::uu____4661 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4663 -> false in
=======
        | l::uu____5324 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____5326 -> false in
>>>>>>> origin/guido_tactics
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
<<<<<<< HEAD
              let uu____4686 = FStar_Util.smap_try_find sm' k in
              match uu____4686 with
=======
              let uu____5344 = FStar_Util.smap_try_find sm' k in
              match uu____5344 with
>>>>>>> origin/guido_tactics
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
<<<<<<< HEAD
                          let uu___190_4702 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___190_4702.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___190_4702.FStar_Syntax_Syntax.sigrng);
=======
                          let uu___192_5360 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___192_5360.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___192_5360.FStar_Syntax_Syntax.sigrng);
>>>>>>> origin/guido_tactics
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
<<<<<<< HEAD
                              (uu___190_4702.FStar_Syntax_Syntax.sigmeta)
                          }
                      | uu____4703 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4706 -> ()));
=======
                              (uu___192_5360.FStar_Syntax_Syntax.sigmeta)
                          }
                      | uu____5361 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____5364 -> ()));
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
            (let uu____4750 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4750);
            (match () with
             | () ->
                 ((let uu____4755 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4755);
                  (match () with
                   | () ->
                       ((let uu____4760 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4760);
                        (match () with
                         | () ->
                             let uu___191_4769 = env1 in
                             let uu____4770 =
=======
            (let uu____5416 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____5416);
            (match () with
             | () ->
                 ((let uu____5421 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____5421);
                  (match () with
                   | () ->
                       ((let uu____5426 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____5426);
                        (match () with
                         | () ->
                             let uu___193_5435 = env1 in
                             let uu____5436 =
>>>>>>> origin/guido_tactics
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
<<<<<<< HEAD
                               curmonad = (uu___191_4769.curmonad);
                               modules = (uu___191_4769.modules);
                               scope_mods = uu____4770;
                               exported_ids = (uu___191_4769.exported_ids);
                               trans_exported_ids =
                                 (uu___191_4769.trans_exported_ids);
                               includes = (uu___191_4769.includes);
                               sigaccum = (uu___191_4769.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___191_4769.expect_typ);
                               docs = (uu___191_4769.docs);
                               remaining_iface_decls =
                                 (uu___191_4769.remaining_iface_decls);
                               syntax_only = (uu___191_4769.syntax_only)
                             }))))) in
          let uu____4774 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4789  ->
                    match uu____4789 with
                    | (l,uu____4793) -> FStar_Ident.lid_equals l mname)) in
          match uu____4774 with
          | None  -> let uu____4798 = prep env in (uu____4798, false)
          | Some (uu____4799,m) ->
              ((let uu____4804 =
                  (let uu____4807 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4807) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4804
                then
                  let uu____4808 =
                    let uu____4809 =
                      let uu____4812 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4812, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4809 in
                  raise uu____4808
                else ());
               (let uu____4814 = let uu____4815 = push env in prep uu____4815 in
                (uu____4814, true)))
=======
                               curmonad = (uu___193_5435.curmonad);
                               modules = (uu___193_5435.modules);
                               scope_mods = uu____5436;
                               exported_ids = (uu___193_5435.exported_ids);
                               trans_exported_ids =
                                 (uu___193_5435.trans_exported_ids);
                               includes = (uu___193_5435.includes);
                               sigaccum = (uu___193_5435.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___193_5435.expect_typ);
                               docs = (uu___193_5435.docs);
                               remaining_iface_decls =
                                 (uu___193_5435.remaining_iface_decls);
                               syntax_only = (uu___193_5435.syntax_only)
                             }))))) in
          let uu____5439 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____5451  ->
                    match uu____5451 with
                    | (l,uu____5455) -> FStar_Ident.lid_equals l mname)) in
          match uu____5439 with
          | None  -> let uu____5460 = prep env in (uu____5460, false)
          | Some (uu____5461,m) ->
              ((let uu____5466 =
                  (let uu____5467 = FStar_Options.interactive () in
                   Prims.op_Negation uu____5467) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____5466
                then
                  let uu____5468 =
                    let uu____5469 =
                      let uu____5472 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____5472, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____5469 in
                  raise uu____5468
                else ());
               (let uu____5474 = let uu____5475 = push env in prep uu____5475 in
                (uu____5474, true)))
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
          let uu___192_4823 = env in
          {
            curmodule = (uu___192_4823.curmodule);
            curmonad = (Some mname);
            modules = (uu___192_4823.modules);
            scope_mods = (uu___192_4823.scope_mods);
            exported_ids = (uu___192_4823.exported_ids);
            trans_exported_ids = (uu___192_4823.trans_exported_ids);
            includes = (uu___192_4823.includes);
            sigaccum = (uu___192_4823.sigaccum);
            sigmap = (uu___192_4823.sigmap);
            iface = (uu___192_4823.iface);
            admitted_iface = (uu___192_4823.admitted_iface);
            expect_typ = (uu___192_4823.expect_typ);
            docs = (uu___192_4823.docs);
            remaining_iface_decls = (uu___192_4823.remaining_iface_decls);
            syntax_only = (uu___192_4823.syntax_only)
          }
let fail_or env lookup lid =
  let uu____4848 = lookup lid in
  match uu____4848 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4857  ->
             match uu____4857 with
             | (lid1,uu____4861) -> FStar_Ident.text_of_lid lid1) env.modules in
=======
          let uu___194_5485 = env in
          {
            curmodule = (uu___194_5485.curmodule);
            curmonad = (Some mname);
            modules = (uu___194_5485.modules);
            scope_mods = (uu___194_5485.scope_mods);
            exported_ids = (uu___194_5485.exported_ids);
            trans_exported_ids = (uu___194_5485.trans_exported_ids);
            includes = (uu___194_5485.includes);
            sigaccum = (uu___194_5485.sigaccum);
            sigmap = (uu___194_5485.sigmap);
            iface = (uu___194_5485.iface);
            admitted_iface = (uu___194_5485.admitted_iface);
            expect_typ = (uu___194_5485.expect_typ);
            docs = (uu___194_5485.docs);
            remaining_iface_decls = (uu___194_5485.remaining_iface_decls);
            syntax_only = (uu___194_5485.syntax_only)
          }
let fail_or env lookup lid =
  let uu____5514 = lookup lid in
  match uu____5514 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____5520  ->
             match uu____5520 with
             | (lid1,uu____5524) -> FStar_Ident.text_of_lid lid1) env.modules in
>>>>>>> origin/guido_tactics
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
<<<<<<< HEAD
             let uu____4868 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4868
               (FStar_Ident.range_of_lid lid) in
           let uu____4869 = resolve_module_name env modul true in
           match uu____4869 with
=======
             let uu____5533 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____5533
               (FStar_Ident.range_of_lid lid) in
           let uu____5534 = resolve_module_name env modul true in
           match uu____5534 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
  let uu____4897 = lookup id in
  match uu____4897 with
=======
  let uu____5564 = lookup id in
  match uu____5564 with
>>>>>>> origin/guido_tactics
  | None  ->
      raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r