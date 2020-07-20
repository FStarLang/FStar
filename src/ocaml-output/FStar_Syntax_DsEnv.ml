open Prims
type used_marker = Prims.bool FStar_ST.ref
type local_binding =
  (FStar_Ident.ident * FStar_Syntax_Syntax.bv * used_marker)
type rec_binding =
  (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth *
    used_marker)
type module_abbrev = (FStar_Ident.ident * FStar_Ident.lident)
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_module -> true | uu____55 -> false
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_namespace -> true | uu____61 -> false
type open_module_or_namespace = (FStar_Ident.lident * open_kind)
type record_or_dc =
  {
  typename: FStar_Ident.lident ;
  constrname: FStar_Ident.ident ;
  parms: FStar_Syntax_Syntax.binders ;
  fields: (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list ;
  is_private: Prims.bool ;
  is_record: Prims.bool }
let (__proj__Mkrecord_or_dc__item__typename :
  record_or_dc -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        typename
let (__proj__Mkrecord_or_dc__item__constrname :
  record_or_dc -> FStar_Ident.ident) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        constrname
let (__proj__Mkrecord_or_dc__item__parms :
  record_or_dc -> FStar_Syntax_Syntax.binders) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        parms
let (__proj__Mkrecord_or_dc__item__fields :
  record_or_dc -> (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        fields
let (__proj__Mkrecord_or_dc__item__is_private : record_or_dc -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        is_private
let (__proj__Mkrecord_or_dc__item__is_record : record_or_dc -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        is_record
type scope_mod =
  | Local_binding of local_binding 
  | Rec_binding of rec_binding 
  | Module_abbrev of module_abbrev 
  | Open_module_or_namespace of open_module_or_namespace 
  | Top_level_def of FStar_Ident.ident 
  | Record_or_dc of record_or_dc 
let (uu___is_Local_binding : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Local_binding _0 -> true | uu____256 -> false
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee -> match projectee with | Local_binding _0 -> _0
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Rec_binding _0 -> true | uu____269 -> false
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee -> match projectee with | Rec_binding _0 -> _0
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Module_abbrev _0 -> true | uu____282 -> false
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee -> match projectee with | Module_abbrev _0 -> _0
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____295 -> false
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee -> match projectee with | Open_module_or_namespace _0 -> _0
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Top_level_def _0 -> true | uu____308 -> false
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Top_level_def _0 -> _0
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_or_dc _0 -> true | uu____321 -> false
let (__proj__Record_or_dc__item___0 : scope_mod -> record_or_dc) =
  fun projectee -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStar_Util.set
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field 
let (uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_term_type -> true | uu____335 -> false
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_field -> true | uu____341 -> false
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref
type env =
  {
  curmodule: FStar_Ident.lident FStar_Pervasives_Native.option ;
  curmonad: FStar_Ident.ident FStar_Pervasives_Native.option ;
  modules: (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list ;
  scope_mods: scope_mod Prims.list ;
  exported_ids: exported_id_set FStar_Util.smap ;
  trans_exported_ids: exported_id_set FStar_Util.smap ;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap ;
  sigaccum: FStar_Syntax_Syntax.sigelts ;
  sigmap: (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap ;
  iface: Prims.bool ;
  admitted_iface: Prims.bool ;
  expect_typ: Prims.bool ;
  remaining_iface_decls:
    (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list ;
  syntax_only: Prims.bool ;
  ds_hooks: dsenv_hooks ;
  dep_graph: FStar_Parser_Dep.deps }
and dsenv_hooks =
  {
  ds_push_open_hook: env -> open_module_or_namespace -> unit ;
  ds_push_include_hook: env -> FStar_Ident.lident -> unit ;
  ds_push_module_abbrev_hook:
    env -> FStar_Ident.ident -> FStar_Ident.lident -> unit }
let (__proj__Mkenv__item__curmodule :
  env -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmodule
let (__proj__Mkenv__item__curmonad :
  env -> FStar_Ident.ident FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmonad
let (__proj__Mkenv__item__modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> modules
let (__proj__Mkenv__item__scope_mods : env -> scope_mod Prims.list) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> scope_mods
let (__proj__Mkenv__item__exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> exported_ids
let (__proj__Mkenv__item__trans_exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> trans_exported_ids
let (__proj__Mkenv__item__includes :
  env -> FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> includes
let (__proj__Mkenv__item__sigaccum : env -> FStar_Syntax_Syntax.sigelts) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> sigaccum
let (__proj__Mkenv__item__sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> sigmap
let (__proj__Mkenv__item__iface : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> iface
let (__proj__Mkenv__item__admitted_iface : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> admitted_iface
let (__proj__Mkenv__item__expect_typ : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> expect_typ
let (__proj__Mkenv__item__remaining_iface_decls :
  env -> (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> remaining_iface_decls
let (__proj__Mkenv__item__syntax_only : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> syntax_only
let (__proj__Mkenv__item__ds_hooks : env -> dsenv_hooks) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> ds_hooks
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> dep_graph
let (__proj__Mkdsenv_hooks__item__ds_push_open_hook :
  dsenv_hooks -> env -> open_module_or_namespace -> unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_open_hook
let (__proj__Mkdsenv_hooks__item__ds_push_include_hook :
  dsenv_hooks -> env -> FStar_Ident.lident -> unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_include_hook
let (__proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook :
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_module_abbrev_hook
type 'a withenv = env -> ('a * env)
let (default_ds_hooks : dsenv_hooks) =
  {
    ds_push_open_hook = (fun uu____1694 -> fun uu____1695 -> ());
    ds_push_include_hook = (fun uu____1698 -> fun uu____1699 -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1703 -> fun uu____1704 -> fun uu____1705 -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Term_name _0 -> true | uu____1738 -> false
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee -> match projectee with | Term_name _0 -> _0
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Eff_name _0 -> true | uu____1773 -> false
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee -> match projectee with | Eff_name _0 -> _0
let (set_iface : env -> Prims.bool -> env) =
  fun env1 ->
    fun b ->
      let uu___125_1802 = env1 in
      {
        curmodule = (uu___125_1802.curmodule);
        curmonad = (uu___125_1802.curmonad);
        modules = (uu___125_1802.modules);
        scope_mods = (uu___125_1802.scope_mods);
        exported_ids = (uu___125_1802.exported_ids);
        trans_exported_ids = (uu___125_1802.trans_exported_ids);
        includes = (uu___125_1802.includes);
        sigaccum = (uu___125_1802.sigaccum);
        sigmap = (uu___125_1802.sigmap);
        iface = b;
        admitted_iface = (uu___125_1802.admitted_iface);
        expect_typ = (uu___125_1802.expect_typ);
        remaining_iface_decls = (uu___125_1802.remaining_iface_decls);
        syntax_only = (uu___125_1802.syntax_only);
        ds_hooks = (uu___125_1802.ds_hooks);
        dep_graph = (uu___125_1802.dep_graph)
      }
let (iface : env -> Prims.bool) = fun e -> e.iface
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___130_1818 = e in
      {
        curmodule = (uu___130_1818.curmodule);
        curmonad = (uu___130_1818.curmonad);
        modules = (uu___130_1818.modules);
        scope_mods = (uu___130_1818.scope_mods);
        exported_ids = (uu___130_1818.exported_ids);
        trans_exported_ids = (uu___130_1818.trans_exported_ids);
        includes = (uu___130_1818.includes);
        sigaccum = (uu___130_1818.sigaccum);
        sigmap = (uu___130_1818.sigmap);
        iface = (uu___130_1818.iface);
        admitted_iface = b;
        expect_typ = (uu___130_1818.expect_typ);
        remaining_iface_decls = (uu___130_1818.remaining_iface_decls);
        syntax_only = (uu___130_1818.syntax_only);
        ds_hooks = (uu___130_1818.ds_hooks);
        dep_graph = (uu___130_1818.dep_graph)
      }
let (admitted_iface : env -> Prims.bool) = fun e -> e.admitted_iface
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___135_1834 = e in
      {
        curmodule = (uu___135_1834.curmodule);
        curmonad = (uu___135_1834.curmonad);
        modules = (uu___135_1834.modules);
        scope_mods = (uu___135_1834.scope_mods);
        exported_ids = (uu___135_1834.exported_ids);
        trans_exported_ids = (uu___135_1834.trans_exported_ids);
        includes = (uu___135_1834.includes);
        sigaccum = (uu___135_1834.sigaccum);
        sigmap = (uu___135_1834.sigmap);
        iface = (uu___135_1834.iface);
        admitted_iface = (uu___135_1834.admitted_iface);
        expect_typ = b;
        remaining_iface_decls = (uu___135_1834.remaining_iface_decls);
        syntax_only = (uu___135_1834.syntax_only);
        ds_hooks = (uu___135_1834.ds_hooks);
        dep_graph = (uu___135_1834.dep_graph)
      }
let (expect_typ : env -> Prims.bool) = fun e -> e.expect_typ
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type]
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env1 ->
    fun lid ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____1855 =
        FStar_Util.smap_try_find env1.trans_exported_ids module_name in
      match uu____1855 with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some exported_id_set1 ->
          let uu____1866 =
            let uu____1869 = exported_id_set1 Exported_id_term_type in
            FStar_ST.op_Bang uu____1869 in
          FStar_All.pipe_right uu____1866 FStar_Util.set_elements
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e -> e.modules
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env1 ->
    FStar_List.filter_map
      (fun uu___0_1913 ->
         match uu___0_1913 with
         | Open_module_or_namespace (lid, _info) ->
             FStar_Pervasives_Native.Some lid
         | uu____1918 -> FStar_Pervasives_Native.None) env1.scope_mods
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e ->
    fun l ->
      let uu___154_1929 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___154_1929.curmonad);
        modules = (uu___154_1929.modules);
        scope_mods = (uu___154_1929.scope_mods);
        exported_ids = (uu___154_1929.exported_ids);
        trans_exported_ids = (uu___154_1929.trans_exported_ids);
        includes = (uu___154_1929.includes);
        sigaccum = (uu___154_1929.sigaccum);
        sigmap = (uu___154_1929.sigmap);
        iface = (uu___154_1929.iface);
        admitted_iface = (uu___154_1929.admitted_iface);
        expect_typ = (uu___154_1929.expect_typ);
        remaining_iface_decls = (uu___154_1929.remaining_iface_decls);
        syntax_only = (uu___154_1929.syntax_only);
        ds_hooks = (uu___154_1929.ds_hooks);
        dep_graph = (uu___154_1929.dep_graph)
      }
let (current_module : env -> FStar_Ident.lident) =
  fun env1 ->
    match env1.curmodule with
    | FStar_Pervasives_Native.None -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
let (iface_decls :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____1950 =
        FStar_All.pipe_right env1.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____1984 ->
                match uu____1984 with
                | (m, uu____1992) -> FStar_Ident.lid_equals l m)) in
      match uu____1950 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2009, decls) ->
          FStar_Pervasives_Native.Some decls
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env1 ->
    fun l ->
      fun ds ->
        let uu____2042 =
          FStar_List.partition
            (fun uu____2072 ->
               match uu____2072 with
               | (m, uu____2080) -> FStar_Ident.lid_equals l m)
            env1.remaining_iface_decls in
        match uu____2042 with
        | (uu____2085, rest) ->
            let uu___179_2119 = env1 in
            {
              curmodule = (uu___179_2119.curmodule);
              curmonad = (uu___179_2119.curmonad);
              modules = (uu___179_2119.modules);
              scope_mods = (uu___179_2119.scope_mods);
              exported_ids = (uu___179_2119.exported_ids);
              trans_exported_ids = (uu___179_2119.trans_exported_ids);
              includes = (uu___179_2119.includes);
              sigaccum = (uu___179_2119.sigaccum);
              sigmap = (uu___179_2119.sigmap);
              iface = (uu___179_2119.iface);
              admitted_iface = (uu___179_2119.admitted_iface);
              expect_typ = (uu___179_2119.expect_typ);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___179_2119.syntax_only);
              ds_hooks = (uu___179_2119.ds_hooks);
              dep_graph = (uu___179_2119.dep_graph)
            }
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Ident.qual_id
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env1 ->
    fun id ->
      match env1.curmonad with
      | FStar_Pervasives_Native.None ->
          let uu____2146 = current_module env1 in qual uu____2146 id
      | FStar_Pervasives_Native.Some monad ->
          let uu____2148 =
            let uu____2149 = current_module env1 in qual uu____2149 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2148 id
let (syntax_only : env -> Prims.bool) = fun env1 -> env1.syntax_only
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env1 ->
    fun b ->
      let uu___189_2165 = env1 in
      {
        curmodule = (uu___189_2165.curmodule);
        curmonad = (uu___189_2165.curmonad);
        modules = (uu___189_2165.modules);
        scope_mods = (uu___189_2165.scope_mods);
        exported_ids = (uu___189_2165.exported_ids);
        trans_exported_ids = (uu___189_2165.trans_exported_ids);
        includes = (uu___189_2165.includes);
        sigaccum = (uu___189_2165.sigaccum);
        sigmap = (uu___189_2165.sigmap);
        iface = (uu___189_2165.iface);
        admitted_iface = (uu___189_2165.admitted_iface);
        expect_typ = (uu___189_2165.expect_typ);
        remaining_iface_decls = (uu___189_2165.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___189_2165.ds_hooks);
        dep_graph = (uu___189_2165.dep_graph)
      }
let (ds_hooks : env -> dsenv_hooks) = fun env1 -> env1.ds_hooks
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env1 ->
    fun hooks ->
      let uu___194_2181 = env1 in
      {
        curmodule = (uu___194_2181.curmodule);
        curmonad = (uu___194_2181.curmonad);
        modules = (uu___194_2181.modules);
        scope_mods = (uu___194_2181.scope_mods);
        exported_ids = (uu___194_2181.exported_ids);
        trans_exported_ids = (uu___194_2181.trans_exported_ids);
        includes = (uu___194_2181.includes);
        sigaccum = (uu___194_2181.sigaccum);
        sigmap = (uu___194_2181.sigmap);
        iface = (uu___194_2181.iface);
        admitted_iface = (uu___194_2181.admitted_iface);
        expect_typ = (uu___194_2181.expect_typ);
        remaining_iface_decls = (uu___194_2181.remaining_iface_decls);
        syntax_only = (uu___194_2181.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___194_2181.dep_graph)
      }
let new_sigmap : 'uuuuuu2186 . unit -> 'uuuuuu2186 FStar_Util.smap =
  fun uu____2193 -> FStar_Util.smap_create (Prims.of_int (100))
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps ->
    let uu____2199 = new_sigmap () in
    let uu____2204 = new_sigmap () in
    let uu____2209 = new_sigmap () in
    let uu____2220 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2199;
      trans_exported_ids = uu____2204;
      includes = uu____2209;
      sigaccum = [];
      sigmap = uu____2220;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env1 -> env1.dep_graph
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env1 ->
    fun ds ->
      let uu___201_2256 = env1 in
      {
        curmodule = (uu___201_2256.curmodule);
        curmonad = (uu___201_2256.curmonad);
        modules = (uu___201_2256.modules);
        scope_mods = (uu___201_2256.scope_mods);
        exported_ids = (uu___201_2256.exported_ids);
        trans_exported_ids = (uu___201_2256.trans_exported_ids);
        includes = (uu___201_2256.includes);
        sigaccum = (uu___201_2256.sigaccum);
        sigmap = (uu___201_2256.sigmap);
        iface = (uu___201_2256.iface);
        admitted_iface = (uu___201_2256.admitted_iface);
        expect_typ = (uu___201_2256.expect_typ);
        remaining_iface_decls = (uu___201_2256.remaining_iface_decls);
        syntax_only = (uu___201_2256.syntax_only);
        ds_hooks = (uu___201_2256.ds_hooks);
        dep_graph = ds
      }
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env1 -> env1.sigmap
let (has_all_in_scope : env -> Prims.bool) =
  fun env1 ->
    FStar_List.existsb
      (fun uu____2280 ->
         match uu____2280 with
         | (m, uu____2286) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
      env1.modules
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv ->
    fun r ->
      let id = FStar_Ident.set_id_range r bv.FStar_Syntax_Syntax.ppname in
      let uu___211_2298 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___211_2298.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___211_2298.FStar_Syntax_Syntax.sort)
      }
let (bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun bv ->
    fun r ->
      let uu____2309 = set_bv_range bv r in
      FStar_Syntax_Syntax.bv_to_name uu____2309
let (unmangleMap :
  (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth *
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) Prims.list)
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.delta_equational,
    FStar_Pervasives_Native.None)]
let (unmangleOpName :
  FStar_Ident.ident ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun id ->
    FStar_Util.find_map unmangleMap
      (fun uu____2382 ->
         match uu____2382 with
         | (x, y, dd, dq) ->
             let uu____2403 =
               let uu____2404 = FStar_Ident.string_of_id id in uu____2404 = x in
             if uu____2403
             then
               let uu____2407 =
                 let uu____2408 =
                   let uu____2409 = FStar_Ident.range_of_id id in
                   FStar_Ident.lid_of_path ["Prims"; y] uu____2409 in
                 FStar_Syntax_Syntax.fvar uu____2408 dd dq in
               FStar_Pervasives_Native.Some uu____2407
             else FStar_Pervasives_Native.None)
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_ok _0 -> true | uu____2441 -> false
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_fail -> true | uu____2473 -> false
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_ignore -> true | uu____2490 -> false
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore ->
    fun uu___1_2518 ->
      match uu___1_2518 with
      | Cont_ok a1 -> FStar_Pervasives_Native.Some a1
      | Cont_fail -> FStar_Pervasives_Native.None
      | Cont_ignore -> k_ignore ()
let find_in_record :
  'uuuuuu2536 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'uuuuuu2536 cont_t) -> 'uuuuuu2536 cont_t
  =
  fun ns ->
    fun id ->
      fun record ->
        fun cont ->
          let typename' =
            let uu____2573 =
              let uu____2574 =
                let uu____2577 = FStar_Ident.ident_of_lid record.typename in
                [uu____2577] in
              FStar_List.append ns uu____2574 in
            FStar_Ident.lid_of_ids uu____2573 in
          let uu____2578 = FStar_Ident.lid_equals typename' record.typename in
          if uu____2578
          then
            let fname =
              let uu____2582 =
                let uu____2583 = FStar_Ident.ns_of_lid record.typename in
                FStar_List.append uu____2583 [id] in
              FStar_Ident.lid_of_ids uu____2582 in
            let find =
              FStar_Util.find_map record.fields
                (fun uu____2597 ->
                   match uu____2597 with
                   | (f, uu____2605) ->
                       let uu____2606 =
                         let uu____2607 = FStar_Ident.string_of_id id in
                         let uu____2608 = FStar_Ident.string_of_id f in
                         uu____2607 = uu____2608 in
                       if uu____2606
                       then FStar_Pervasives_Native.Some record
                       else FStar_Pervasives_Native.None) in
            match find with
            | FStar_Pervasives_Native.Some r -> cont r
            | FStar_Pervasives_Native.None -> Cont_ignore
          else Cont_ignore
let (get_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option)
  = fun e -> fun mname -> FStar_Util.smap_try_find e.exported_ids mname
let (get_trans_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option)
  = fun e -> fun mname -> FStar_Util.smap_try_find e.trans_exported_ids mname
let (string_of_exported_id_kind : exported_id_kind -> Prims.string) =
  fun uu___2_2670 ->
    match uu___2_2670 with
    | Exported_id_field -> "field"
    | Exported_id_term_type -> "term/type"
let find_in_module_with_includes :
  'a .
    exported_id_kind ->
      (FStar_Ident.lident -> 'a cont_t) ->
        'a cont_t ->
          env -> FStar_Ident.lident -> FStar_Ident.ident -> 'a cont_t
  =
  fun eikind ->
    fun find_in_module ->
      fun find_in_module_default ->
        fun env1 ->
          fun ns ->
            fun id ->
              let idstr = FStar_Ident.string_of_id id in
              let rec aux uu___3_2741 =
                match uu___3_2741 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = FStar_Ident.string_of_lid modul in
                    let not_shadowed =
                      let uu____2752 = get_exported_id_set env1 mname in
                      match uu____2752 with
                      | FStar_Pervasives_Native.None -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____2777 = mex eikind in
                            FStar_ST.op_Bang uu____2777 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____2799 =
                        FStar_Util.smap_try_find env1.includes mname in
                      match uu____2799 with
                      | FStar_Pervasives_Native.None -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____2840 = qual modul id in
                        find_in_module uu____2840
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore -> aux (FStar_List.append mincludes q)
                     | uu____2844 -> look_into) in
              aux [ns]
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___4_2851 ->
    match uu___4_2851 with | Exported_id_field -> true | uu____2852 -> false
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
  fun env1 ->
    fun id ->
      fun eikind ->
        fun k_local_binding ->
          fun k_rec_binding ->
            fun k_record ->
              fun find_in_module ->
                fun lookup_default_id ->
                  let check_local_binding_id uu___5_2973 =
                    match uu___5_2973 with
                    | (id', uu____2975, uu____2976) ->
                        let uu____2977 = FStar_Ident.string_of_id id' in
                        let uu____2978 = FStar_Ident.string_of_id id in
                        uu____2977 = uu____2978 in
                  let check_rec_binding_id uu___6_2984 =
                    match uu___6_2984 with
                    | (id', uu____2986, uu____2987, uu____2988) ->
                        let uu____2989 = FStar_Ident.string_of_id id' in
                        let uu____2990 = FStar_Ident.string_of_id id in
                        uu____2989 = uu____2990 in
                  let curmod_ns =
                    let uu____2992 = current_module env1 in
                    FStar_Ident.ids_of_lid uu____2992 in
                  let proc uu___7_3000 =
                    match uu___7_3000 with
                    | Local_binding l when check_local_binding_id l ->
                        let uu____3004 = l in
                        (match uu____3004 with
                         | (uu____3007, uu____3008, used_marker1) ->
                             (FStar_ST.op_Colon_Equals used_marker1 true;
                              k_local_binding l))
                    | Rec_binding r when check_rec_binding_id r ->
                        let uu____3018 = r in
                        (match uu____3018 with
                         | (uu____3021, uu____3022, uu____3023, used_marker1)
                             ->
                             (FStar_ST.op_Colon_Equals used_marker1 true;
                              k_rec_binding r))
                    | Open_module_or_namespace (ns, Open_module) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env1 ns id
                    | Top_level_def id' when
                        let uu____3034 = FStar_Ident.string_of_id id' in
                        let uu____3035 = FStar_Ident.string_of_id id in
                        uu____3034 = uu____3035 ->
                        lookup_default_id Cont_ignore id
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____3037 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid ->
                             let id1 = FStar_Ident.ident_of_lid lid in
                             let uu____3043 = FStar_Ident.ns_of_lid lid in
                             find_in_record uu____3043 id1 r k_record)
                          Cont_ignore env1 uu____3037 id
                    | uu____3046 -> Cont_ignore in
                  let rec aux uu___8_3056 =
                    match uu___8_3056 with
                    | a1::q ->
                        let uu____3065 = proc a1 in
                        option_of_cont (fun uu____3069 -> aux q) uu____3065
                    | [] ->
                        let uu____3070 = lookup_default_id Cont_fail id in
                        option_of_cont
                          (fun uu____3074 -> FStar_Pervasives_Native.None)
                          uu____3070 in
                  aux env1.scope_mods
let found_local_binding :
  'uuuuuu3083 'uuuuuu3084 .
    FStar_Range.range ->
      ('uuuuuu3083 * FStar_Syntax_Syntax.bv * 'uuuuuu3084) ->
        FStar_Syntax_Syntax.term
  =
  fun r ->
    fun uu____3100 ->
      match uu____3100 with | (id', x, uu____3109) -> bv_to_name x r
let find_in_module :
  'uuuuuu3120 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'uuuuuu3120)
          -> 'uuuuuu3120 -> 'uuuuuu3120
  =
  fun env1 ->
    fun lid ->
      fun k_global_def ->
        fun k_not_found ->
          let uu____3159 =
            let uu____3166 = FStar_Ident.string_of_lid lid in
            FStar_Util.smap_try_find (sigmap env1) uu____3166 in
          match uu____3159 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None -> k_not_found
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun id ->
      let uu____3198 = unmangleOpName id in
      match uu____3198 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3204 ->
          try_lookup_id'' env1 id Exported_id_term_type
            (fun r ->
               let uu____3210 =
                 let uu____3211 = FStar_Ident.range_of_id id in
                 found_local_binding uu____3211 r in
               Cont_ok uu____3210) (fun uu____3213 -> Cont_fail)
            (fun uu____3215 -> Cont_ignore)
            (fun i ->
               find_in_module env1 i
                 (fun uu____3222 -> fun uu____3223 -> Cont_fail) Cont_ignore)
            (fun uu____3230 -> fun uu____3231 -> Cont_fail)
let lookup_default_id :
  'a .
    env ->
      FStar_Ident.ident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'a cont_t)
          -> 'a cont_t -> 'a cont_t
  =
  fun env1 ->
    fun id ->
      fun k_global_def ->
        fun k_not_found ->
          let find_in_monad =
            match env1.curmonad with
            | FStar_Pervasives_Native.Some uu____3302 ->
                let lid = qualify env1 id in
                let uu____3304 =
                  let uu____3311 = FStar_Ident.string_of_lid lid in
                  FStar_Util.smap_try_find (sigmap env1) uu____3311 in
                (match uu____3304 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3329 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3329
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v -> v
          | FStar_Pervasives_Native.None ->
              let lid =
                let uu____3352 = current_module env1 in qual uu____3352 id in
              find_in_module env1 lid k_global_def k_not_found
let (lid_is_curmod : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      match env1.curmodule with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some m -> FStar_Ident.lid_equals lid m
let (module_is_defined : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      (lid_is_curmod env1 lid) ||
        (FStar_List.existsb
           (fun x ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env1.modules)
let (resolve_module_name :
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      fun honor_ns ->
        let nslen =
          let uu____3406 = FStar_Ident.ns_of_lid lid in
          FStar_List.length uu____3406 in
        let rec aux uu___9_3418 =
          match uu___9_3418 with
          | [] ->
              let uu____3423 = module_is_defined env1 lid in
              if uu____3423
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns
              ->
              let new_lid =
                let uu____3432 =
                  let uu____3433 = FStar_Ident.path_of_lid ns in
                  let uu____3436 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3433 uu____3436 in
                let uu____3439 = FStar_Ident.range_of_lid lid in
                FStar_Ident.lid_of_path uu____3432 uu____3439 in
              let uu____3440 = module_is_defined env1 new_lid in
              if uu____3440
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name, modul))::uu____3446 when
              (nslen = Prims.int_zero) &&
                (let uu____3451 = FStar_Ident.string_of_id name in
                 let uu____3452 =
                   let uu____3453 = FStar_Ident.ident_of_lid lid in
                   FStar_Ident.string_of_id uu____3453 in
                 uu____3451 = uu____3452)
              -> FStar_Pervasives_Native.Some modul
          | uu____3454::q -> aux q in
        aux env1.scope_mods
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env1 ->
    fun lid ->
      fun open_kind1 ->
        FStar_List.existsb
          (fun uu___10_3476 ->
             match uu___10_3476 with
             | Open_module_or_namespace (ns, k) ->
                 (k = open_kind1) && (FStar_Ident.lid_equals lid ns)
             | uu____3479 -> false) env1.scope_mods
let (namespace_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 -> fun lid -> is_open env1 lid Open_namespace
let (module_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid -> (lid_is_curmod env1 lid) || (is_open env1 lid Open_module)
let (shorten_module_path :
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  =
  fun env1 ->
    fun ids ->
      fun is_full_path ->
        let rec aux revns id =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id in
          if namespace_is_open env1 lid
          then
            FStar_Pervasives_Native.Some ((FStar_List.rev (id :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu____3598 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____3598
                   (FStar_Util.map_option
                      (fun uu____3648 ->
                         match uu____3648 with
                         | (stripped_ids, rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let do_shorten env2 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____3718 = aux ns_rev_prefix ns_last_id in
              (match uu____3718 with
               | FStar_Pervasives_Native.None -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids))) in
        if is_full_path && ((FStar_List.length ids) > Prims.int_zero)
        then
          let uu____3779 =
            let uu____3782 = FStar_Ident.lid_of_ids ids in
            resolve_module_name env1 uu____3782 true in
          match uu____3779 with
          | FStar_Pervasives_Native.Some m when module_is_open env1 m ->
              (ids, [])
          | uu____3796 -> do_shorten env1 ids
        else do_shorten env1 ids
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
  fun env1 ->
    fun lid ->
      fun eikind ->
        fun k_local_binding ->
          fun k_rec_binding ->
            fun k_record ->
              fun f_module ->
                fun l_default ->
                  let uu____3915 = FStar_Ident.ns_of_lid lid in
                  match uu____3915 with
                  | uu____3918::uu____3919 ->
                      let uu____3922 =
                        let uu____3925 =
                          let uu____3926 =
                            let uu____3927 = FStar_Ident.ns_of_lid lid in
                            FStar_Ident.lid_of_ids uu____3927 in
                          let uu____3928 = FStar_Ident.range_of_lid lid in
                          FStar_Ident.set_lid_range uu____3926 uu____3928 in
                        resolve_module_name env1 uu____3925 true in
                      (match uu____3922 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____3932 =
                             let uu____3935 = FStar_Ident.ident_of_lid lid in
                             find_in_module_with_includes eikind f_module
                               Cont_fail env1 modul uu____3935 in
                           option_of_cont
                             (fun uu____3937 -> FStar_Pervasives_Native.None)
                             uu____3932)
                  | [] ->
                      let uu____3938 = FStar_Ident.ident_of_lid lid in
                      try_lookup_id'' env1 uu____3938 eikind k_local_binding
                        k_rec_binding k_record f_module l_default
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none ->
    fun uu___11_3961 ->
      match uu___11_3961 with
      | FStar_Pervasives_Native.Some v -> Cont_ok v
      | FStar_Pervasives_Native.None -> k_none
let resolve_in_open_namespaces' :
  'a .
    env ->
      FStar_Ident.lident ->
        (local_binding -> 'a FStar_Pervasives_Native.option) ->
          (rec_binding -> 'a FStar_Pervasives_Native.option) ->
            (FStar_Ident.lident ->
               (FStar_Syntax_Syntax.sigelt * Prims.bool) ->
                 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun env1 ->
    fun lid ->
      fun k_local_binding ->
        fun k_rec_binding ->
          fun k_global_def ->
            let k_global_def' k lid1 def =
              let uu____4077 = k_global_def lid1 def in
              cont_of_option k uu____4077 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env1 lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env1 i (k_global_def' k) k in
            resolve_in_open_namespaces'' env1 lid Exported_id_term_type
              (fun l ->
                 let uu____4113 = k_local_binding l in
                 cont_of_option Cont_fail uu____4113)
              (fun r ->
                 let uu____4119 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4119)
              (fun uu____4123 -> Cont_ignore) f_module l_default
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4133, uu____4134, uu____4135, l, uu____4137, uu____4138) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___12_4149 ->
               match uu___12_4149 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4152, fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4164 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____4170, uu____4171, uu____4172) -> FStar_Pervasives_Native.None
    | uu____4173 -> FStar_Pervasives_Native.None
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs ->
    fun lid ->
      let uu____4188 =
        FStar_Util.find_map lbs
          (fun lb ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4196 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4196
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4188 FStar_Util.must
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    fun ns ->
      (let uu____4216 =
         let uu____4217 = FStar_Ident.ns_of_lid lid in
         FStar_List.length uu____4217 in
       let uu____4220 =
         let uu____4221 = FStar_Ident.ids_of_lid ns in
         FStar_List.length uu____4221 in
       uu____4216 = uu____4220) &&
        (let uu____4225 =
           let uu____4226 = FStar_Ident.ns_of_lid lid in
           FStar_Ident.lid_of_ids uu____4226 in
         FStar_Ident.lid_equals uu____4225 ns)
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid ->
    fun quals ->
      let dd =
        let uu____4242 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___13_4247 ->
                     match uu___13_4247 with
                     | FStar_Syntax_Syntax.Projector uu____4248 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____4253 -> true
                     | uu____4254 -> false))) in
        if uu____4242
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant in
      let uu____4256 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___14_4260 ->
                 match uu___14_4260 with
                 | FStar_Syntax_Syntax.Assumption -> true
                 | uu____4261 -> false)))
          &&
          (let uu____4263 =
             FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___15_4267 ->
                     match uu___15_4267 with
                     | FStar_Syntax_Syntax.New -> true
                     | uu____4268 -> false)) in
           Prims.op_Negation uu____4263) in
      if uu____4256 then FStar_Syntax_Syntax.Delta_abstract dd else dd
let (try_lookup_name :
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option)
  =
  fun any_val ->
    fun exclude_interf ->
      fun env1 ->
        fun lid ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___18_4311 =
            match uu___18_4311 with
            | (uu____4318, true) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se, uu____4320) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4323 ->
                     let uu____4340 =
                       let uu____4341 =
                         let uu____4348 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4348, (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4341 in
                     FStar_Pervasives_Native.Some uu____4340
                 | FStar_Syntax_Syntax.Sig_datacon uu____4351 ->
                     let uu____4366 =
                       let uu____4367 =
                         let uu____4374 =
                           let uu____4375 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____4375 in
                         (uu____4374, (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4367 in
                     FStar_Pervasives_Native.Some uu____4366
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____4380, lbs), uu____4382) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____4392 =
                       let uu____4393 =
                         let uu____4400 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____4400, (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4393 in
                     FStar_Pervasives_Native.Some uu____4392
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1, uu____4404, uu____4405) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____4409 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___16_4413 ->
                                  match uu___16_4413 with
                                  | FStar_Syntax_Syntax.Assumption -> true
                                  | uu____4414 -> false))) in
                     if uu____4409
                     then
                       let lid2 =
                         let uu____4418 = FStar_Ident.range_of_lid source_lid in
                         FStar_Ident.set_lid_range lid1 uu____4418 in
                       let dd = delta_depth_of_declaration lid2 quals in
                       let uu____4420 =
                         FStar_Util.find_map quals
                           (fun uu___17_4425 ->
                              match uu___17_4425 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____4429 -> FStar_Pervasives_Native.None) in
                       (match uu____4420 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name
                                 (refl_const,
                                   (se.FStar_Syntax_Syntax.sigattrs)))
                        | uu____4438 ->
                            let uu____4441 =
                              let uu____4442 =
                                let uu____4449 =
                                  let uu____4450 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____4450 in
                                (uu____4449,
                                  (se.FStar_Syntax_Syntax.sigattrs)) in
                              Term_name uu____4442 in
                            FStar_Pervasives_Native.Some uu____4441)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4457 =
                       let uu____4458 =
                         let uu____4463 =
                           let uu____4464 =
                             FStar_Ident.range_of_lid source_lid in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____4464 in
                         (se, uu____4463) in
                       Eff_name uu____4458 in
                     FStar_Pervasives_Native.Some uu____4457
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4465 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
                     let uu____4484 =
                       let uu____4485 =
                         let uu____4492 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                Prims.int_one) FStar_Pervasives_Native.None in
                         (uu____4492, []) in
                       Term_name uu____4485 in
                     FStar_Pervasives_Native.Some uu____4484
                 | uu____4495 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let t =
              let uu____4517 = FStar_Ident.range_of_lid lid in
              found_local_binding uu____4517 r in
            FStar_Pervasives_Native.Some (Term_name (t, [])) in
          let k_rec_binding uu____4547 =
            match uu____4547 with
            | (id, l, dd, used_marker1) ->
                (FStar_ST.op_Colon_Equals used_marker1 true;
                 (let uu____4605 =
                    let uu____4606 =
                      let uu____4613 =
                        let uu____4614 =
                          let uu____4615 = FStar_Ident.range_of_lid lid in
                          FStar_Ident.set_lid_range l uu____4615 in
                        FStar_Syntax_Syntax.fvar uu____4614 dd
                          FStar_Pervasives_Native.None in
                      (uu____4613, []) in
                    Term_name uu____4606 in
                  FStar_Pervasives_Native.Some uu____4605)) in
          let found_unmangled =
            let uu____4621 = FStar_Ident.ns_of_lid lid in
            match uu____4621 with
            | [] ->
                let uu____4624 =
                  let uu____4627 = FStar_Ident.ident_of_lid lid in
                  unmangleOpName uu____4627 in
                (match uu____4624 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____4633 -> FStar_Pervasives_Native.None)
            | uu____4636 -> FStar_Pervasives_Native.None in
          match found_unmangled with
          | FStar_Pervasives_Native.None ->
              resolve_in_open_namespaces' env1 lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
let (try_lookup_effect_name' :
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)
          FStar_Pervasives_Native.option)
  =
  fun exclude_interf ->
    fun env1 ->
      fun lid ->
        let uu____4669 = try_lookup_name true exclude_interf env1 lid in
        match uu____4669 with
        | FStar_Pervasives_Native.Some (Eff_name (o, l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____4684 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____4703 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu____4703 with
      | FStar_Pervasives_Native.Some (o, l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____4718 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____4743 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu____4743 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4759;
             FStar_Syntax_Syntax.sigquals = uu____4760;
             FStar_Syntax_Syntax.sigmeta = uu____4761;
             FStar_Syntax_Syntax.sigattrs = uu____4762;
             FStar_Syntax_Syntax.sigopts = uu____4763;_},
           l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____4783, uu____4784, uu____4785, uu____4786, cattributes);
             FStar_Syntax_Syntax.sigrng = uu____4788;
             FStar_Syntax_Syntax.sigquals = uu____4789;
             FStar_Syntax_Syntax.sigmeta = uu____4790;
             FStar_Syntax_Syntax.sigattrs = uu____4791;
             FStar_Syntax_Syntax.sigopts = uu____4792;_},
           l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____4816 -> FStar_Pervasives_Native.None
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____4841 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu____4841 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____4851;
             FStar_Syntax_Syntax.sigquals = uu____4852;
             FStar_Syntax_Syntax.sigmeta = uu____4853;
             FStar_Syntax_Syntax.sigattrs = uu____4854;
             FStar_Syntax_Syntax.sigopts = uu____4855;_},
           uu____4856)
          -> FStar_Pervasives_Native.Some ne
      | uu____4867 -> FStar_Pervasives_Native.None
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____4884 = try_lookup_effect_name env1 lid in
      match uu____4884 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____4887 -> true
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____4900 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu____4900 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l', uu____4910, uu____4911, uu____4912, uu____4913);
             FStar_Syntax_Syntax.sigrng = uu____4914;
             FStar_Syntax_Syntax.sigquals = uu____4915;
             FStar_Syntax_Syntax.sigmeta = uu____4916;
             FStar_Syntax_Syntax.sigattrs = uu____4917;
             FStar_Syntax_Syntax.sigopts = uu____4918;_},
           uu____4919)
          ->
          let rec aux new_name =
            let uu____4942 =
              let uu____4949 = FStar_Ident.string_of_lid new_name in
              FStar_Util.smap_try_find (sigmap env1) uu____4949 in
            match uu____4942 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s, uu____4961) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____4969 =
                       let uu____4970 = FStar_Ident.range_of_lid l in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____4970 in
                     FStar_Pervasives_Native.Some uu____4969
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____4971, uu____4972, uu____4973, cmp, uu____4975) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____4981 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____4982, l') ->
          FStar_Pervasives_Native.Some l'
      | uu____4988 -> FStar_Pervasives_Native.None
let (lookup_letbinding_quals_and_attrs :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.qualifier Prims.list *
        FStar_Syntax_Syntax.attribute Prims.list))
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___19_5037 =
        match uu___19_5037 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5052, uu____5053, uu____5054);
             FStar_Syntax_Syntax.sigrng = uu____5055;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5057;
             FStar_Syntax_Syntax.sigattrs = attrs;
             FStar_Syntax_Syntax.sigopts = uu____5059;_},
           uu____5060) -> FStar_Pervasives_Native.Some (quals, attrs)
        | uu____5079 -> FStar_Pervasives_Native.None in
      let uu____5092 =
        resolve_in_open_namespaces' env1 lid
          (fun uu____5112 -> FStar_Pervasives_Native.None)
          (fun uu____5122 -> FStar_Pervasives_Native.None) k_global_def in
      match uu____5092 with
      | FStar_Pervasives_Native.Some qa -> qa
      | uu____5156 -> ([], [])
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun path ->
      let uu____5183 =
        FStar_List.tryFind
          (fun uu____5198 ->
             match uu____5198 with
             | (mlid, modul) ->
                 let uu____5205 = FStar_Ident.path_of_lid mlid in
                 uu____5205 = path) env1.modules in
      match uu____5183 with
      | FStar_Pervasives_Native.Some (uu____5208, modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___20_5246 =
        match uu___20_5246 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5253, lbs), uu____5255);
             FStar_Syntax_Syntax.sigrng = uu____5256;
             FStar_Syntax_Syntax.sigquals = uu____5257;
             FStar_Syntax_Syntax.sigmeta = uu____5258;
             FStar_Syntax_Syntax.sigattrs = uu____5259;
             FStar_Syntax_Syntax.sigopts = uu____5260;_},
           uu____5261) ->
            let fv = lb_fv lbs lid1 in
            let uu____5277 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____5277
        | uu____5278 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu____5284 -> FStar_Pervasives_Native.None)
        (fun uu____5286 -> FStar_Pervasives_Native.None) k_global_def
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___21_5317 =
        match uu___21_5317 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs, uu____5327);
             FStar_Syntax_Syntax.sigrng = uu____5328;
             FStar_Syntax_Syntax.sigquals = uu____5329;
             FStar_Syntax_Syntax.sigmeta = uu____5330;
             FStar_Syntax_Syntax.sigattrs = uu____5331;
             FStar_Syntax_Syntax.sigopts = uu____5332;_},
           uu____5333) ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____5358 -> FStar_Pervasives_Native.None)
        | uu____5365 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu____5375 -> FStar_Pervasives_Native.None)
        (fun uu____5379 -> FStar_Pervasives_Native.None) k_global_def
let (empty_include_smap :
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap) = new_sigmap ()
let (empty_exported_id_smap : exported_id_set FStar_Util.smap) =
  new_sigmap ()
let (try_lookup_lid' :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute
            Prims.list) FStar_Pervasives_Native.option)
  =
  fun any_val ->
    fun exclude_interface ->
      fun env1 ->
        fun lid ->
          let uu____5432 = try_lookup_name any_val exclude_interface env1 lid in
          match uu____5432 with
          | FStar_Pervasives_Native.Some (Term_name (e, attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____5457 -> FStar_Pervasives_Native.None
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x ->
    match x with
    | FStar_Pervasives_Native.Some (t, uu____5494) ->
        FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (try_lookup_lid_with_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  = fun env1 -> fun l -> try_lookup_lid' env1.iface false env1 l
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____5549 = try_lookup_lid_with_attributes env1 l in
      FStar_All.pipe_right uu____5549 drop_attributes
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____5580 = try_lookup_lid env1 l in
      match uu____5580 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____5586 =
            let uu____5587 = FStar_Syntax_Subst.compress e in
            uu____5587.FStar_Syntax_Syntax.n in
          (match uu____5586 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____5593 -> FStar_Pervasives_Native.None)
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      let uu____5604 =
        let uu____5613 = FStar_Ident.ns_of_lid lid in
        shorten_module_path env1 uu____5613 true in
      match uu____5604 with
      | (uu____5616, short) ->
          let uu____5626 = FStar_Ident.ident_of_lid lid in
          FStar_Ident.lid_of_ns_and_id short uu____5626
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env1 ->
    fun lid ->
      match env1.curmodule with
      | FStar_Pervasives_Native.None -> shorten_lid' env1 lid
      | uu____5637 ->
          let lid_without_ns =
            let uu____5641 = FStar_Ident.ident_of_lid lid in
            FStar_Ident.lid_of_ns_and_id [] uu____5641 in
          let uu____5642 =
            resolve_to_fully_qualified_name env1 lid_without_ns in
          (match uu____5642 with
           | FStar_Pervasives_Native.Some lid' when
               let uu____5646 = FStar_Ident.string_of_lid lid' in
               let uu____5647 = FStar_Ident.string_of_lid lid in
               uu____5646 = uu____5647 -> lid_without_ns
           | uu____5648 -> shorten_lid' env1 lid)
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let env' =
        let uu___863_5678 = env1 in
        {
          curmodule = (uu___863_5678.curmodule);
          curmonad = (uu___863_5678.curmonad);
          modules = (uu___863_5678.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___863_5678.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___863_5678.sigaccum);
          sigmap = (uu___863_5678.sigmap);
          iface = (uu___863_5678.iface);
          admitted_iface = (uu___863_5678.admitted_iface);
          expect_typ = (uu___863_5678.expect_typ);
          remaining_iface_decls = (uu___863_5678.remaining_iface_decls);
          syntax_only = (uu___863_5678.syntax_only);
          ds_hooks = (uu___863_5678.ds_hooks);
          dep_graph = (uu___863_5678.dep_graph)
        } in
      try_lookup_lid_with_attributes env' l
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____5693 = try_lookup_lid_with_attributes_no_resolve env1 l in
      FStar_All.pipe_right uu____5693 drop_attributes
let (try_lookup_datacon :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 se =
        match se with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5747, uu____5748, uu____5749);
             FStar_Syntax_Syntax.sigrng = uu____5750;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5752;
             FStar_Syntax_Syntax.sigattrs = uu____5753;
             FStar_Syntax_Syntax.sigopts = uu____5754;_},
           uu____5755) ->
            let uu____5762 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___22_5766 ->
                      match uu___22_5766 with
                      | FStar_Syntax_Syntax.Assumption -> true
                      | uu____5767 -> false)) in
            if uu____5762
            then
              let uu____5770 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____5770
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____5772;
             FStar_Syntax_Syntax.sigrng = uu____5773;
             FStar_Syntax_Syntax.sigquals = uu____5774;
             FStar_Syntax_Syntax.sigmeta = uu____5775;
             FStar_Syntax_Syntax.sigattrs = uu____5776;
             FStar_Syntax_Syntax.sigopts = uu____5777;_},
           uu____5778) ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se) in
            let uu____5802 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1 in
            FStar_Pervasives_Native.Some uu____5802
        | uu____5803 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu____5809 -> FStar_Pervasives_Native.None)
        (fun uu____5811 -> FStar_Pervasives_Native.None) k_global_def
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___23_5844 =
        match uu___23_5844 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____5853, uu____5854, uu____5855, uu____5856, datas,
                uu____5858);
             FStar_Syntax_Syntax.sigrng = uu____5859;
             FStar_Syntax_Syntax.sigquals = uu____5860;
             FStar_Syntax_Syntax.sigmeta = uu____5861;
             FStar_Syntax_Syntax.sigattrs = uu____5862;
             FStar_Syntax_Syntax.sigopts = uu____5863;_},
           uu____5864) -> FStar_Pervasives_Native.Some datas
        | uu____5881 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu____5891 -> FStar_Pervasives_Native.None)
        (fun uu____5895 -> FStar_Pervasives_Native.None) k_global_def
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push uu____5971 =
    let uu____5972 =
      let uu____5977 =
        let uu____5980 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____5980 in
      let uu____6001 = FStar_ST.op_Bang record_cache in uu____5977 ::
        uu____6001 in
    FStar_ST.op_Colon_Equals record_cache uu____5972 in
  let pop uu____6041 =
    let uu____6042 =
      let uu____6047 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____6047 in
    FStar_ST.op_Colon_Equals record_cache uu____6042 in
  let snapshot uu____6091 = FStar_Common.snapshot push record_cache () in
  let rollback depth = FStar_Common.rollback pop record_cache depth in
  let peek uu____6113 =
    let uu____6114 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____6114 in
  let insert r =
    let uu____6141 =
      let uu____6146 = let uu____6149 = peek () in r :: uu____6149 in
      let uu____6152 =
        let uu____6157 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6157 in
      uu____6146 :: uu____6152 in
    FStar_ST.op_Colon_Equals record_cache uu____6141 in
  let filter uu____6199 =
    let rc = peek () in
    let filtered =
      FStar_List.filter (fun r -> Prims.op_Negation r.is_private) rc in
    let uu____6208 =
      let uu____6213 =
        let uu____6218 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____6218 in
      filtered :: uu____6213 in
    FStar_ST.op_Colon_Equals record_cache uu____6208 in
  let aux = ((push, pop), ((snapshot, rollback), (peek, insert))) in
  (aux, filter)
let (record_cache_aux :
  (((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))))
  = FStar_Pervasives_Native.fst record_cache_aux_with_filter
let (filter_record_cache : unit -> unit) =
  FStar_Pervasives_Native.snd record_cache_aux_with_filter
let (push_record_cache : unit -> unit) =
  FStar_Pervasives_Native.fst (FStar_Pervasives_Native.fst record_cache_aux)
let (pop_record_cache : unit -> unit) =
  FStar_Pervasives_Native.snd (FStar_Pervasives_Native.fst record_cache_aux)
let (snapshot_record_cache : unit -> (Prims.int * unit)) =
  FStar_Pervasives_Native.fst
    (FStar_Pervasives_Native.fst
       (FStar_Pervasives_Native.snd record_cache_aux))
let (rollback_record_cache :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  FStar_Pervasives_Native.snd
    (FStar_Pervasives_Native.fst
       (FStar_Pervasives_Native.snd record_cache_aux))
let (peek_record_cache : unit -> record_or_dc Prims.list) =
  FStar_Pervasives_Native.fst
    (FStar_Pervasives_Native.snd
       (FStar_Pervasives_Native.snd record_cache_aux))
let (insert_record_cache : record_or_dc -> unit) =
  FStar_Pervasives_Native.snd
    (FStar_Pervasives_Native.snd
       (FStar_Pervasives_Native.snd record_cache_aux))
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref -> FStar_Syntax_Syntax.sigelt -> unit)
  =
  fun e ->
    fun new_globs ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs, uu____7067) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___24_7085 ->
                   match uu___24_7085 with
                   | FStar_Syntax_Syntax.RecordType uu____7086 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____7095 -> true
                   | uu____7104 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___25_7129 ->
                      match uu___25_7129 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid, uu____7131, uu____7132, uu____7133,
                             uu____7134, uu____7135);
                          FStar_Syntax_Syntax.sigrng = uu____7136;
                          FStar_Syntax_Syntax.sigquals = uu____7137;
                          FStar_Syntax_Syntax.sigmeta = uu____7138;
                          FStar_Syntax_Syntax.sigattrs = uu____7139;
                          FStar_Syntax_Syntax.sigopts = uu____7140;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____7151 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___26_7191 ->
                    match uu___26_7191 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename, univs, parms, uu____7195, uu____7196,
                           dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____7198;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____7200;
                        FStar_Syntax_Syntax.sigattrs = uu____7201;
                        FStar_Syntax_Syntax.sigopts = uu____7202;_} ->
                        let uu____7215 =
                          let uu____7216 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____7216 in
                        (match uu____7215 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname, uu____7222, t, uu____7224, n,
                                uu____7226);
                             FStar_Syntax_Syntax.sigrng = uu____7227;
                             FStar_Syntax_Syntax.sigquals = uu____7228;
                             FStar_Syntax_Syntax.sigmeta = uu____7229;
                             FStar_Syntax_Syntax.sigattrs = uu____7230;
                             FStar_Syntax_Syntax.sigopts = uu____7231;_} ->
                             let uu____7242 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____7242 with
                              | (all_formals, uu____7250) ->
                                  let uu____7255 =
                                    FStar_Util.first_N n all_formals in
                                  (match uu____7255 with
                                   | (_params, formals) ->
                                       let is_rec = is_record typename_quals in
                                       let formals' =
                                         FStar_All.pipe_right formals
                                           (FStar_List.collect
                                              (fun uu____7348 ->
                                                 match uu____7348 with
                                                 | (x, q) ->
                                                     let uu____7361 =
                                                       (FStar_Syntax_Syntax.is_null_bv
                                                          x)
                                                         ||
                                                         (is_rec &&
                                                            (FStar_Syntax_Syntax.is_implicit
                                                               q)) in
                                                     if uu____7361
                                                     then []
                                                     else [(x, q)])) in
                                       let fields' =
                                         FStar_All.pipe_right formals'
                                           (FStar_List.map
                                              (fun uu____7413 ->
                                                 match uu____7413 with
                                                 | (x, q) ->
                                                     ((x.FStar_Syntax_Syntax.ppname),
                                                       (x.FStar_Syntax_Syntax.sort)))) in
                                       let fields = fields' in
                                       let record =
                                         let uu____7436 =
                                           FStar_Ident.ident_of_lid
                                             constrname in
                                         {
                                           typename;
                                           constrname = uu____7436;
                                           parms;
                                           fields;
                                           is_private =
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Private
                                                typename_quals);
                                           is_record = is_rec
                                         } in
                                       ((let uu____7438 =
                                           let uu____7441 =
                                             FStar_ST.op_Bang new_globs in
                                           (Record_or_dc record) ::
                                             uu____7441 in
                                         FStar_ST.op_Colon_Equals new_globs
                                           uu____7438);
                                        (match () with
                                         | () ->
                                             ((let add_field uu____7474 =
                                                 match uu____7474 with
                                                 | (id, uu____7480) ->
                                                     let modul =
                                                       let uu____7482 =
                                                         let uu____7483 =
                                                           FStar_Ident.ns_of_lid
                                                             constrname in
                                                         FStar_Ident.lid_of_ids
                                                           uu____7483 in
                                                       FStar_Ident.string_of_lid
                                                         uu____7482 in
                                                     let uu____7484 =
                                                       get_exported_id_set e
                                                         modul in
                                                     (match uu____7484 with
                                                      | FStar_Pervasives_Native.Some
                                                          my_ex ->
                                                          let my_exported_ids
                                                            =
                                                            my_ex
                                                              Exported_id_field in
                                                          ((let uu____7507 =
                                                              let uu____7508
                                                                =
                                                                FStar_Ident.string_of_id
                                                                  id in
                                                              let uu____7509
                                                                =
                                                                FStar_ST.op_Bang
                                                                  my_exported_ids in
                                                              FStar_Util.set_add
                                                                uu____7508
                                                                uu____7509 in
                                                            FStar_ST.op_Colon_Equals
                                                              my_exported_ids
                                                              uu____7507);
                                                           (match () with
                                                            | () ->
                                                                let projname
                                                                  =
                                                                  let uu____7525
                                                                    =
                                                                    let uu____7526
                                                                    =
                                                                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                    constrname
                                                                    id in
                                                                    FStar_All.pipe_right
                                                                    uu____7526
                                                                    FStar_Ident.ident_of_lid in
                                                                  FStar_All.pipe_right
                                                                    uu____7525
                                                                    FStar_Ident.string_of_id in
                                                                let uu____7528
                                                                  =
                                                                  let uu____7529
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    my_exported_ids in
                                                                  FStar_Util.set_add
                                                                    projname
                                                                    uu____7529 in
                                                                FStar_ST.op_Colon_Equals
                                                                  my_exported_ids
                                                                  uu____7528))
                                                      | FStar_Pervasives_Native.None
                                                          -> ()) in
                                               FStar_List.iter add_field
                                                 fields');
                                              (match () with
                                               | () ->
                                                   insert_record_cache record))))))
                         | uu____7553 -> ())
                    | uu____7554 -> ()))
        | uu____7555 -> ()
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env1 ->
    fun fieldname ->
      let find_in_cache fieldname1 =
        let uu____7576 =
          let uu____7583 = FStar_Ident.ns_of_lid fieldname1 in
          let uu____7586 = FStar_Ident.ident_of_lid fieldname1 in
          (uu____7583, uu____7586) in
        match uu____7576 with
        | (ns, id) ->
            let uu____7597 = peek_record_cache () in
            FStar_Util.find_map uu____7597
              (fun record ->
                 let uu____7603 =
                   find_in_record ns id record (fun r -> Cont_ok r) in
                 option_of_cont
                   (fun uu____7609 -> FStar_Pervasives_Native.None)
                   uu____7603) in
      resolve_in_open_namespaces'' env1 fieldname Exported_id_field
        (fun uu____7611 -> Cont_ignore) (fun uu____7613 -> Cont_ignore)
        (fun r -> Cont_ok r)
        (fun fn ->
           let uu____7619 = find_in_cache fn in
           cont_of_option Cont_ignore uu____7619)
        (fun k -> fun uu____7625 -> k)
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env1 ->
    fun fieldname ->
      let uu____7640 = try_lookup_record_or_dc_by_field_name env1 fieldname in
      match uu____7640 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____7646 -> FStar_Pervasives_Native.None
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env1 ->
    fun lid ->
      fun record ->
        let uu____7664 = try_lookup_record_by_field_name env1 lid in
        match uu____7664 with
        | FStar_Pervasives_Native.Some record' when
            let uu____7668 = FStar_Ident.nsstr record.typename in
            let uu____7669 = FStar_Ident.nsstr record'.typename in
            uu____7668 = uu____7669 ->
            let uu____7670 =
              let uu____7673 = FStar_Ident.ns_of_lid record.typename in
              let uu____7676 = FStar_Ident.ident_of_lid lid in
              find_in_record uu____7673 uu____7676 record
                (fun uu____7678 -> Cont_ok ()) in
            (match uu____7670 with
             | Cont_ok uu____7679 -> true
             | uu____7680 -> false)
        | uu____7683 -> false
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun fieldname ->
      let uu____7702 = try_lookup_record_or_dc_by_field_name env1 fieldname in
      match uu____7702 with
      | FStar_Pervasives_Native.Some r ->
          let uu____7712 =
            let uu____7717 =
              let uu____7718 =
                let uu____7719 =
                  let uu____7720 = FStar_Ident.ns_of_lid r.typename in
                  FStar_List.append uu____7720 [r.constrname] in
                FStar_Ident.lid_of_ids uu____7719 in
              let uu____7723 = FStar_Ident.range_of_lid fieldname in
              FStar_Ident.set_lid_range uu____7718 uu____7723 in
            (uu____7717, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____7712
      | uu____7728 -> FStar_Pervasives_Native.None
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____7743 ->
    let uu____7744 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____7744
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____7760 ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___27_7771 ->
      match uu___27_7771 with
      | Exported_id_term_type -> term_type_set
      | Exported_id_field -> field_set
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val ->
    fun exclude_interface ->
      fun env1 ->
        fun lid ->
          let filter_scope_mods uu___28_7801 =
            match uu___28_7801 with
            | Rec_binding uu____7802 -> true
            | uu____7803 -> false in
          let this_env =
            let uu___1096_7805 = env1 in
            let uu____7806 =
              FStar_List.filter filter_scope_mods env1.scope_mods in
            {
              curmodule = (uu___1096_7805.curmodule);
              curmonad = (uu___1096_7805.curmonad);
              modules = (uu___1096_7805.modules);
              scope_mods = uu____7806;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1096_7805.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1096_7805.sigaccum);
              sigmap = (uu___1096_7805.sigmap);
              iface = (uu___1096_7805.iface);
              admitted_iface = (uu___1096_7805.admitted_iface);
              expect_typ = (uu___1096_7805.expect_typ);
              remaining_iface_decls = (uu___1096_7805.remaining_iface_decls);
              syntax_only = (uu___1096_7805.syntax_only);
              ds_hooks = (uu___1096_7805.ds_hooks);
              dep_graph = (uu___1096_7805.dep_graph)
            } in
          let uu____7809 =
            try_lookup_lid' any_val exclude_interface this_env lid in
          match uu____7809 with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some uu____7824 -> false
let (push_scope_mod : env -> scope_mod -> env) =
  fun env1 ->
    fun scope_mod1 ->
      let uu___1104_7847 = env1 in
      {
        curmodule = (uu___1104_7847.curmodule);
        curmonad = (uu___1104_7847.curmonad);
        modules = (uu___1104_7847.modules);
        scope_mods = (scope_mod1 :: (env1.scope_mods));
        exported_ids = (uu___1104_7847.exported_ids);
        trans_exported_ids = (uu___1104_7847.trans_exported_ids);
        includes = (uu___1104_7847.includes);
        sigaccum = (uu___1104_7847.sigaccum);
        sigmap = (uu___1104_7847.sigmap);
        iface = (uu___1104_7847.iface);
        admitted_iface = (uu___1104_7847.admitted_iface);
        expect_typ = (uu___1104_7847.expect_typ);
        remaining_iface_decls = (uu___1104_7847.remaining_iface_decls);
        syntax_only = (uu___1104_7847.syntax_only);
        ds_hooks = (uu___1104_7847.ds_hooks);
        dep_graph = (uu___1104_7847.dep_graph)
      }
let (push_bv' :
  env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv * used_marker)) =
  fun env1 ->
    fun x ->
      let r = FStar_Ident.range_of_id x in
      let bv =
        let uu____7866 = FStar_Ident.string_of_id x in
        FStar_Syntax_Syntax.gen_bv uu____7866
          (FStar_Pervasives_Native.Some r)
          (let uu___1109_7868 = FStar_Syntax_Syntax.tun in
           {
             FStar_Syntax_Syntax.n = (uu___1109_7868.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r;
             FStar_Syntax_Syntax.vars =
               (uu___1109_7868.FStar_Syntax_Syntax.vars)
           }) in
      let used_marker1 = FStar_Util.mk_ref false in
      ((push_scope_mod env1 (Local_binding (x, bv, used_marker1))), bv,
        used_marker1)
let (push_bv : env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv)) =
  fun env1 ->
    fun x ->
      let uu____7886 = push_bv' env1 x in
      match uu____7886 with | (env2, bv, uu____7899) -> (env2, bv)
let (push_top_level_rec_binding :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.delta_depth -> (env * Prims.bool FStar_ST.ref))
  =
  fun env0 ->
    fun x ->
      fun dd ->
        let l = qualify env0 x in
        let uu____7928 =
          (unique false true env0 l) || (FStar_Options.interactive ()) in
        if uu____7928
        then
          let used_marker1 = FStar_Util.mk_ref false in
          ((push_scope_mod env0 (Rec_binding (x, l, dd, used_marker1))),
            used_marker1)
        else
          (let uu____7941 =
             let uu____7946 =
               let uu____7947 = FStar_Ident.string_of_lid l in
               Prims.op_Hat "Duplicate top-level names " uu____7947 in
             (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____7946) in
           let uu____7948 = FStar_Ident.range_of_lid l in
           FStar_Errors.raise_error uu____7941 uu____7948)
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup ->
    fun env1 ->
      fun s ->
        let err l =
          let sopt =
            let uu____7983 = FStar_Ident.string_of_lid l in
            FStar_Util.smap_try_find (sigmap env1) uu____7983 in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se, uu____7990) ->
                let uu____7995 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se) in
                (match uu____7995 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____7999 = FStar_Ident.range_of_lid l1 in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____7999
                 | FStar_Pervasives_Native.None -> "<unknown>")
            | FStar_Pervasives_Native.None -> "<unknown>" in
          let uu____8004 =
            let uu____8009 =
              let uu____8010 = FStar_Ident.string_of_lid l in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____8010 r in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____8009) in
          let uu____8011 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____8004 uu____8011 in
        let globals = FStar_Util.mk_ref env1.scope_mods in
        let env2 =
          let uu____8020 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____8029 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____8036 -> (false, true)
            | uu____8045 -> (false, false) in
          match uu____8020 with
          | (any_val, exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s in
              let uu____8051 =
                FStar_Util.find_map lids
                  (fun l ->
                     let uu____8057 =
                       let uu____8058 =
                         unique any_val exclude_interface env1 l in
                       Prims.op_Negation uu____8058 in
                     if uu____8057
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None) in
              (match uu____8051 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____8063 ->
                   (extract_record env1 globals s;
                    (let uu___1156_8067 = env1 in
                     {
                       curmodule = (uu___1156_8067.curmodule);
                       curmonad = (uu___1156_8067.curmonad);
                       modules = (uu___1156_8067.modules);
                       scope_mods = (uu___1156_8067.scope_mods);
                       exported_ids = (uu___1156_8067.exported_ids);
                       trans_exported_ids =
                         (uu___1156_8067.trans_exported_ids);
                       includes = (uu___1156_8067.includes);
                       sigaccum = (s :: (env1.sigaccum));
                       sigmap = (uu___1156_8067.sigmap);
                       iface = (uu___1156_8067.iface);
                       admitted_iface = (uu___1156_8067.admitted_iface);
                       expect_typ = (uu___1156_8067.expect_typ);
                       remaining_iface_decls =
                         (uu___1156_8067.remaining_iface_decls);
                       syntax_only = (uu___1156_8067.syntax_only);
                       ds_hooks = (uu___1156_8067.ds_hooks);
                       dep_graph = (uu___1156_8067.dep_graph)
                     }))) in
        let env3 =
          let uu___1159_8069 = env2 in
          let uu____8070 = FStar_ST.op_Bang globals in
          {
            curmodule = (uu___1159_8069.curmodule);
            curmonad = (uu___1159_8069.curmonad);
            modules = (uu___1159_8069.modules);
            scope_mods = uu____8070;
            exported_ids = (uu___1159_8069.exported_ids);
            trans_exported_ids = (uu___1159_8069.trans_exported_ids);
            includes = (uu___1159_8069.includes);
            sigaccum = (uu___1159_8069.sigaccum);
            sigmap = (uu___1159_8069.sigmap);
            iface = (uu___1159_8069.iface);
            admitted_iface = (uu___1159_8069.admitted_iface);
            expect_typ = (uu___1159_8069.expect_typ);
            remaining_iface_decls = (uu___1159_8069.remaining_iface_decls);
            syntax_only = (uu___1159_8069.syntax_only);
            ds_hooks = (uu___1159_8069.ds_hooks);
            dep_graph = (uu___1159_8069.dep_graph)
          } in
        let uu____8083 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses, uu____8109) ->
              let uu____8118 =
                FStar_List.map
                  (fun se -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
              (env3, uu____8118)
          | uu____8145 -> (env3, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
        match uu____8083 with
        | (env4, lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____8204 ->
                     match uu____8204 with
                     | (lids, se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid ->
                                 (let uu____8227 =
                                    let uu____8230 =
                                      let uu____8231 =
                                        FStar_Ident.ident_of_lid lid in
                                      Top_level_def uu____8231 in
                                    let uu____8232 = FStar_ST.op_Bang globals in
                                    uu____8230 :: uu____8232 in
                                  FStar_ST.op_Colon_Equals globals uu____8227);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____8256 =
                                          let uu____8257 =
                                            FStar_Ident.ns_of_lid lid in
                                          FStar_Ident.lid_of_ids uu____8257 in
                                        FStar_Ident.string_of_lid uu____8256 in
                                      ((let uu____8259 =
                                          get_exported_id_set env4 modul in
                                        match uu____8259 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type in
                                            let uu____8281 =
                                              let uu____8282 =
                                                let uu____8283 =
                                                  FStar_Ident.ident_of_lid
                                                    lid in
                                                FStar_Ident.string_of_id
                                                  uu____8283 in
                                              let uu____8284 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids in
                                              FStar_Util.set_add uu____8282
                                                uu____8284 in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____8281
                                        | FStar_Pervasives_Native.None -> ());
                                       (match () with
                                        | () ->
                                            let is_iface =
                                              env4.iface &&
                                                (Prims.op_Negation
                                                   env4.admitted_iface) in
                                            let uu____8305 =
                                              FStar_Ident.string_of_lid lid in
                                            FStar_Util.smap_add (sigmap env4)
                                              uu____8305
                                              (se,
                                                (env4.iface &&
                                                   (Prims.op_Negation
                                                      env4.admitted_iface))))))))));
             (let env5 =
                let uu___1184_8311 = env4 in
                let uu____8312 = FStar_ST.op_Bang globals in
                {
                  curmodule = (uu___1184_8311.curmodule);
                  curmonad = (uu___1184_8311.curmonad);
                  modules = (uu___1184_8311.modules);
                  scope_mods = uu____8312;
                  exported_ids = (uu___1184_8311.exported_ids);
                  trans_exported_ids = (uu___1184_8311.trans_exported_ids);
                  includes = (uu___1184_8311.includes);
                  sigaccum = (uu___1184_8311.sigaccum);
                  sigmap = (uu___1184_8311.sigmap);
                  iface = (uu___1184_8311.iface);
                  admitted_iface = (uu___1184_8311.admitted_iface);
                  expect_typ = (uu___1184_8311.expect_typ);
                  remaining_iface_decls =
                    (uu___1184_8311.remaining_iface_decls);
                  syntax_only = (uu___1184_8311.syntax_only);
                  ds_hooks = (uu___1184_8311.ds_hooks);
                  dep_graph = (uu___1184_8311.dep_graph)
                } in
              env5))
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1 -> fun se -> push_sigelt' true env1 se
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1 -> fun se -> push_sigelt' false env1 se
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun ns ->
      let uu____8355 =
        let uu____8360 = resolve_module_name env1 ns false in
        match uu____8360 with
        | FStar_Pervasives_Native.None ->
            let modules = env1.modules in
            let uu____8374 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____8390 ->
                      match uu____8390 with
                      | (m, uu____8396) ->
                          let uu____8397 =
                            let uu____8398 = FStar_Ident.string_of_lid m in
                            Prims.op_Hat uu____8398 "." in
                          let uu____8399 =
                            let uu____8400 = FStar_Ident.string_of_lid ns in
                            Prims.op_Hat uu____8400 "." in
                          FStar_Util.starts_with uu____8397 uu____8399)) in
            if uu____8374
            then (ns, Open_namespace)
            else
              (let uu____8406 =
                 let uu____8411 =
                   let uu____8412 = FStar_Ident.string_of_lid ns in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____8412 in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____8411) in
               let uu____8413 = FStar_Ident.range_of_lid ns in
               FStar_Errors.raise_error uu____8406 uu____8413)
        | FStar_Pervasives_Native.Some ns' -> (ns', Open_module) in
      match uu____8355 with
      | (ns', kd) ->
          ((env1.ds_hooks).ds_push_open_hook env1 (ns', kd);
           push_scope_mod env1 (Open_module_or_namespace (ns', kd)))
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun ns ->
      let ns0 = ns in
      let uu____8433 = resolve_module_name env1 ns false in
      match uu____8433 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env1.ds_hooks).ds_push_include_hook env1 ns1;
           (let env2 =
              push_scope_mod env1
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____8440 = current_module env2 in
              FStar_Ident.string_of_lid uu____8440 in
            (let uu____8442 = FStar_Util.smap_try_find env2.includes curmod in
             match uu____8442 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____8466 =
                   let uu____8469 = FStar_ST.op_Bang incl in ns1 ::
                     uu____8469 in
                 FStar_ST.op_Colon_Equals incl uu____8466);
            (match () with
             | () ->
                 let uu____8492 =
                   let uu____8500 = FStar_Ident.string_of_lid ns1 in
                   get_trans_exported_id_set env2 uu____8500 in
                 (match uu____8492 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____8513 =
                          let uu____8556 = get_exported_id_set env2 curmod in
                          let uu____8576 =
                            get_trans_exported_id_set env2 curmod in
                          (uu____8556, uu____8576) in
                        match uu____8513 with
                        | (FStar_Pervasives_Native.Some cur_exports,
                           FStar_Pervasives_Native.Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____8749 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____8749 in
                              let ex = cur_exports k in
                              (let uu____8784 =
                                 let uu____8787 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____8787 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____8784);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____8822 =
                                     let uu____8825 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____8825 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____8822) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____8844 -> ());
                       (match () with | () -> env2))
                  | FStar_Pervasives_Native.None ->
                      let uu____8892 =
                        let uu____8897 =
                          let uu____8898 = FStar_Ident.string_of_lid ns1 in
                          FStar_Util.format1
                            "include: Module %s was not prepared" uu____8898 in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____8897) in
                      let uu____8899 = FStar_Ident.range_of_lid ns1 in
                      FStar_Errors.raise_error uu____8892 uu____8899))))
      | uu____8900 ->
          let uu____8903 =
            let uu____8908 =
              let uu____8909 = FStar_Ident.string_of_lid ns in
              FStar_Util.format1 "include: Module %s cannot be found"
                uu____8909 in
            (FStar_Errors.Fatal_ModuleNotFound, uu____8908) in
          let uu____8910 = FStar_Ident.range_of_lid ns in
          FStar_Errors.raise_error uu____8903 uu____8910
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun x ->
      fun l ->
        let uu____8926 = module_is_defined env1 l in
        if uu____8926
        then
          ((env1.ds_hooks).ds_push_module_abbrev_hook env1 x l;
           push_scope_mod env1 (Module_abbrev (x, l)))
        else
          (let uu____8929 =
             let uu____8934 =
               let uu____8935 = FStar_Ident.string_of_lid l in
               FStar_Util.format1 "Module %s cannot be found" uu____8935 in
             (FStar_Errors.Fatal_ModuleNotFound, uu____8934) in
           let uu____8936 = FStar_Ident.range_of_lid l in
           FStar_Errors.raise_error uu____8929 uu____8936)
let (check_admits :
  env -> FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul) =
  fun env1 ->
    fun m ->
      let admitted_sig_lids =
        FStar_All.pipe_right env1.sigaccum
          (FStar_List.fold_left
             (fun lids ->
                fun se ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) when
                      let uu____8978 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
                      Prims.op_Negation uu____8978 ->
                      let uu____8981 =
                        let uu____8988 = FStar_Ident.string_of_lid l in
                        FStar_Util.smap_try_find (sigmap env1) uu____8988 in
                      (match uu____8981 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____8995;
                              FStar_Syntax_Syntax.sigrng = uu____8996;
                              FStar_Syntax_Syntax.sigquals = uu____8997;
                              FStar_Syntax_Syntax.sigmeta = uu____8998;
                              FStar_Syntax_Syntax.sigattrs = uu____8999;
                              FStar_Syntax_Syntax.sigopts = uu____9000;_},
                            uu____9001)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____9018;
                              FStar_Syntax_Syntax.sigrng = uu____9019;
                              FStar_Syntax_Syntax.sigquals = uu____9020;
                              FStar_Syntax_Syntax.sigmeta = uu____9021;
                              FStar_Syntax_Syntax.sigattrs = uu____9022;
                              FStar_Syntax_Syntax.sigopts = uu____9023;_},
                            uu____9024)
                           -> lids
                       | uu____9051 ->
                           ((let uu____9059 =
                               let uu____9060 = FStar_Options.interactive () in
                               Prims.op_Negation uu____9060 in
                             if uu____9059
                             then
                               let uu____9061 = FStar_Ident.range_of_lid l in
                               let uu____9062 =
                                 let uu____9067 =
                                   let uu____9068 =
                                     FStar_Ident.string_of_lid l in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____9068 in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____9067) in
                               FStar_Errors.log_issue uu____9061 uu____9062
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals) in
                             (let uu____9074 = FStar_Ident.string_of_lid l in
                              FStar_Util.smap_add (sigmap env1) uu____9074
                                ((let uu___1275_9080 = se in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (uu___1275_9080.FStar_Syntax_Syntax.sigel);
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___1275_9080.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals = quals;
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___1275_9080.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___1275_9080.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___1275_9080.FStar_Syntax_Syntax.sigopts)
                                  }), false));
                             l
                             ::
                             lids)))
                  | uu____9081 -> lids) []) in
      let uu___1280_9082 = m in
      let uu____9083 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid, uu____9093, uu____9094) when
                    FStar_List.existsb
                      (fun l -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1289_9097 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1289_9097.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1289_9097.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1289_9097.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1289_9097.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1289_9097.FStar_Syntax_Syntax.sigopts)
                    }
                | uu____9098 -> s)) in
      {
        FStar_Syntax_Syntax.name = (uu___1280_9082.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____9083;
        FStar_Syntax_Syntax.is_interface =
          (uu___1280_9082.FStar_Syntax_Syntax.is_interface)
      }
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env1 ->
    fun modul ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses, uu____9121) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun se1 ->
                            match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid, uu____9142, uu____9143, uu____9144,
                                 uu____9145, uu____9146)
                                ->
                                let uu____9151 =
                                  FStar_Ident.string_of_lid lid in
                                FStar_Util.smap_remove (sigmap env1)
                                  uu____9151
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid, univ_names, binders, typ, uu____9160,
                                 uu____9161)
                                ->
                                ((let uu____9171 =
                                    FStar_Ident.string_of_lid lid in
                                  FStar_Util.smap_remove (sigmap env1)
                                    uu____9171);
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____9177 =
                                        let uu____9184 =
                                          let uu____9185 =
                                            let uu____9186 =
                                              let uu____9201 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  typ in
                                              (binders, uu____9201) in
                                            FStar_Syntax_Syntax.Tm_arrow
                                              uu____9186 in
                                          let uu____9214 =
                                            FStar_Ident.range_of_lid lid in
                                          FStar_Syntax_Syntax.mk uu____9185
                                            uu____9214 in
                                        (lid, univ_names, uu____9184) in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____9177 in
                                    let se2 =
                                      let uu___1321_9216 = se1 in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1321_9216.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1321_9216.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1321_9216.FStar_Syntax_Syntax.sigattrs);
                                        FStar_Syntax_Syntax.sigopts =
                                          (uu___1321_9216.FStar_Syntax_Syntax.sigopts)
                                      } in
                                    let uu____9217 =
                                      FStar_Ident.string_of_lid lid in
                                    FStar_Util.smap_add (sigmap env1)
                                      uu____9217 (se2, false))
                                 else ())
                            | uu____9223 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid, uu____9226, uu____9227) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    let uu____9228 = FStar_Ident.string_of_lid lid in
                    FStar_Util.smap_remove (sigmap env1) uu____9228
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____9234, lbs), uu____9236)
                  ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_All.pipe_right lbs
                      (FStar_List.iter
                         (fun lb ->
                            let uu____9250 =
                              let uu____9251 =
                                let uu____9252 =
                                  let uu____9255 =
                                    FStar_Util.right
                                      lb.FStar_Syntax_Syntax.lbname in
                                  uu____9255.FStar_Syntax_Syntax.fv_name in
                                uu____9252.FStar_Syntax_Syntax.v in
                              FStar_Ident.string_of_lid uu____9251 in
                            FStar_Util.smap_remove (sigmap env1) uu____9250))
                  else ()
              | uu____9261 -> ()));
      (let curmod =
         let uu____9263 = current_module env1 in
         FStar_Ident.string_of_lid uu____9263 in
       (let uu____9265 =
          let uu____9308 = get_exported_id_set env1 curmod in
          let uu____9328 = get_trans_exported_id_set env1 curmod in
          (uu____9308, uu____9328) in
        match uu____9265 with
        | (FStar_Pervasives_Native.Some cur_ex, FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____9503 = cur_ex eikind in FStar_ST.op_Bang uu____9503 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____9541 =
                let uu____9544 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____9544 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____9541 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____9563 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1354_9607 = env1 in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1354_9607.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env1.modules));
                    scope_mods = [];
                    exported_ids = (uu___1354_9607.exported_ids);
                    trans_exported_ids = (uu___1354_9607.trans_exported_ids);
                    includes = (uu___1354_9607.includes);
                    sigaccum = [];
                    sigmap = (uu___1354_9607.sigmap);
                    iface = (uu___1354_9607.iface);
                    admitted_iface = (uu___1354_9607.admitted_iface);
                    expect_typ = (uu___1354_9607.expect_typ);
                    remaining_iface_decls =
                      (uu___1354_9607.remaining_iface_decls);
                    syntax_only = (uu___1354_9607.syntax_only);
                    ds_hooks = (uu___1354_9607.ds_hooks);
                    dep_graph = (uu___1354_9607.dep_graph)
                  }))))
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push : env -> env) =
  fun env1 ->
    FStar_Util.atomically
      (fun uu____9631 ->
         push_record_cache ();
         (let uu____9634 =
            let uu____9637 = FStar_ST.op_Bang stack in env1 :: uu____9637 in
          FStar_ST.op_Colon_Equals stack uu____9634);
         (let uu___1360_9660 = env1 in
          let uu____9661 = FStar_Util.smap_copy env1.exported_ids in
          let uu____9666 = FStar_Util.smap_copy env1.trans_exported_ids in
          let uu____9671 = FStar_Util.smap_copy env1.includes in
          let uu____9682 = FStar_Util.smap_copy env1.sigmap in
          {
            curmodule = (uu___1360_9660.curmodule);
            curmonad = (uu___1360_9660.curmonad);
            modules = (uu___1360_9660.modules);
            scope_mods = (uu___1360_9660.scope_mods);
            exported_ids = uu____9661;
            trans_exported_ids = uu____9666;
            includes = uu____9671;
            sigaccum = (uu___1360_9660.sigaccum);
            sigmap = uu____9682;
            iface = (uu___1360_9660.iface);
            admitted_iface = (uu___1360_9660.admitted_iface);
            expect_typ = (uu___1360_9660.expect_typ);
            remaining_iface_decls = (uu___1360_9660.remaining_iface_decls);
            syntax_only = (uu___1360_9660.syntax_only);
            ds_hooks = (uu___1360_9660.ds_hooks);
            dep_graph = (uu___1360_9660.dep_graph)
          }))
let (pop : unit -> env) =
  fun uu____9697 ->
    FStar_Util.atomically
      (fun uu____9704 ->
         let uu____9705 = FStar_ST.op_Bang stack in
         match uu____9705 with
         | env1::tl ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl; env1)
         | uu____9734 -> failwith "Impossible: Too many pops")
let (snapshot : env -> (Prims.int * env)) =
  fun env1 -> FStar_Common.snapshot push stack env1
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth -> FStar_Common.rollback pop stack depth
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m ->
    fun env1 ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____9772 ->
            let uu____9775 = FStar_Ident.nsstr l in
            let uu____9776 = FStar_Ident.string_of_lid m in
            uu____9775 = uu____9776
        | uu____9777 -> false in
      let sm = sigmap env1 in
      let env2 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env2 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k ->
              let uu____9811 = FStar_Util.smap_try_find sm' k in
              match uu____9811 with
              | FStar_Pervasives_Native.Some (se, true) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) ->
                          let uu___1395_9836 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1395_9836.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1395_9836.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1395_9836.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1395_9836.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___1395_9836.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____9837 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____9842 -> ()));
      env2
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env1 ->
    fun modul ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env1 modul
        else modul in
      let uu____9865 = finish env1 modul1 in (uu____9865, modul1)
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list ;
  exported_id_fields: Prims.string Prims.list }
let (__proj__Mkexported_ids__item__exported_id_terms :
  exported_ids -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { exported_id_terms; exported_id_fields;_} -> exported_id_terms
let (__proj__Mkexported_ids__item__exported_id_fields :
  exported_ids -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { exported_id_terms; exported_id_fields;_} -> exported_id_fields
let (as_exported_ids : exported_id_set -> exported_ids) =
  fun e ->
    let terms =
      let uu____9920 =
        let uu____9923 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____9923 in
      FStar_Util.set_elements uu____9920 in
    let fields =
      let uu____9945 =
        let uu____9948 = e Exported_id_field in FStar_ST.op_Bang uu____9948 in
      FStar_Util.set_elements uu____9945 in
    { exported_id_terms = terms; exported_id_fields = fields }
let (as_exported_id_set :
  exported_ids FStar_Pervasives_Native.option ->
    exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref)
  =
  fun e ->
    match e with
    | FStar_Pervasives_Native.None -> exported_id_set_new ()
    | FStar_Pervasives_Native.Some e1 ->
        let terms =
          let uu____9996 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____9996 in
        let fields =
          let uu____10006 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____10006 in
        (fun uu___29_10011 ->
           match uu___29_10011 with
           | Exported_id_term_type -> terms
           | Exported_id_field -> fields)
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option }
let (__proj__Mkmodule_inclusion_info__item__mii_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { mii_exported_ids; mii_trans_exported_ids; mii_includes;_} ->
        mii_exported_ids
let (__proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { mii_exported_ids; mii_trans_exported_ids; mii_includes;_} ->
        mii_trans_exported_ids
let (__proj__Mkmodule_inclusion_info__item__mii_includes :
  module_inclusion_info ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { mii_exported_ids; mii_trans_exported_ids; mii_includes;_} ->
        mii_includes
let (default_mii : module_inclusion_info) =
  {
    mii_exported_ids = FStar_Pervasives_Native.None;
    mii_trans_exported_ids = FStar_Pervasives_Native.None;
    mii_includes = FStar_Pervasives_Native.None
  }
let as_includes :
  'uuuuuu10109 .
    'uuuuuu10109 Prims.list FStar_Pervasives_Native.option ->
      'uuuuuu10109 Prims.list FStar_ST.ref
  =
  fun uu___30_10122 ->
    match uu___30_10122 with
    | FStar_Pervasives_Native.None -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env1 ->
    fun l ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____10163 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____10163 as_exported_ids in
      let uu____10169 = as_ids_opt env1.exported_ids in
      let uu____10172 = as_ids_opt env1.trans_exported_ids in
      let uu____10175 =
        let uu____10180 = FStar_Util.smap_try_find env1.includes mname in
        FStar_Util.map_opt uu____10180 (fun r -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____10169;
        mii_trans_exported_ids = uu____10172;
        mii_includes = uu____10175
      }
let (prepare_module_or_interface :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident -> module_inclusion_info -> (env * Prims.bool))
  =
  fun intf ->
    fun admitted ->
      fun env1 ->
        fun mname ->
          fun mii ->
            let prep env2 =
              let filename =
                let uu____10249 = FStar_Ident.string_of_lid mname in
                FStar_Util.strcat uu____10249 ".fst" in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename in
              let auto_open1 =
                let convert_kind uu___31_10269 =
                  match uu___31_10269 with
                  | FStar_Parser_Dep.Open_namespace -> Open_namespace
                  | FStar_Parser_Dep.Open_module -> Open_module in
                FStar_List.map
                  (fun uu____10281 ->
                     match uu____10281 with
                     | (lid, kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                let uu____10299 =
                  let uu____10300 =
                    let uu____10301 = FStar_Ident.ns_of_lid mname in
                    FStar_List.length uu____10301 in
                  uu____10300 > Prims.int_zero in
                if uu____10299
                then
                  let uu____10310 =
                    let uu____10315 =
                      let uu____10316 = FStar_Ident.ns_of_lid mname in
                      FStar_Ident.lid_of_ids uu____10316 in
                    (uu____10315, Open_namespace) in
                  [uu____10310]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____10346 = FStar_Ident.string_of_lid mname in
               let uu____10347 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env2.exported_ids uu____10346 uu____10347);
              (match () with
               | () ->
                   ((let uu____10352 = FStar_Ident.string_of_lid mname in
                     let uu____10353 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env2.trans_exported_ids uu____10352
                       uu____10353);
                    (match () with
                     | () ->
                         ((let uu____10358 = FStar_Ident.string_of_lid mname in
                           let uu____10359 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env2.includes uu____10358
                             uu____10359);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1465_10369 = env2 in
                                 let uu____10370 =
                                   FStar_List.map
                                     (fun x -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1465_10369.curmonad);
                                   modules = (uu___1465_10369.modules);
                                   scope_mods = uu____10370;
                                   exported_ids =
                                     (uu___1465_10369.exported_ids);
                                   trans_exported_ids =
                                     (uu___1465_10369.trans_exported_ids);
                                   includes = (uu___1465_10369.includes);
                                   sigaccum = (uu___1465_10369.sigaccum);
                                   sigmap = (env2.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1465_10369.expect_typ);
                                   remaining_iface_decls =
                                     (uu___1465_10369.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1465_10369.syntax_only);
                                   ds_hooks = (uu___1465_10369.ds_hooks);
                                   dep_graph = (uu___1465_10369.dep_graph)
                                 } in
                               (FStar_List.iter
                                  (fun op ->
                                     (env2.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____10382 =
              FStar_All.pipe_right env1.modules
                (FStar_Util.find_opt
                   (fun uu____10408 ->
                      match uu____10408 with
                      | (l, uu____10414) -> FStar_Ident.lid_equals l mname)) in
            match uu____10382 with
            | FStar_Pervasives_Native.None ->
                let uu____10423 = prep env1 in (uu____10423, false)
            | FStar_Pervasives_Native.Some (uu____10424, m) ->
                ((let uu____10431 =
                    (let uu____10434 = FStar_Options.interactive () in
                     Prims.op_Negation uu____10434) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____10431
                  then
                    let uu____10435 =
                      let uu____10440 =
                        let uu____10441 = FStar_Ident.string_of_lid mname in
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          uu____10441 in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____10440) in
                    let uu____10442 = FStar_Ident.range_of_lid mname in
                    FStar_Errors.raise_error uu____10435 uu____10442
                  else ());
                 (let uu____10444 =
                    let uu____10445 = push env1 in prep uu____10445 in
                  (uu____10444, true)))
let (enter_monad_scope : env -> FStar_Ident.ident -> env) =
  fun env1 ->
    fun mname ->
      match env1.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          let uu____10457 =
            let uu____10462 =
              let uu____10463 =
                let uu____10464 = FStar_Ident.string_of_id mname in
                let uu____10465 =
                  let uu____10466 = FStar_Ident.string_of_id mname' in
                  Prims.op_Hat ", but already in monad scope " uu____10466 in
                Prims.op_Hat uu____10464 uu____10465 in
              Prims.op_Hat "Trying to define monad " uu____10463 in
            (FStar_Errors.Fatal_MonadAlreadyDefined, uu____10462) in
          let uu____10467 = FStar_Ident.range_of_id mname in
          FStar_Errors.raise_error uu____10457 uu____10467
      | FStar_Pervasives_Native.None ->
          let uu___1486_10468 = env1 in
          {
            curmodule = (uu___1486_10468.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1486_10468.modules);
            scope_mods = (uu___1486_10468.scope_mods);
            exported_ids = (uu___1486_10468.exported_ids);
            trans_exported_ids = (uu___1486_10468.trans_exported_ids);
            includes = (uu___1486_10468.includes);
            sigaccum = (uu___1486_10468.sigaccum);
            sigmap = (uu___1486_10468.sigmap);
            iface = (uu___1486_10468.iface);
            admitted_iface = (uu___1486_10468.admitted_iface);
            expect_typ = (uu___1486_10468.expect_typ);
            remaining_iface_decls = (uu___1486_10468.remaining_iface_decls);
            syntax_only = (uu___1486_10468.syntax_only);
            ds_hooks = (uu___1486_10468.ds_hooks);
            dep_graph = (uu___1486_10468.dep_graph)
          }
let fail_or :
  'a .
    env ->
      (FStar_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStar_Ident.lident -> 'a
  =
  fun env1 ->
    fun lookup ->
      fun lid ->
        let uu____10502 = lookup lid in
        match uu____10502 with
        | FStar_Pervasives_Native.None ->
            let opened_modules =
              FStar_List.map
                (fun uu____10515 ->
                   match uu____10515 with
                   | (lid1, uu____10521) -> FStar_Ident.string_of_lid lid1)
                env1.modules in
            let msg =
              let uu____10523 = FStar_Ident.string_of_lid lid in
              FStar_Util.format1 "Identifier not found: [%s]" uu____10523 in
            let msg1 =
              let uu____10525 =
                let uu____10526 =
                  let uu____10527 = FStar_Ident.ns_of_lid lid in
                  FStar_List.length uu____10527 in
                uu____10526 = Prims.int_zero in
              if uu____10525
              then msg
              else
                (let modul =
                   let uu____10532 =
                     let uu____10533 = FStar_Ident.ns_of_lid lid in
                     FStar_Ident.lid_of_ids uu____10533 in
                   let uu____10534 = FStar_Ident.range_of_lid lid in
                   FStar_Ident.set_lid_range uu____10532 uu____10534 in
                 let uu____10535 = resolve_module_name env1 modul true in
                 match uu____10535 with
                 | FStar_Pervasives_Native.None ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     let uu____10539 = FStar_Ident.string_of_lid modul in
                     FStar_Util.format3
                       "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                       msg uu____10539 opened_modules1
                 | FStar_Pervasives_Native.Some modul' when
                     Prims.op_Negation
                       (FStar_List.existsb
                          (fun m ->
                             let uu____10544 =
                               FStar_Ident.string_of_lid modul' in
                             m = uu____10544) opened_modules)
                     ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     let uu____10546 = FStar_Ident.string_of_lid modul in
                     let uu____10547 = FStar_Ident.string_of_lid modul' in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                       msg uu____10546 uu____10547 opened_modules1
                 | FStar_Pervasives_Native.Some modul' ->
                     let uu____10549 = FStar_Ident.string_of_lid modul in
                     let uu____10550 = FStar_Ident.string_of_lid modul' in
                     let uu____10551 =
                       let uu____10552 = FStar_Ident.ident_of_lid lid in
                       FStar_Ident.string_of_id uu____10552 in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, definition %s not found"
                       msg uu____10549 uu____10550 uu____10551) in
            let uu____10553 = FStar_Ident.range_of_lid lid in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____10553
        | FStar_Pervasives_Native.Some r -> r
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup ->
    fun id ->
      let uu____10581 = lookup id in
      match uu____10581 with
      | FStar_Pervasives_Native.None ->
          let uu____10584 =
            let uu____10589 =
              let uu____10590 =
                let uu____10591 = FStar_Ident.string_of_id id in
                Prims.op_Hat uu____10591 "]" in
              Prims.op_Hat "Identifier not found [" uu____10590 in
            (FStar_Errors.Fatal_IdentifierNotFound, uu____10589) in
          let uu____10592 = FStar_Ident.range_of_id id in
          FStar_Errors.raise_error uu____10584 uu____10592
      | FStar_Pervasives_Native.Some r -> r