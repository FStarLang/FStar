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
    match projectee with | Open_module -> true | uu____59 -> false
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_namespace -> true | uu____70 -> false
type open_module_or_namespace = (FStar_Ident.lident * open_kind)
type record_or_dc =
  {
  typename: FStar_Ident.lident ;
  constrname: FStar_Ident.ident ;
  parms: FStar_Syntax_Syntax.binders ;
  fields: (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list ;
  is_private_or_abstract: Prims.bool ;
  is_record: Prims.bool }
let (__proj__Mkrecord_or_dc__item__typename :
  record_or_dc -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> typename
let (__proj__Mkrecord_or_dc__item__constrname :
  record_or_dc -> FStar_Ident.ident) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> constrname
let (__proj__Mkrecord_or_dc__item__parms :
  record_or_dc -> FStar_Syntax_Syntax.binders) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> parms
let (__proj__Mkrecord_or_dc__item__fields :
  record_or_dc -> (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> fields
let (__proj__Mkrecord_or_dc__item__is_private_or_abstract :
  record_or_dc -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> is_private_or_abstract
let (__proj__Mkrecord_or_dc__item__is_record : record_or_dc -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> is_record
type scope_mod =
  | Local_binding of local_binding 
  | Rec_binding of rec_binding 
  | Module_abbrev of module_abbrev 
  | Open_module_or_namespace of open_module_or_namespace 
  | Top_level_def of FStar_Ident.ident 
  | Record_or_dc of record_or_dc 
let (uu___is_Local_binding : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Local_binding _0 -> true | uu____294 -> false
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee -> match projectee with | Local_binding _0 -> _0
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Rec_binding _0 -> true | uu____313 -> false
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee -> match projectee with | Rec_binding _0 -> _0
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Module_abbrev _0 -> true | uu____332 -> false
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee -> match projectee with | Module_abbrev _0 -> _0
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____351 -> false
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee -> match projectee with | Open_module_or_namespace _0 -> _0
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Top_level_def _0 -> true | uu____370 -> false
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Top_level_def _0 -> _0
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_or_dc _0 -> true | uu____389 -> false
let (__proj__Record_or_dc__item___0 : scope_mod -> record_or_dc) =
  fun projectee -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStar_Util.set
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field 
let (uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_term_type -> true | uu____410 -> false
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_field -> true | uu____421 -> false
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
    ds_push_open_hook = (fun uu____1890 -> fun uu____1891 -> ());
    ds_push_include_hook = (fun uu____1894 -> fun uu____1895 -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1899 -> fun uu____1900 -> fun uu____1901 -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Term_name _0 -> true | uu____1938 -> false
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee -> match projectee with | Term_name _0 -> _0
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Eff_name _0 -> true | uu____1979 -> false
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee -> match projectee with | Eff_name _0 -> _0
let (set_iface : env -> Prims.bool -> env) =
  fun env1 ->
    fun b ->
      let uu___126_2013 = env1 in
      {
        curmodule = (uu___126_2013.curmodule);
        curmonad = (uu___126_2013.curmonad);
        modules = (uu___126_2013.modules);
        scope_mods = (uu___126_2013.scope_mods);
        exported_ids = (uu___126_2013.exported_ids);
        trans_exported_ids = (uu___126_2013.trans_exported_ids);
        includes = (uu___126_2013.includes);
        sigaccum = (uu___126_2013.sigaccum);
        sigmap = (uu___126_2013.sigmap);
        iface = b;
        admitted_iface = (uu___126_2013.admitted_iface);
        expect_typ = (uu___126_2013.expect_typ);
        remaining_iface_decls = (uu___126_2013.remaining_iface_decls);
        syntax_only = (uu___126_2013.syntax_only);
        ds_hooks = (uu___126_2013.ds_hooks);
        dep_graph = (uu___126_2013.dep_graph)
      }
let (iface : env -> Prims.bool) = fun e -> e.iface
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___131_2034 = e in
      {
        curmodule = (uu___131_2034.curmodule);
        curmonad = (uu___131_2034.curmonad);
        modules = (uu___131_2034.modules);
        scope_mods = (uu___131_2034.scope_mods);
        exported_ids = (uu___131_2034.exported_ids);
        trans_exported_ids = (uu___131_2034.trans_exported_ids);
        includes = (uu___131_2034.includes);
        sigaccum = (uu___131_2034.sigaccum);
        sigmap = (uu___131_2034.sigmap);
        iface = (uu___131_2034.iface);
        admitted_iface = b;
        expect_typ = (uu___131_2034.expect_typ);
        remaining_iface_decls = (uu___131_2034.remaining_iface_decls);
        syntax_only = (uu___131_2034.syntax_only);
        ds_hooks = (uu___131_2034.ds_hooks);
        dep_graph = (uu___131_2034.dep_graph)
      }
let (admitted_iface : env -> Prims.bool) = fun e -> e.admitted_iface
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___136_2055 = e in
      {
        curmodule = (uu___136_2055.curmodule);
        curmonad = (uu___136_2055.curmonad);
        modules = (uu___136_2055.modules);
        scope_mods = (uu___136_2055.scope_mods);
        exported_ids = (uu___136_2055.exported_ids);
        trans_exported_ids = (uu___136_2055.trans_exported_ids);
        includes = (uu___136_2055.includes);
        sigaccum = (uu___136_2055.sigaccum);
        sigmap = (uu___136_2055.sigmap);
        iface = (uu___136_2055.iface);
        admitted_iface = (uu___136_2055.admitted_iface);
        expect_typ = b;
        remaining_iface_decls = (uu___136_2055.remaining_iface_decls);
        syntax_only = (uu___136_2055.syntax_only);
        ds_hooks = (uu___136_2055.ds_hooks);
        dep_graph = (uu___136_2055.dep_graph)
      }
let (expect_typ : env -> Prims.bool) = fun e -> e.expect_typ
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type]
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env1 ->
    fun lid ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____2082 =
        FStar_Util.smap_try_find env1.trans_exported_ids module_name in
      match uu____2082 with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some exported_id_set1 ->
          let uu____2095 =
            let uu____2099 = exported_id_set1 Exported_id_term_type in
            FStar_ST.op_Bang uu____2099 in
          FStar_All.pipe_right uu____2095 FStar_Util.set_elements
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e -> e.modules
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env1 ->
    FStar_List.filter_map
      (fun uu___0_2187 ->
         match uu___0_2187 with
         | Open_module_or_namespace (lid, _info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2192 -> FStar_Pervasives_Native.None) env1.scope_mods
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e ->
    fun l ->
      let uu___155_2204 = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___155_2204.curmonad);
        modules = (uu___155_2204.modules);
        scope_mods = (uu___155_2204.scope_mods);
        exported_ids = (uu___155_2204.exported_ids);
        trans_exported_ids = (uu___155_2204.trans_exported_ids);
        includes = (uu___155_2204.includes);
        sigaccum = (uu___155_2204.sigaccum);
        sigmap = (uu___155_2204.sigmap);
        iface = (uu___155_2204.iface);
        admitted_iface = (uu___155_2204.admitted_iface);
        expect_typ = (uu___155_2204.expect_typ);
        remaining_iface_decls = (uu___155_2204.remaining_iface_decls);
        syntax_only = (uu___155_2204.syntax_only);
        ds_hooks = (uu___155_2204.ds_hooks);
        dep_graph = (uu___155_2204.dep_graph)
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
      let uu____2228 =
        FStar_All.pipe_right env1.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2262 ->
                match uu____2262 with
                | (m, uu____2271) -> FStar_Ident.lid_equals l m)) in
      match uu____2228 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2288, decls) ->
          FStar_Pervasives_Native.Some decls
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env1 ->
    fun l ->
      fun ds ->
        let uu____2322 =
          FStar_List.partition
            (fun uu____2352 ->
               match uu____2352 with
               | (m, uu____2361) -> FStar_Ident.lid_equals l m)
            env1.remaining_iface_decls in
        match uu____2322 with
        | (uu____2366, rest) ->
            let uu___180_2400 = env1 in
            {
              curmodule = (uu___180_2400.curmodule);
              curmonad = (uu___180_2400.curmonad);
              modules = (uu___180_2400.modules);
              scope_mods = (uu___180_2400.scope_mods);
              exported_ids = (uu___180_2400.exported_ids);
              trans_exported_ids = (uu___180_2400.trans_exported_ids);
              includes = (uu___180_2400.includes);
              sigaccum = (uu___180_2400.sigaccum);
              sigmap = (uu___180_2400.sigmap);
              iface = (uu___180_2400.iface);
              admitted_iface = (uu___180_2400.admitted_iface);
              expect_typ = (uu___180_2400.expect_typ);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___180_2400.syntax_only);
              ds_hooks = (uu___180_2400.ds_hooks);
              dep_graph = (uu___180_2400.dep_graph)
            }
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Ident.qual_id
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env1 ->
    fun id ->
      match env1.curmonad with
      | FStar_Pervasives_Native.None ->
          let uu____2429 = current_module env1 in qual uu____2429 id
      | FStar_Pervasives_Native.Some monad ->
          let uu____2431 =
            let uu____2432 = current_module env1 in qual uu____2432 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2431 id
let (syntax_only : env -> Prims.bool) = fun env1 -> env1.syntax_only
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env1 ->
    fun b ->
      let uu___190_2453 = env1 in
      {
        curmodule = (uu___190_2453.curmodule);
        curmonad = (uu___190_2453.curmonad);
        modules = (uu___190_2453.modules);
        scope_mods = (uu___190_2453.scope_mods);
        exported_ids = (uu___190_2453.exported_ids);
        trans_exported_ids = (uu___190_2453.trans_exported_ids);
        includes = (uu___190_2453.includes);
        sigaccum = (uu___190_2453.sigaccum);
        sigmap = (uu___190_2453.sigmap);
        iface = (uu___190_2453.iface);
        admitted_iface = (uu___190_2453.admitted_iface);
        expect_typ = (uu___190_2453.expect_typ);
        remaining_iface_decls = (uu___190_2453.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___190_2453.ds_hooks);
        dep_graph = (uu___190_2453.dep_graph)
      }
let (ds_hooks : env -> dsenv_hooks) = fun env1 -> env1.ds_hooks
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env1 ->
    fun hooks ->
      let uu___195_2471 = env1 in
      {
        curmodule = (uu___195_2471.curmodule);
        curmonad = (uu___195_2471.curmonad);
        modules = (uu___195_2471.modules);
        scope_mods = (uu___195_2471.scope_mods);
        exported_ids = (uu___195_2471.exported_ids);
        trans_exported_ids = (uu___195_2471.trans_exported_ids);
        includes = (uu___195_2471.includes);
        sigaccum = (uu___195_2471.sigaccum);
        sigmap = (uu___195_2471.sigmap);
        iface = (uu___195_2471.iface);
        admitted_iface = (uu___195_2471.admitted_iface);
        expect_typ = (uu___195_2471.expect_typ);
        remaining_iface_decls = (uu___195_2471.remaining_iface_decls);
        syntax_only = (uu___195_2471.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___195_2471.dep_graph)
      }
let new_sigmap : 'uuuuuu2477 . unit -> 'uuuuuu2477 FStar_Util.smap =
  fun uu____2484 -> FStar_Util.smap_create (Prims.of_int (100))
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps ->
    let uu____2492 = new_sigmap () in
    let uu____2497 = new_sigmap () in
    let uu____2502 = new_sigmap () in
    let uu____2513 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2492;
      trans_exported_ids = uu____2497;
      includes = uu____2502;
      sigaccum = [];
      sigmap = uu____2513;
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
      let uu___202_2557 = env1 in
      {
        curmodule = (uu___202_2557.curmodule);
        curmonad = (uu___202_2557.curmonad);
        modules = (uu___202_2557.modules);
        scope_mods = (uu___202_2557.scope_mods);
        exported_ids = (uu___202_2557.exported_ids);
        trans_exported_ids = (uu___202_2557.trans_exported_ids);
        includes = (uu___202_2557.includes);
        sigaccum = (uu___202_2557.sigaccum);
        sigmap = (uu___202_2557.sigmap);
        iface = (uu___202_2557.iface);
        admitted_iface = (uu___202_2557.admitted_iface);
        expect_typ = (uu___202_2557.expect_typ);
        remaining_iface_decls = (uu___202_2557.remaining_iface_decls);
        syntax_only = (uu___202_2557.syntax_only);
        ds_hooks = (uu___202_2557.ds_hooks);
        dep_graph = ds
      }
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env1 -> env1.sigmap
let (has_all_in_scope : env -> Prims.bool) =
  fun env1 ->
    FStar_List.existsb
      (fun uu____2585 ->
         match uu____2585 with
         | (m, uu____2592) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
      env1.modules
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv ->
    fun r ->
      let id = FStar_Ident.set_id_range r bv.FStar_Syntax_Syntax.ppname in
      let uu___212_2605 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___212_2605.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___212_2605.FStar_Syntax_Syntax.sort)
      }
let (bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun bv ->
    fun r ->
      let uu____2617 = set_bv_range bv r in
      FStar_Syntax_Syntax.bv_to_name uu____2617
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
      (fun uu____2710 ->
         match uu____2710 with
         | (x, y, dd, dq) ->
             let uu____2737 =
               let uu____2739 = FStar_Ident.string_of_id id in uu____2739 = x in
             if uu____2737
             then
               let uu____2745 =
                 let uu____2746 =
                   let uu____2747 = FStar_Ident.range_of_id id in
                   FStar_Ident.lid_of_path ["Prims"; y] uu____2747 in
                 FStar_Syntax_Syntax.fvar uu____2746 dd dq in
               FStar_Pervasives_Native.Some uu____2745
             else FStar_Pervasives_Native.None)
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_ok _0 -> true | uu____2787 -> false
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_fail -> true | uu____2824 -> false
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_ignore -> true | uu____2845 -> false
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore ->
    fun uu___1_2875 ->
      match uu___1_2875 with
      | Cont_ok a1 -> FStar_Pervasives_Native.Some a1
      | Cont_fail -> FStar_Pervasives_Native.None
      | Cont_ignore -> k_ignore ()
let find_in_record :
  'uuuuuu2894 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'uuuuuu2894 cont_t) -> 'uuuuuu2894 cont_t
  =
  fun ns ->
    fun id ->
      fun record ->
        fun cont ->
          let typename' =
            let uu____2931 =
              let uu____2932 =
                let uu____2935 = FStar_Ident.ident_of_lid record.typename in
                [uu____2935] in
              FStar_List.append ns uu____2932 in
            FStar_Ident.lid_of_ids uu____2931 in
          let uu____2936 = FStar_Ident.lid_equals typename' record.typename in
          if uu____2936
          then
            let fname =
              let uu____2942 =
                let uu____2943 = FStar_Ident.ns_of_lid record.typename in
                FStar_List.append uu____2943 [id] in
              FStar_Ident.lid_of_ids uu____2942 in
            let find =
              FStar_Util.find_map record.fields
                (fun uu____2957 ->
                   match uu____2957 with
                   | (f, uu____2965) ->
                       let uu____2966 =
                         let uu____2968 = FStar_Ident.string_of_id id in
                         let uu____2970 = FStar_Ident.string_of_id f in
                         uu____2968 = uu____2970 in
                       if uu____2966
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
  fun uu___2_3045 ->
    match uu___2_3045 with
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
              let rec aux uu___3_3121 =
                match uu___3_3121 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = FStar_Ident.string_of_lid modul in
                    let not_shadowed =
                      let uu____3134 = get_exported_id_set env1 mname in
                      match uu____3134 with
                      | FStar_Pervasives_Native.None -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____3161 = mex eikind in
                            FStar_ST.op_Bang uu____3161 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu____3223 =
                        FStar_Util.smap_try_find env1.includes mname in
                      match uu____3223 with
                      | FStar_Pervasives_Native.None -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3278 = qual modul id in
                        find_in_module uu____3278
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore -> aux (FStar_List.append mincludes q)
                     | uu____3283 -> look_into) in
              aux [ns]
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___4_3292 ->
    match uu___4_3292 with | Exported_id_field -> true | uu____3295 -> false
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
                  let check_local_binding_id uu___5_3419 =
                    match uu___5_3419 with
                    | (id', uu____3422, uu____3423) ->
                        let uu____3424 = FStar_Ident.string_of_id id' in
                        let uu____3426 = FStar_Ident.string_of_id id in
                        uu____3424 = uu____3426 in
                  let check_rec_binding_id uu___6_3435 =
                    match uu___6_3435 with
                    | (id', uu____3438, uu____3439, uu____3440) ->
                        let uu____3441 = FStar_Ident.string_of_id id' in
                        let uu____3443 = FStar_Ident.string_of_id id in
                        uu____3441 = uu____3443 in
                  let curmod_ns =
                    let uu____3447 = current_module env1 in
                    FStar_Ident.ids_of_lid uu____3447 in
                  let proc uu___7_3455 =
                    match uu___7_3455 with
                    | Local_binding l when check_local_binding_id l ->
                        let uu____3459 = l in
                        (match uu____3459 with
                         | (uu____3462, uu____3463, used_marker1) ->
                             (FStar_ST.op_Colon_Equals used_marker1 true;
                              k_local_binding l))
                    | Rec_binding r when check_rec_binding_id r ->
                        let uu____3489 = r in
                        (match uu____3489 with
                         | (uu____3492, uu____3493, uu____3494, used_marker1)
                             ->
                             (FStar_ST.op_Colon_Equals used_marker1 true;
                              k_rec_binding r))
                    | Open_module_or_namespace (ns, Open_module) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env1 ns id
                    | Top_level_def id' when
                        let uu____3521 = FStar_Ident.string_of_id id' in
                        let uu____3523 = FStar_Ident.string_of_id id in
                        uu____3521 = uu____3523 ->
                        lookup_default_id Cont_ignore id
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____3527 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid ->
                             let id1 = FStar_Ident.ident_of_lid lid in
                             let uu____3533 = FStar_Ident.ns_of_lid lid in
                             find_in_record uu____3533 id1 r k_record)
                          Cont_ignore env1 uu____3527 id
                    | uu____3536 -> Cont_ignore in
                  let rec aux uu___8_3546 =
                    match uu___8_3546 with
                    | a1::q ->
                        let uu____3555 = proc a1 in
                        option_of_cont (fun uu____3559 -> aux q) uu____3555
                    | [] ->
                        let uu____3560 = lookup_default_id Cont_fail id in
                        option_of_cont
                          (fun uu____3564 -> FStar_Pervasives_Native.None)
                          uu____3560 in
                  aux env1.scope_mods
let found_local_binding :
  'uuuuuu3574 'uuuuuu3575 .
    FStar_Range.range ->
      ('uuuuuu3574 * FStar_Syntax_Syntax.bv * 'uuuuuu3575) ->
        FStar_Syntax_Syntax.term
  =
  fun r ->
    fun uu____3591 ->
      match uu____3591 with | (id', x, uu____3600) -> bv_to_name x r
let find_in_module :
  'uuuuuu3612 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'uuuuuu3612)
          -> 'uuuuuu3612 -> 'uuuuuu3612
  =
  fun env1 ->
    fun lid ->
      fun k_global_def ->
        fun k_not_found ->
          let uu____3653 =
            let uu____3661 = FStar_Ident.string_of_lid lid in
            FStar_Util.smap_try_find (sigmap env1) uu____3661 in
          match uu____3653 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None -> k_not_found
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun id ->
      let uu____3699 = unmangleOpName id in
      match uu____3699 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3705 ->
          try_lookup_id'' env1 id Exported_id_term_type
            (fun r ->
               let uu____3711 =
                 let uu____3712 = FStar_Ident.range_of_id id in
                 found_local_binding uu____3712 r in
               Cont_ok uu____3711) (fun uu____3714 -> Cont_fail)
            (fun uu____3716 -> Cont_ignore)
            (fun i ->
               find_in_module env1 i
                 (fun uu____3723 -> fun uu____3724 -> Cont_fail) Cont_ignore)
            (fun uu____3732 -> fun uu____3733 -> Cont_fail)
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
            | FStar_Pervasives_Native.Some uu____3807 ->
                let lid = qualify env1 id in
                let uu____3809 =
                  let uu____3817 = FStar_Ident.string_of_lid lid in
                  FStar_Util.smap_try_find (sigmap env1) uu____3817 in
                (match uu____3809 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3839 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu____3839
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v -> v
          | FStar_Pervasives_Native.None ->
              let lid =
                let uu____3863 = current_module env1 in qual uu____3863 id in
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
          let uu____3926 = FStar_Ident.ns_of_lid lid in
          FStar_List.length uu____3926 in
        let rec aux uu___9_3938 =
          match uu___9_3938 with
          | [] ->
              let uu____3943 = module_is_defined env1 lid in
              if uu____3943
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns
              ->
              let new_lid =
                let uu____3955 =
                  let uu____3956 = FStar_Ident.path_of_lid ns in
                  let uu____3960 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____3956 uu____3960 in
                let uu____3965 = FStar_Ident.range_of_lid lid in
                FStar_Ident.lid_of_path uu____3955 uu____3965 in
              let uu____3966 = module_is_defined env1 new_lid in
              if uu____3966
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name, modul))::uu____3975 when
              (nslen = Prims.int_zero) &&
                (let uu____3982 = FStar_Ident.string_of_id name in
                 let uu____3984 =
                   let uu____3986 = FStar_Ident.ident_of_lid lid in
                   FStar_Ident.string_of_id uu____3986 in
                 uu____3982 = uu____3984)
              -> FStar_Pervasives_Native.Some modul
          | uu____3988::q -> aux q in
        aux env1.scope_mods
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env1 ->
    fun lid ->
      fun open_kind1 ->
        FStar_List.existsb
          (fun uu___10_4012 ->
             match uu___10_4012 with
             | Open_module_or_namespace (ns, k) ->
                 (k = open_kind1) && (FStar_Ident.lid_equals lid ns)
             | uu____4016 -> false) env1.scope_mods
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
                 let uu____4145 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____4145
                   (FStar_Util.map_option
                      (fun uu____4195 ->
                         match uu____4195 with
                         | (stripped_ids, rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let do_shorten env2 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4265 = aux ns_rev_prefix ns_last_id in
              (match uu____4265 with
               | FStar_Pervasives_Native.None -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids))) in
        if is_full_path && ((FStar_List.length ids) > Prims.int_zero)
        then
          let uu____4328 =
            let uu____4331 = FStar_Ident.lid_of_ids ids in
            resolve_module_name env1 uu____4331 true in
          match uu____4328 with
          | FStar_Pervasives_Native.Some m when module_is_open env1 m ->
              (ids, [])
          | uu____4346 -> do_shorten env1 ids
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
                  let uu____4467 = FStar_Ident.ns_of_lid lid in
                  match uu____4467 with
                  | uu____4470::uu____4471 ->
                      let uu____4474 =
                        let uu____4477 =
                          let uu____4478 =
                            let uu____4479 = FStar_Ident.ns_of_lid lid in
                            FStar_Ident.lid_of_ids uu____4479 in
                          let uu____4480 = FStar_Ident.range_of_lid lid in
                          FStar_Ident.set_lid_range uu____4478 uu____4480 in
                        resolve_module_name env1 uu____4477 true in
                      (match uu____4474 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4485 =
                             let uu____4488 = FStar_Ident.ident_of_lid lid in
                             find_in_module_with_includes eikind f_module
                               Cont_fail env1 modul uu____4488 in
                           option_of_cont
                             (fun uu____4490 -> FStar_Pervasives_Native.None)
                             uu____4485)
                  | [] ->
                      let uu____4491 = FStar_Ident.ident_of_lid lid in
                      try_lookup_id'' env1 uu____4491 eikind k_local_binding
                        k_rec_binding k_record f_module l_default
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none ->
    fun uu___11_4515 ->
      match uu___11_4515 with
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
              let uu____4636 = k_global_def lid1 def in
              cont_of_option k uu____4636 in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env1 lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env1 i (k_global_def' k) k in
            resolve_in_open_namespaces'' env1 lid Exported_id_term_type
              (fun l ->
                 let uu____4672 = k_local_binding l in
                 cont_of_option Cont_fail uu____4672)
              (fun r ->
                 let uu____4678 = k_rec_binding r in
                 cont_of_option Cont_fail uu____4678)
              (fun uu____4682 -> Cont_ignore) f_module l_default
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4693, uu____4694, uu____4695, l, uu____4697, uu____4698) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___12_4711 ->
               match uu___12_4711 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4714, fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4726 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____4732, uu____4733, uu____4734) -> FStar_Pervasives_Native.None
    | uu____4735 -> FStar_Pervasives_Native.None
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs ->
    fun lid ->
      let uu____4751 =
        FStar_Util.find_map lbs
          (fun lb ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____4759 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____4759
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____4751 FStar_Util.must
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    fun ns ->
      (let uu____4784 =
         let uu____4785 = FStar_Ident.ns_of_lid lid in
         FStar_List.length uu____4785 in
       let uu____4788 =
         let uu____4789 = FStar_Ident.ids_of_lid ns in
         FStar_List.length uu____4789 in
       uu____4784 = uu____4788) &&
        (let uu____4793 =
           let uu____4794 = FStar_Ident.ns_of_lid lid in
           FStar_Ident.lid_of_ids uu____4794 in
         FStar_Ident.lid_equals uu____4793 ns)
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid ->
    fun quals ->
      let dd =
        let uu____4811 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___13_4818 ->
                     match uu___13_4818 with
                     | FStar_Syntax_Syntax.Projector uu____4820 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____4826 -> true
                     | uu____4828 -> false))) in
        if uu____4811
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant in
      let uu____4833 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___14_4839 ->
                 match uu___14_4839 with
                 | FStar_Syntax_Syntax.Abstract -> true
                 | uu____4842 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___15_4848 ->
                    match uu___15_4848 with
                    | FStar_Syntax_Syntax.Assumption -> true
                    | uu____4851 -> false)))
             &&
             (let uu____4854 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___16_4860 ->
                        match uu___16_4860 with
                        | FStar_Syntax_Syntax.New -> true
                        | uu____4863 -> false)) in
              Prims.op_Negation uu____4854)) in
      if uu____4833 then FStar_Syntax_Syntax.Delta_abstract dd else dd
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
          let k_global_def source_lid uu___19_4915 =
            match uu___19_4915 with
            | (uu____4923, true) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se, uu____4927) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4932 ->
                     let uu____4949 =
                       let uu____4950 =
                         let uu____4957 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____4957, (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4950 in
                     FStar_Pervasives_Native.Some uu____4949
                 | FStar_Syntax_Syntax.Sig_datacon uu____4960 ->
                     let uu____4976 =
                       let uu____4977 =
                         let uu____4984 =
                           let uu____4985 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____4985 in
                         (uu____4984, (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____4977 in
                     FStar_Pervasives_Native.Some uu____4976
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____4990, lbs), uu____4992) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____5004 =
                       let uu____5005 =
                         let uu____5012 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____5012, (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu____5005 in
                     FStar_Pervasives_Native.Some uu____5004
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1, uu____5016, uu____5017) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____5021 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___17_5027 ->
                                  match uu___17_5027 with
                                  | FStar_Syntax_Syntax.Assumption -> true
                                  | uu____5030 -> false))) in
                     if uu____5021
                     then
                       let lid2 =
                         let uu____5036 = FStar_Ident.range_of_lid source_lid in
                         FStar_Ident.set_lid_range lid1 uu____5036 in
                       let dd = delta_depth_of_declaration lid2 quals in
                       let uu____5038 =
                         FStar_Util.find_map quals
                           (fun uu___18_5043 ->
                              match uu___18_5043 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____5047 -> FStar_Pervasives_Native.None) in
                       (match uu____5038 with
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
                        | uu____5056 ->
                            let uu____5059 =
                              let uu____5060 =
                                let uu____5067 =
                                  let uu____5068 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____5068 in
                                (uu____5067,
                                  (se.FStar_Syntax_Syntax.sigattrs)) in
                              Term_name uu____5060 in
                            FStar_Pervasives_Native.Some uu____5059)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5076 =
                       let uu____5077 =
                         let uu____5082 =
                           let uu____5083 =
                             FStar_Ident.range_of_lid source_lid in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____5083 in
                         (se, uu____5082) in
                       Eff_name uu____5077 in
                     FStar_Pervasives_Native.Some uu____5076
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5084 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
                     let uu____5103 =
                       let uu____5104 =
                         let uu____5111 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                Prims.int_one) FStar_Pervasives_Native.None in
                         (uu____5111, []) in
                       Term_name uu____5104 in
                     FStar_Pervasives_Native.Some uu____5103
                 | uu____5115 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let t =
              let uu____5137 = FStar_Ident.range_of_lid lid in
              found_local_binding uu____5137 r in
            FStar_Pervasives_Native.Some (Term_name (t, [])) in
          let k_rec_binding uu____5195 =
            match uu____5195 with
            | (id, l, dd, used_marker1) ->
                (FStar_ST.op_Colon_Equals used_marker1 true;
                 (let uu____5353 =
                    let uu____5354 =
                      let uu____5361 =
                        let uu____5362 =
                          let uu____5363 = FStar_Ident.range_of_lid lid in
                          FStar_Ident.set_lid_range l uu____5363 in
                        FStar_Syntax_Syntax.fvar uu____5362 dd
                          FStar_Pervasives_Native.None in
                      (uu____5361, []) in
                    Term_name uu____5354 in
                  FStar_Pervasives_Native.Some uu____5353)) in
          let found_unmangled =
            let uu____5369 = FStar_Ident.ns_of_lid lid in
            match uu____5369 with
            | [] ->
                let uu____5372 =
                  let uu____5375 = FStar_Ident.ident_of_lid lid in
                  unmangleOpName uu____5375 in
                (match uu____5372 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____5381 -> FStar_Pervasives_Native.None)
            | uu____5384 -> FStar_Pervasives_Native.None in
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
        let uu____5420 = try_lookup_name true exclude_interf env1 lid in
        match uu____5420 with
        | FStar_Pervasives_Native.Some (Eff_name (o, l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____5436 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____5456 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu____5456 with
      | FStar_Pervasives_Native.Some (o, l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5471 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____5497 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu____5497 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5513;
             FStar_Syntax_Syntax.sigquals = uu____5514;
             FStar_Syntax_Syntax.sigmeta = uu____5515;
             FStar_Syntax_Syntax.sigattrs = uu____5516;
             FStar_Syntax_Syntax.sigopts = uu____5517;_},
           l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5537, uu____5538, uu____5539, uu____5540, cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5542;
             FStar_Syntax_Syntax.sigquals = uu____5543;
             FStar_Syntax_Syntax.sigmeta = uu____5544;
             FStar_Syntax_Syntax.sigattrs = uu____5545;
             FStar_Syntax_Syntax.sigopts = uu____5546;_},
           l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5570 -> FStar_Pervasives_Native.None
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____5596 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu____5596 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5606;
             FStar_Syntax_Syntax.sigquals = uu____5607;
             FStar_Syntax_Syntax.sigmeta = uu____5608;
             FStar_Syntax_Syntax.sigattrs = uu____5609;
             FStar_Syntax_Syntax.sigopts = uu____5610;_},
           uu____5611)
          -> FStar_Pervasives_Native.Some ne
      | uu____5622 -> FStar_Pervasives_Native.None
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu____5641 = try_lookup_effect_name env1 lid in
      match uu____5641 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____5646 -> true
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____5661 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu____5661 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l', uu____5671, uu____5672, uu____5673, uu____5674);
             FStar_Syntax_Syntax.sigrng = uu____5675;
             FStar_Syntax_Syntax.sigquals = uu____5676;
             FStar_Syntax_Syntax.sigmeta = uu____5677;
             FStar_Syntax_Syntax.sigattrs = uu____5678;
             FStar_Syntax_Syntax.sigopts = uu____5679;_},
           uu____5680)
          ->
          let rec aux new_name =
            let uu____5703 =
              let uu____5711 = FStar_Ident.string_of_lid new_name in
              FStar_Util.smap_try_find (sigmap env1) uu____5711 in
            match uu____5703 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s, uu____5726) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5737 =
                       let uu____5738 = FStar_Ident.range_of_lid l in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5738 in
                     FStar_Pervasives_Native.Some uu____5737
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5739, uu____5740, uu____5741, cmp, uu____5743) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____5749 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5750, l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5756 -> FStar_Pervasives_Native.None
let (lookup_letbinding_quals_and_attrs :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.qualifier Prims.list *
        FStar_Syntax_Syntax.attribute Prims.list))
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___20_5807 =
        match uu___20_5807 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5823, uu____5824, uu____5825);
             FStar_Syntax_Syntax.sigrng = uu____5826;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5828;
             FStar_Syntax_Syntax.sigattrs = attrs;
             FStar_Syntax_Syntax.sigopts = uu____5830;_},
           uu____5831) -> FStar_Pervasives_Native.Some (quals, attrs)
        | uu____5852 -> FStar_Pervasives_Native.None in
      let uu____5866 =
        resolve_in_open_namespaces' env1 lid
          (fun uu____5886 -> FStar_Pervasives_Native.None)
          (fun uu____5896 -> FStar_Pervasives_Native.None) k_global_def in
      match uu____5866 with
      | FStar_Pervasives_Native.Some qa -> qa
      | uu____5930 -> ([], [])
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun path ->
      let uu____5958 =
        FStar_List.tryFind
          (fun uu____5973 ->
             match uu____5973 with
             | (mlid, modul) ->
                 let uu____5981 = FStar_Ident.path_of_lid mlid in
                 uu____5981 = path) env1.modules in
      match uu____5958 with
      | FStar_Pervasives_Native.Some (uu____5984, modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___21_6024 =
        match uu___21_6024 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____6032, lbs), uu____6034);
             FStar_Syntax_Syntax.sigrng = uu____6035;
             FStar_Syntax_Syntax.sigquals = uu____6036;
             FStar_Syntax_Syntax.sigmeta = uu____6037;
             FStar_Syntax_Syntax.sigattrs = uu____6038;
             FStar_Syntax_Syntax.sigopts = uu____6039;_},
           uu____6040) ->
            let fv = lb_fv lbs lid1 in
            let uu____6060 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu____6060
        | uu____6061 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6068 -> FStar_Pervasives_Native.None)
        (fun uu____6070 -> FStar_Pervasives_Native.None) k_global_def
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___22_6103 =
        match uu___22_6103 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs, uu____6114);
             FStar_Syntax_Syntax.sigrng = uu____6115;
             FStar_Syntax_Syntax.sigquals = uu____6116;
             FStar_Syntax_Syntax.sigmeta = uu____6117;
             FStar_Syntax_Syntax.sigattrs = uu____6118;
             FStar_Syntax_Syntax.sigopts = uu____6119;_},
           uu____6120) ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____6148 -> FStar_Pervasives_Native.None)
        | uu____6155 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6166 -> FStar_Pervasives_Native.None)
        (fun uu____6170 -> FStar_Pervasives_Native.None) k_global_def
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
          let uu____6230 = try_lookup_name any_val exclude_interface env1 lid in
          match uu____6230 with
          | FStar_Pervasives_Native.Some (Term_name (e, attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____6255 -> FStar_Pervasives_Native.None
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x ->
    match x with
    | FStar_Pervasives_Native.Some (t, uu____6293) ->
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
      let uu____6351 = try_lookup_lid_with_attributes env1 l in
      FStar_All.pipe_right uu____6351 drop_attributes
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____6383 = try_lookup_lid env1 l in
      match uu____6383 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____6389 =
            let uu____6390 = FStar_Syntax_Subst.compress e in
            uu____6390.FStar_Syntax_Syntax.n in
          (match uu____6389 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____6396 -> FStar_Pervasives_Native.None)
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      let uu____6408 =
        let uu____6417 = FStar_Ident.ns_of_lid lid in
        shorten_module_path env1 uu____6417 true in
      match uu____6408 with
      | (uu____6421, short) ->
          let uu____6431 = FStar_Ident.ident_of_lid lid in
          FStar_Ident.lid_of_ns_and_id short uu____6431
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env1 ->
    fun lid ->
      match env1.curmodule with
      | FStar_Pervasives_Native.None -> shorten_lid' env1 lid
      | uu____6443 ->
          let lid_without_ns =
            let uu____6447 = FStar_Ident.ident_of_lid lid in
            FStar_Ident.lid_of_ns_and_id [] uu____6447 in
          let uu____6448 =
            resolve_to_fully_qualified_name env1 lid_without_ns in
          (match uu____6448 with
           | FStar_Pervasives_Native.Some lid' when
               let uu____6452 = FStar_Ident.string_of_lid lid' in
               let uu____6454 = FStar_Ident.string_of_lid lid in
               uu____6452 = uu____6454 -> lid_without_ns
           | uu____6457 -> shorten_lid' env1 lid)
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let env' =
        let uu___867_6488 = env1 in
        {
          curmodule = (uu___867_6488.curmodule);
          curmonad = (uu___867_6488.curmonad);
          modules = (uu___867_6488.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___867_6488.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___867_6488.sigaccum);
          sigmap = (uu___867_6488.sigmap);
          iface = (uu___867_6488.iface);
          admitted_iface = (uu___867_6488.admitted_iface);
          expect_typ = (uu___867_6488.expect_typ);
          remaining_iface_decls = (uu___867_6488.remaining_iface_decls);
          syntax_only = (uu___867_6488.syntax_only);
          ds_hooks = (uu___867_6488.ds_hooks);
          dep_graph = (uu___867_6488.dep_graph)
        } in
      try_lookup_lid_with_attributes env' l
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu____6504 = try_lookup_lid_with_attributes_no_resolve env1 l in
      FStar_All.pipe_right uu____6504 drop_attributes
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
               (uu____6561, uu____6562, uu____6563);
             FStar_Syntax_Syntax.sigrng = uu____6564;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6566;
             FStar_Syntax_Syntax.sigattrs = uu____6567;
             FStar_Syntax_Syntax.sigopts = uu____6568;_},
           uu____6569) ->
            let uu____6578 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___23_6584 ->
                      match uu___23_6584 with
                      | FStar_Syntax_Syntax.Assumption -> true
                      | uu____6587 -> false)) in
            if uu____6578
            then
              let uu____6592 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____6592
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6595;
             FStar_Syntax_Syntax.sigrng = uu____6596;
             FStar_Syntax_Syntax.sigquals = uu____6597;
             FStar_Syntax_Syntax.sigmeta = uu____6598;
             FStar_Syntax_Syntax.sigattrs = uu____6599;
             FStar_Syntax_Syntax.sigopts = uu____6600;_},
           uu____6601) ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se) in
            let uu____6629 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1 in
            FStar_Pervasives_Native.Some uu____6629
        | uu____6630 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6637 -> FStar_Pervasives_Native.None)
        (fun uu____6639 -> FStar_Pervasives_Native.None) k_global_def
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___24_6674 =
        match uu___24_6674 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6684, uu____6685, uu____6686, uu____6687, datas,
                uu____6689);
             FStar_Syntax_Syntax.sigrng = uu____6690;
             FStar_Syntax_Syntax.sigquals = uu____6691;
             FStar_Syntax_Syntax.sigmeta = uu____6692;
             FStar_Syntax_Syntax.sigattrs = uu____6693;
             FStar_Syntax_Syntax.sigopts = uu____6694;_},
           uu____6695) -> FStar_Pervasives_Native.Some datas
        | uu____6714 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6725 -> FStar_Pervasives_Native.None)
        (fun uu____6729 -> FStar_Pervasives_Native.None) k_global_def
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push uu____6808 =
    let uu____6809 =
      let uu____6814 =
        let uu____6817 = FStar_ST.op_Bang record_cache in
        FStar_List.hd uu____6817 in
      let uu____6851 = FStar_ST.op_Bang record_cache in uu____6814 ::
        uu____6851 in
    FStar_ST.op_Colon_Equals record_cache uu____6809 in
  let pop uu____6917 =
    let uu____6918 =
      let uu____6923 = FStar_ST.op_Bang record_cache in
      FStar_List.tl uu____6923 in
    FStar_ST.op_Colon_Equals record_cache uu____6918 in
  let snapshot uu____6994 = FStar_Common.snapshot push record_cache () in
  let rollback depth = FStar_Common.rollback pop record_cache depth in
  let peek uu____7018 =
    let uu____7019 = FStar_ST.op_Bang record_cache in
    FStar_List.hd uu____7019 in
  let insert r =
    let uu____7059 =
      let uu____7064 = let uu____7067 = peek () in r :: uu____7067 in
      let uu____7070 =
        let uu____7075 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____7075 in
      uu____7064 :: uu____7070 in
    FStar_ST.op_Colon_Equals record_cache uu____7059 in
  let filter uu____7143 =
    let rc = peek () in
    let filtered =
      FStar_List.filter (fun r -> Prims.op_Negation r.is_private_or_abstract)
        rc in
    let uu____7152 =
      let uu____7157 =
        let uu____7162 = FStar_ST.op_Bang record_cache in
        FStar_List.tl uu____7162 in
      filtered :: uu____7157 in
    FStar_ST.op_Colon_Equals record_cache uu____7152 in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs, uu____8088) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___25_8107 ->
                   match uu___25_8107 with
                   | FStar_Syntax_Syntax.RecordType uu____8109 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____8119 -> true
                   | uu____8129 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___26_8155 ->
                      match uu___26_8155 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid, uu____8158, uu____8159, uu____8160,
                             uu____8161, uu____8162);
                          FStar_Syntax_Syntax.sigrng = uu____8163;
                          FStar_Syntax_Syntax.sigquals = uu____8164;
                          FStar_Syntax_Syntax.sigmeta = uu____8165;
                          FStar_Syntax_Syntax.sigattrs = uu____8166;
                          FStar_Syntax_Syntax.sigopts = uu____8167;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____8180 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___27_8221 ->
                    match uu___27_8221 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename, univs, parms, uu____8225, uu____8226,
                           dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____8228;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____8230;
                        FStar_Syntax_Syntax.sigattrs = uu____8231;
                        FStar_Syntax_Syntax.sigopts = uu____8232;_} ->
                        let uu____8245 =
                          let uu____8246 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____8246 in
                        (match uu____8245 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname, uu____8252, t, uu____8254, n,
                                uu____8256);
                             FStar_Syntax_Syntax.sigrng = uu____8257;
                             FStar_Syntax_Syntax.sigquals = uu____8258;
                             FStar_Syntax_Syntax.sigmeta = uu____8259;
                             FStar_Syntax_Syntax.sigattrs = uu____8260;
                             FStar_Syntax_Syntax.sigopts = uu____8261;_} ->
                             let uu____8274 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____8274 with
                              | (all_formals, uu____8282) ->
                                  let uu____8287 =
                                    FStar_Util.first_N n all_formals in
                                  (match uu____8287 with
                                   | (_params, formals) ->
                                       let is_rec = is_record typename_quals in
                                       let formals' =
                                         FStar_All.pipe_right formals
                                           (FStar_List.collect
                                              (fun uu____8381 ->
                                                 match uu____8381 with
                                                 | (x, q) ->
                                                     let uu____8394 =
                                                       (FStar_Syntax_Syntax.is_null_bv
                                                          x)
                                                         ||
                                                         (is_rec &&
                                                            (FStar_Syntax_Syntax.is_implicit
                                                               q)) in
                                                     if uu____8394
                                                     then []
                                                     else [(x, q)])) in
                                       let fields' =
                                         FStar_All.pipe_right formals'
                                           (FStar_List.map
                                              (fun uu____8449 ->
                                                 match uu____8449 with
                                                 | (x, q) ->
                                                     ((x.FStar_Syntax_Syntax.ppname),
                                                       (x.FStar_Syntax_Syntax.sort)))) in
                                       let fields = fields' in
                                       let record =
                                         let uu____8472 =
                                           FStar_Ident.ident_of_lid
                                             constrname in
                                         {
                                           typename;
                                           constrname = uu____8472;
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
                                       ((let uu____8474 =
                                           let uu____8477 =
                                             FStar_ST.op_Bang new_globs in
                                           (Record_or_dc record) ::
                                             uu____8477 in
                                         FStar_ST.op_Colon_Equals new_globs
                                           uu____8474);
                                        (match () with
                                         | () ->
                                             ((let add_field uu____8536 =
                                                 match uu____8536 with
                                                 | (id, uu____8542) ->
                                                     let modul =
                                                       let uu____8545 =
                                                         let uu____8546 =
                                                           FStar_Ident.ns_of_lid
                                                             constrname in
                                                         FStar_Ident.lid_of_ids
                                                           uu____8546 in
                                                       FStar_Ident.string_of_lid
                                                         uu____8545 in
                                                     let uu____8547 =
                                                       get_exported_id_set e
                                                         modul in
                                                     (match uu____8547 with
                                                      | FStar_Pervasives_Native.Some
                                                          my_ex ->
                                                          let my_exported_ids
                                                            =
                                                            my_ex
                                                              Exported_id_field in
                                                          ((let uu____8570 =
                                                              let uu____8571
                                                                =
                                                                FStar_Ident.string_of_id
                                                                  id in
                                                              let uu____8573
                                                                =
                                                                FStar_ST.op_Bang
                                                                  my_exported_ids in
                                                              FStar_Util.set_add
                                                                uu____8571
                                                                uu____8573 in
                                                            FStar_ST.op_Colon_Equals
                                                              my_exported_ids
                                                              uu____8570);
                                                           (match () with
                                                            | () ->
                                                                let projname
                                                                  =
                                                                  let uu____8618
                                                                    =
                                                                    let uu____8619
                                                                    =
                                                                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                    constrname
                                                                    id in
                                                                    FStar_All.pipe_right
                                                                    uu____8619
                                                                    FStar_Ident.ident_of_lid in
                                                                  FStar_All.pipe_right
                                                                    uu____8618
                                                                    FStar_Ident.string_of_id in
                                                                let uu____8622
                                                                  =
                                                                  let uu____8623
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    my_exported_ids in
                                                                  FStar_Util.set_add
                                                                    projname
                                                                    uu____8623 in
                                                                FStar_ST.op_Colon_Equals
                                                                  my_exported_ids
                                                                  uu____8622))
                                                      | FStar_Pervasives_Native.None
                                                          -> ()) in
                                               FStar_List.iter add_field
                                                 fields');
                                              (match () with
                                               | () ->
                                                   insert_record_cache record))))))
                         | uu____8675 -> ())
                    | uu____8676 -> ()))
        | uu____8677 -> ()
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env1 ->
    fun fieldname ->
      let find_in_cache fieldname1 =
        let uu____8699 =
          let uu____8706 = FStar_Ident.ns_of_lid fieldname1 in
          let uu____8709 = FStar_Ident.ident_of_lid fieldname1 in
          (uu____8706, uu____8709) in
        match uu____8699 with
        | (ns, id) ->
            let uu____8720 = peek_record_cache () in
            FStar_Util.find_map uu____8720
              (fun record ->
                 let uu____8726 =
                   find_in_record ns id record (fun r -> Cont_ok r) in
                 option_of_cont
                   (fun uu____8732 -> FStar_Pervasives_Native.None)
                   uu____8726) in
      resolve_in_open_namespaces'' env1 fieldname Exported_id_field
        (fun uu____8734 -> Cont_ignore) (fun uu____8736 -> Cont_ignore)
        (fun r -> Cont_ok r)
        (fun fn ->
           let uu____8742 = find_in_cache fn in
           cont_of_option Cont_ignore uu____8742)
        (fun k -> fun uu____8748 -> k)
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env1 ->
    fun fieldname ->
      let uu____8764 = try_lookup_record_or_dc_by_field_name env1 fieldname in
      match uu____8764 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8770 -> FStar_Pervasives_Native.None
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env1 ->
    fun lid ->
      fun record ->
        let uu____8790 = try_lookup_record_by_field_name env1 lid in
        match uu____8790 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8795 = FStar_Ident.nsstr record.typename in
            let uu____8797 = FStar_Ident.nsstr record'.typename in
            uu____8795 = uu____8797 ->
            let uu____8800 =
              let uu____8803 = FStar_Ident.ns_of_lid record.typename in
              let uu____8806 = FStar_Ident.ident_of_lid lid in
              find_in_record uu____8803 uu____8806 record
                (fun uu____8808 -> Cont_ok ()) in
            (match uu____8800 with
             | Cont_ok uu____8810 -> true
             | uu____8812 -> false)
        | uu____8816 -> false
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun fieldname ->
      let uu____8838 = try_lookup_record_or_dc_by_field_name env1 fieldname in
      match uu____8838 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8849 =
            let uu____8855 =
              let uu____8856 =
                let uu____8857 =
                  let uu____8858 = FStar_Ident.ns_of_lid r.typename in
                  FStar_List.append uu____8858 [r.constrname] in
                FStar_Ident.lid_of_ids uu____8857 in
              let uu____8861 = FStar_Ident.range_of_lid fieldname in
              FStar_Ident.set_lid_range uu____8856 uu____8861 in
            (uu____8855, (r.is_record)) in
          FStar_Pervasives_Native.Some uu____8849
      | uu____8868 -> FStar_Pervasives_Native.None
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8886 ->
    let uu____8887 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu____8887
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8908 ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___28_8921 ->
      match uu___28_8921 with
      | Exported_id_term_type -> term_type_set
      | Exported_id_field -> field_set
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val ->
    fun exclude_interface ->
      fun env1 ->
        fun lid ->
          let filter_scope_mods uu___29_8959 =
            match uu___29_8959 with
            | Rec_binding uu____8961 -> true
            | uu____8963 -> false in
          let this_env =
            let uu___1100_8966 = env1 in
            let uu____8967 =
              FStar_List.filter filter_scope_mods env1.scope_mods in
            {
              curmodule = (uu___1100_8966.curmodule);
              curmonad = (uu___1100_8966.curmonad);
              modules = (uu___1100_8966.modules);
              scope_mods = uu____8967;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1100_8966.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1100_8966.sigaccum);
              sigmap = (uu___1100_8966.sigmap);
              iface = (uu___1100_8966.iface);
              admitted_iface = (uu___1100_8966.admitted_iface);
              expect_typ = (uu___1100_8966.expect_typ);
              remaining_iface_decls = (uu___1100_8966.remaining_iface_decls);
              syntax_only = (uu___1100_8966.syntax_only);
              ds_hooks = (uu___1100_8966.ds_hooks);
              dep_graph = (uu___1100_8966.dep_graph)
            } in
          let uu____8970 =
            try_lookup_lid' any_val exclude_interface this_env lid in
          match uu____8970 with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some uu____8987 -> false
let (push_scope_mod : env -> scope_mod -> env) =
  fun env1 ->
    fun scope_mod1 ->
      let uu___1108_9012 = env1 in
      {
        curmodule = (uu___1108_9012.curmodule);
        curmonad = (uu___1108_9012.curmonad);
        modules = (uu___1108_9012.modules);
        scope_mods = (scope_mod1 :: (env1.scope_mods));
        exported_ids = (uu___1108_9012.exported_ids);
        trans_exported_ids = (uu___1108_9012.trans_exported_ids);
        includes = (uu___1108_9012.includes);
        sigaccum = (uu___1108_9012.sigaccum);
        sigmap = (uu___1108_9012.sigmap);
        iface = (uu___1108_9012.iface);
        admitted_iface = (uu___1108_9012.admitted_iface);
        expect_typ = (uu___1108_9012.expect_typ);
        remaining_iface_decls = (uu___1108_9012.remaining_iface_decls);
        syntax_only = (uu___1108_9012.syntax_only);
        ds_hooks = (uu___1108_9012.ds_hooks);
        dep_graph = (uu___1108_9012.dep_graph)
      }
let (push_bv' :
  env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv * used_marker)) =
  fun env1 ->
    fun x ->
      let r = FStar_Ident.range_of_id x in
      let bv =
        let uu____9032 = FStar_Ident.string_of_id x in
        FStar_Syntax_Syntax.gen_bv uu____9032
          (FStar_Pervasives_Native.Some r)
          (let uu___1113_9035 = FStar_Syntax_Syntax.tun in
           {
             FStar_Syntax_Syntax.n = (uu___1113_9035.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r;
             FStar_Syntax_Syntax.vars =
               (uu___1113_9035.FStar_Syntax_Syntax.vars)
           }) in
      let used_marker1 = FStar_Util.mk_ref false in
      ((push_scope_mod env1 (Local_binding (x, bv, used_marker1))), bv,
        used_marker1)
let (push_bv : env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv)) =
  fun env1 ->
    fun x ->
      let uu____9057 = push_bv' env1 x in
      match uu____9057 with | (env2, bv, uu____9070) -> (env2, bv)
let (push_top_level_rec_binding :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.delta_depth -> (env * Prims.bool FStar_ST.ref))
  =
  fun env0 ->
    fun x ->
      fun dd ->
        let l = qualify env0 x in
        let uu____9102 =
          (unique false true env0 l) || (FStar_Options.interactive ()) in
        if uu____9102
        then
          let used_marker1 = FStar_Util.mk_ref false in
          ((push_scope_mod env0 (Rec_binding (x, l, dd, used_marker1))),
            used_marker1)
        else
          (let uu____9125 =
             let uu____9131 =
               let uu____9133 = FStar_Ident.string_of_lid l in
               Prims.op_Hat "Duplicate top-level names " uu____9133 in
             (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____9131) in
           let uu____9137 = FStar_Ident.range_of_lid l in
           FStar_Errors.raise_error uu____9125 uu____9137)
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup ->
    fun env1 ->
      fun s ->
        let err l =
          let sopt =
            let uu____9177 = FStar_Ident.string_of_lid l in
            FStar_Util.smap_try_find (sigmap env1) uu____9177 in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se, uu____9188) ->
                let uu____9196 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se) in
                (match uu____9196 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____9201 = FStar_Ident.range_of_lid l1 in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____9201
                 | FStar_Pervasives_Native.None -> "<unknown>")
            | FStar_Pervasives_Native.None -> "<unknown>" in
          let uu____9210 =
            let uu____9216 =
              let uu____9218 = FStar_Ident.string_of_lid l in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____9218 r in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____9216) in
          let uu____9222 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____9210 uu____9222 in
        let globals = FStar_Util.mk_ref env1.scope_mods in
        let env2 =
          let uu____9231 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____9244 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____9255 -> (false, true)
            | uu____9268 -> (false, false) in
          match uu____9231 with
          | (any_val, exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s in
              let uu____9282 =
                FStar_Util.find_map lids
                  (fun l ->
                     let uu____9288 =
                       let uu____9290 =
                         unique any_val exclude_interface env1 l in
                       Prims.op_Negation uu____9290 in
                     if uu____9288
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None) in
              (match uu____9282 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____9298 ->
                   (extract_record env1 globals s;
                    (let uu___1160_9302 = env1 in
                     {
                       curmodule = (uu___1160_9302.curmodule);
                       curmonad = (uu___1160_9302.curmonad);
                       modules = (uu___1160_9302.modules);
                       scope_mods = (uu___1160_9302.scope_mods);
                       exported_ids = (uu___1160_9302.exported_ids);
                       trans_exported_ids =
                         (uu___1160_9302.trans_exported_ids);
                       includes = (uu___1160_9302.includes);
                       sigaccum = (s :: (env1.sigaccum));
                       sigmap = (uu___1160_9302.sigmap);
                       iface = (uu___1160_9302.iface);
                       admitted_iface = (uu___1160_9302.admitted_iface);
                       expect_typ = (uu___1160_9302.expect_typ);
                       remaining_iface_decls =
                         (uu___1160_9302.remaining_iface_decls);
                       syntax_only = (uu___1160_9302.syntax_only);
                       ds_hooks = (uu___1160_9302.ds_hooks);
                       dep_graph = (uu___1160_9302.dep_graph)
                     }))) in
        let env3 =
          let uu___1163_9304 = env2 in
          let uu____9305 = FStar_ST.op_Bang globals in
          {
            curmodule = (uu___1163_9304.curmodule);
            curmonad = (uu___1163_9304.curmonad);
            modules = (uu___1163_9304.modules);
            scope_mods = uu____9305;
            exported_ids = (uu___1163_9304.exported_ids);
            trans_exported_ids = (uu___1163_9304.trans_exported_ids);
            includes = (uu___1163_9304.includes);
            sigaccum = (uu___1163_9304.sigaccum);
            sigmap = (uu___1163_9304.sigmap);
            iface = (uu___1163_9304.iface);
            admitted_iface = (uu___1163_9304.admitted_iface);
            expect_typ = (uu___1163_9304.expect_typ);
            remaining_iface_decls = (uu___1163_9304.remaining_iface_decls);
            syntax_only = (uu___1163_9304.syntax_only);
            ds_hooks = (uu___1163_9304.ds_hooks);
            dep_graph = (uu___1163_9304.dep_graph)
          } in
        let uu____9331 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses, uu____9357) ->
              let uu____9366 =
                FStar_List.map
                  (fun se -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
              (env3, uu____9366)
          | uu____9393 -> (env3, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
        match uu____9331 with
        | (env4, lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____9452 ->
                     match uu____9452 with
                     | (lids, se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid ->
                                 (let uu____9475 =
                                    let uu____9478 =
                                      let uu____9479 =
                                        FStar_Ident.ident_of_lid lid in
                                      Top_level_def uu____9479 in
                                    let uu____9480 = FStar_ST.op_Bang globals in
                                    uu____9478 :: uu____9480 in
                                  FStar_ST.op_Colon_Equals globals uu____9475);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____9531 =
                                          let uu____9532 =
                                            FStar_Ident.ns_of_lid lid in
                                          FStar_Ident.lid_of_ids uu____9532 in
                                        FStar_Ident.string_of_lid uu____9531 in
                                      ((let uu____9534 =
                                          get_exported_id_set env4 modul in
                                        match uu____9534 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type in
                                            let uu____9556 =
                                              let uu____9557 =
                                                let uu____9559 =
                                                  FStar_Ident.ident_of_lid
                                                    lid in
                                                FStar_Ident.string_of_id
                                                  uu____9559 in
                                              let uu____9560 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids in
                                              FStar_Util.set_add uu____9557
                                                uu____9560 in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____9556
                                        | FStar_Pervasives_Native.None -> ());
                                       (match () with
                                        | () ->
                                            let is_iface =
                                              env4.iface &&
                                                (Prims.op_Negation
                                                   env4.admitted_iface) in
                                            let uu____9610 =
                                              FStar_Ident.string_of_lid lid in
                                            FStar_Util.smap_add (sigmap env4)
                                              uu____9610
                                              (se,
                                                (env4.iface &&
                                                   (Prims.op_Negation
                                                      env4.admitted_iface))))))))));
             (let env5 =
                let uu___1188_9619 = env4 in
                let uu____9620 = FStar_ST.op_Bang globals in
                {
                  curmodule = (uu___1188_9619.curmodule);
                  curmonad = (uu___1188_9619.curmonad);
                  modules = (uu___1188_9619.modules);
                  scope_mods = uu____9620;
                  exported_ids = (uu___1188_9619.exported_ids);
                  trans_exported_ids = (uu___1188_9619.trans_exported_ids);
                  includes = (uu___1188_9619.includes);
                  sigaccum = (uu___1188_9619.sigaccum);
                  sigmap = (uu___1188_9619.sigmap);
                  iface = (uu___1188_9619.iface);
                  admitted_iface = (uu___1188_9619.admitted_iface);
                  expect_typ = (uu___1188_9619.expect_typ);
                  remaining_iface_decls =
                    (uu___1188_9619.remaining_iface_decls);
                  syntax_only = (uu___1188_9619.syntax_only);
                  ds_hooks = (uu___1188_9619.ds_hooks);
                  dep_graph = (uu___1188_9619.dep_graph)
                } in
              env5))
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1 -> fun se -> push_sigelt' true env1 se
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1 -> fun se -> push_sigelt' false env1 se
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun ns ->
      let uu____9681 =
        let uu____9686 = resolve_module_name env1 ns false in
        match uu____9686 with
        | FStar_Pervasives_Native.None ->
            let modules = env1.modules in
            let uu____9701 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9719 ->
                      match uu____9719 with
                      | (m, uu____9726) ->
                          let uu____9727 =
                            let uu____9729 = FStar_Ident.string_of_lid m in
                            Prims.op_Hat uu____9729 "." in
                          let uu____9732 =
                            let uu____9734 = FStar_Ident.string_of_lid ns in
                            Prims.op_Hat uu____9734 "." in
                          FStar_Util.starts_with uu____9727 uu____9732)) in
            if uu____9701
            then (ns, Open_namespace)
            else
              (let uu____9744 =
                 let uu____9750 =
                   let uu____9752 = FStar_Ident.string_of_lid ns in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9752 in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9750) in
               let uu____9756 = FStar_Ident.range_of_lid ns in
               FStar_Errors.raise_error uu____9744 uu____9756)
        | FStar_Pervasives_Native.Some ns' -> (ns', Open_module) in
      match uu____9681 with
      | (ns', kd) ->
          ((env1.ds_hooks).ds_push_open_hook env1 (ns', kd);
           push_scope_mod env1 (Open_module_or_namespace (ns', kd)))
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun ns ->
      let ns0 = ns in
      let uu____9777 = resolve_module_name env1 ns false in
      match uu____9777 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env1.ds_hooks).ds_push_include_hook env1 ns1;
           (let env2 =
              push_scope_mod env1
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____9786 = current_module env2 in
              FStar_Ident.string_of_lid uu____9786 in
            (let uu____9788 = FStar_Util.smap_try_find env2.includes curmod in
             match uu____9788 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9812 =
                   let uu____9815 = FStar_ST.op_Bang incl in ns1 ::
                     uu____9815 in
                 FStar_ST.op_Colon_Equals incl uu____9812);
            (match () with
             | () ->
                 let uu____9864 =
                   let uu____9872 = FStar_Ident.string_of_lid ns1 in
                   get_trans_exported_id_set env2 uu____9872 in
                 (match uu____9864 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9886 =
                          let uu____9983 = get_exported_id_set env2 curmod in
                          let uu____10030 =
                            get_trans_exported_id_set env2 curmod in
                          (uu____9983, uu____10030) in
                        match uu____9886 with
                        | (FStar_Pervasives_Native.Some cur_exports,
                           FStar_Pervasives_Native.Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10446 = ns_trans_exports k in
                                FStar_ST.op_Bang uu____10446 in
                              let ex = cur_exports k in
                              (let uu____10547 =
                                 let uu____10551 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu____10551 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu____10547);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____10643 =
                                     let uu____10647 =
                                       FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu____10647 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10643) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10696 -> ());
                       (match () with | () -> env2))
                  | FStar_Pervasives_Native.None ->
                      let uu____10798 =
                        let uu____10804 =
                          let uu____10806 = FStar_Ident.string_of_lid ns1 in
                          FStar_Util.format1
                            "include: Module %s was not prepared" uu____10806 in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10804) in
                      let uu____10810 = FStar_Ident.range_of_lid ns1 in
                      FStar_Errors.raise_error uu____10798 uu____10810))))
      | uu____10811 ->
          let uu____10814 =
            let uu____10820 =
              let uu____10822 = FStar_Ident.string_of_lid ns in
              FStar_Util.format1 "include: Module %s cannot be found"
                uu____10822 in
            (FStar_Errors.Fatal_ModuleNotFound, uu____10820) in
          let uu____10826 = FStar_Ident.range_of_lid ns in
          FStar_Errors.raise_error uu____10814 uu____10826
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun x ->
      fun l ->
        let uu____10843 = module_is_defined env1 l in
        if uu____10843
        then
          ((env1.ds_hooks).ds_push_module_abbrev_hook env1 x l;
           push_scope_mod env1 (Module_abbrev (x, l)))
        else
          (let uu____10849 =
             let uu____10855 =
               let uu____10857 = FStar_Ident.string_of_lid l in
               FStar_Util.format1 "Module %s cannot be found" uu____10857 in
             (FStar_Errors.Fatal_ModuleNotFound, uu____10855) in
           let uu____10861 = FStar_Ident.range_of_lid l in
           FStar_Errors.raise_error uu____10849 uu____10861)
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
                      let uu____10904 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
                      Prims.op_Negation uu____10904 ->
                      let uu____10909 =
                        let uu____10917 = FStar_Ident.string_of_lid l in
                        FStar_Util.smap_try_find (sigmap env1) uu____10917 in
                      (match uu____10909 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____10926;
                              FStar_Syntax_Syntax.sigrng = uu____10927;
                              FStar_Syntax_Syntax.sigquals = uu____10928;
                              FStar_Syntax_Syntax.sigmeta = uu____10929;
                              FStar_Syntax_Syntax.sigattrs = uu____10930;
                              FStar_Syntax_Syntax.sigopts = uu____10931;_},
                            uu____10932)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____10952;
                              FStar_Syntax_Syntax.sigrng = uu____10953;
                              FStar_Syntax_Syntax.sigquals = uu____10954;
                              FStar_Syntax_Syntax.sigmeta = uu____10955;
                              FStar_Syntax_Syntax.sigattrs = uu____10956;
                              FStar_Syntax_Syntax.sigopts = uu____10957;_},
                            uu____10958)
                           -> lids
                       | uu____10988 ->
                           ((let uu____10997 =
                               let uu____10999 = FStar_Options.interactive () in
                               Prims.op_Negation uu____10999 in
                             if uu____10997
                             then
                               let uu____11002 = FStar_Ident.range_of_lid l in
                               let uu____11003 =
                                 let uu____11009 =
                                   let uu____11011 =
                                     FStar_Ident.string_of_lid l in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____11011 in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____11009) in
                               FStar_Errors.log_issue uu____11002 uu____11003
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals) in
                             (let uu____11021 = FStar_Ident.string_of_lid l in
                              FStar_Util.smap_add (sigmap env1) uu____11021
                                ((let uu___1279_11030 = se in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (uu___1279_11030.FStar_Syntax_Syntax.sigel);
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___1279_11030.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals = quals;
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___1279_11030.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___1279_11030.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___1279_11030.FStar_Syntax_Syntax.sigopts)
                                  }), false));
                             l
                             ::
                             lids)))
                  | uu____11032 -> lids) []) in
      let uu___1284_11033 = m in
      let uu____11034 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid, uu____11044, uu____11045) when
                    FStar_List.existsb
                      (fun l -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1293_11048 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1293_11048.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1293_11048.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1293_11048.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1293_11048.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1293_11048.FStar_Syntax_Syntax.sigopts)
                    }
                | uu____11049 -> s)) in
      {
        FStar_Syntax_Syntax.name = (uu___1284_11033.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11034;
        FStar_Syntax_Syntax.exports =
          (uu___1284_11033.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1284_11033.FStar_Syntax_Syntax.is_interface)
      }
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env1 ->
    fun modul ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses, uu____11073) ->
                  if
                    (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                      ||
                      (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun se1 ->
                            match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid, uu____11095, uu____11096, uu____11097,
                                 uu____11098, uu____11099)
                                ->
                                let uu____11106 =
                                  FStar_Ident.string_of_lid lid in
                                FStar_Util.smap_remove (sigmap env1)
                                  uu____11106
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid, univ_names, binders, typ, uu____11117,
                                 uu____11118)
                                ->
                                ((let uu____11128 =
                                    FStar_Ident.string_of_lid lid in
                                  FStar_Util.smap_remove (sigmap env1)
                                    uu____11128);
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11137 =
                                        let uu____11144 =
                                          let uu____11145 =
                                            let uu____11146 =
                                              let uu____11161 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  typ in
                                              (binders, uu____11161) in
                                            FStar_Syntax_Syntax.Tm_arrow
                                              uu____11146 in
                                          let uu____11174 =
                                            FStar_Ident.range_of_lid lid in
                                          FStar_Syntax_Syntax.mk uu____11145
                                            uu____11174 in
                                        (lid, univ_names, uu____11144) in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11137 in
                                    let se2 =
                                      let uu___1325_11176 = se1 in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1325_11176.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1325_11176.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1325_11176.FStar_Syntax_Syntax.sigattrs);
                                        FStar_Syntax_Syntax.sigopts =
                                          (uu___1325_11176.FStar_Syntax_Syntax.sigopts)
                                      } in
                                    let uu____11177 =
                                      FStar_Ident.string_of_lid lid in
                                    FStar_Util.smap_add (sigmap env1)
                                      uu____11177 (se2, false))
                                 else ())
                            | uu____11188 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid, uu____11192, uu____11193) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    let uu____11195 = FStar_Ident.string_of_lid lid in
                    FStar_Util.smap_remove (sigmap env1) uu____11195
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11204, lbs), uu____11206)
                  ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb ->
                             let uu____11224 =
                               let uu____11226 =
                                 let uu____11227 =
                                   let uu____11230 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____11230.FStar_Syntax_Syntax.fv_name in
                                 uu____11227.FStar_Syntax_Syntax.v in
                               FStar_Ident.string_of_lid uu____11226 in
                             FStar_Util.smap_remove (sigmap env1) uu____11224))
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
                          (fun lb ->
                             let lid =
                               let uu____11248 =
                                 let uu____11251 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____11251.FStar_Syntax_Syntax.fv_name in
                               uu____11248.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___1348_11256 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1348_11256.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1348_11256.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1348_11256.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___1348_11256.FStar_Syntax_Syntax.sigopts)
                               } in
                             let uu____11257 = FStar_Ident.string_of_lid lid in
                             FStar_Util.smap_add (sigmap env1) uu____11257
                               (decl, false)))
                   else ())
              | uu____11268 -> ()));
      (let curmod =
         let uu____11271 = current_module env1 in
         FStar_Ident.string_of_lid uu____11271 in
       (let uu____11273 =
          let uu____11370 = get_exported_id_set env1 curmod in
          let uu____11417 = get_trans_exported_id_set env1 curmod in
          (uu____11370, uu____11417) in
        match uu____11273 with
        | (FStar_Pervasives_Native.Some cur_ex, FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____11836 = cur_ex eikind in
                FStar_ST.op_Bang uu____11836 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____11942 =
                let uu____11946 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____11946 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____11942 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____11995 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1366_12093 = env1 in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1366_12093.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env1.modules));
                    scope_mods = [];
                    exported_ids = (uu___1366_12093.exported_ids);
                    trans_exported_ids = (uu___1366_12093.trans_exported_ids);
                    includes = (uu___1366_12093.includes);
                    sigaccum = [];
                    sigmap = (uu___1366_12093.sigmap);
                    iface = (uu___1366_12093.iface);
                    admitted_iface = (uu___1366_12093.admitted_iface);
                    expect_typ = (uu___1366_12093.expect_typ);
                    remaining_iface_decls =
                      (uu___1366_12093.remaining_iface_decls);
                    syntax_only = (uu___1366_12093.syntax_only);
                    ds_hooks = (uu___1366_12093.ds_hooks);
                    dep_graph = (uu___1366_12093.dep_graph)
                  }))))
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push : env -> env) =
  fun env1 ->
    FStar_Util.atomically
      (fun uu____12119 ->
         push_record_cache ();
         (let uu____12122 =
            let uu____12125 = FStar_ST.op_Bang stack in env1 :: uu____12125 in
          FStar_ST.op_Colon_Equals stack uu____12122);
         (let uu___1372_12174 = env1 in
          let uu____12175 = FStar_Util.smap_copy env1.exported_ids in
          let uu____12180 = FStar_Util.smap_copy env1.trans_exported_ids in
          let uu____12185 = FStar_Util.smap_copy env1.includes in
          let uu____12196 = FStar_Util.smap_copy env1.sigmap in
          {
            curmodule = (uu___1372_12174.curmodule);
            curmonad = (uu___1372_12174.curmonad);
            modules = (uu___1372_12174.modules);
            scope_mods = (uu___1372_12174.scope_mods);
            exported_ids = uu____12175;
            trans_exported_ids = uu____12180;
            includes = uu____12185;
            sigaccum = (uu___1372_12174.sigaccum);
            sigmap = uu____12196;
            iface = (uu___1372_12174.iface);
            admitted_iface = (uu___1372_12174.admitted_iface);
            expect_typ = (uu___1372_12174.expect_typ);
            remaining_iface_decls = (uu___1372_12174.remaining_iface_decls);
            syntax_only = (uu___1372_12174.syntax_only);
            ds_hooks = (uu___1372_12174.ds_hooks);
            dep_graph = (uu___1372_12174.dep_graph)
          }))
let (pop : unit -> env) =
  fun uu____12214 ->
    FStar_Util.atomically
      (fun uu____12221 ->
         let uu____12222 = FStar_ST.op_Bang stack in
         match uu____12222 with
         | env1::tl ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl; env1)
         | uu____12277 -> failwith "Impossible: Too many pops")
let (snapshot : env -> (Prims.int * env)) =
  fun env1 -> FStar_Common.snapshot push stack env1
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth -> FStar_Common.rollback pop stack depth
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m ->
    fun env1 ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12324 ->
            let uu____12327 = FStar_Ident.nsstr l in
            let uu____12329 = FStar_Ident.string_of_lid m in
            uu____12327 = uu____12329
        | uu____12332 -> false in
      let sm = sigmap env1 in
      let env2 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env2 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k ->
              let uu____12374 = FStar_Util.smap_try_find sm' k in
              match uu____12374 with
              | FStar_Pervasives_Native.Some (se, true) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) ->
                          let uu___1407_12405 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1407_12405.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1407_12405.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1407_12405.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1407_12405.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___1407_12405.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____12406 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12414 -> ()));
      env2
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env1 ->
    fun modul ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env1 modul
        else modul in
      let uu____12441 = finish env1 modul1 in (uu____12441, modul1)
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
      let uu____12510 =
        let uu____12514 = e Exported_id_term_type in
        FStar_ST.op_Bang uu____12514 in
      FStar_Util.set_elements uu____12510 in
    let fields =
      let uu____12577 =
        let uu____12581 = e Exported_id_field in FStar_ST.op_Bang uu____12581 in
      FStar_Util.set_elements uu____12577 in
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
          let uu____12673 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu____12673 in
        let fields =
          let uu____12687 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu____12687 in
        (fun uu___30_12695 ->
           match uu___30_12695 with
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
  'uuuuuu12799 .
    'uuuuuu12799 Prims.list FStar_Pervasives_Native.option ->
      'uuuuuu12799 Prims.list FStar_ST.ref
  =
  fun uu___31_12812 ->
    match uu___31_12812 with
    | FStar_Pervasives_Native.None -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env1 ->
    fun l ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu____12855 = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu____12855 as_exported_ids in
      let uu____12861 = as_ids_opt env1.exported_ids in
      let uu____12864 = as_ids_opt env1.trans_exported_ids in
      let uu____12867 =
        let uu____12872 = FStar_Util.smap_try_find env1.includes mname in
        FStar_Util.map_opt uu____12872 (fun r -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu____12861;
        mii_trans_exported_ids = uu____12864;
        mii_includes = uu____12867
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
                let uu____12961 = FStar_Ident.string_of_lid mname in
                FStar_Util.strcat uu____12961 ".fst" in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename in
              let auto_open1 =
                let convert_kind uu___32_12983 =
                  match uu___32_12983 with
                  | FStar_Parser_Dep.Open_namespace -> Open_namespace
                  | FStar_Parser_Dep.Open_module -> Open_module in
                FStar_List.map
                  (fun uu____12995 ->
                     match uu____12995 with
                     | (lid, kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                let uu____13013 =
                  let uu____13015 =
                    let uu____13017 = FStar_Ident.ns_of_lid mname in
                    FStar_List.length uu____13017 in
                  uu____13015 > Prims.int_zero in
                if uu____13013
                then
                  let uu____13028 =
                    let uu____13033 =
                      let uu____13034 = FStar_Ident.ns_of_lid mname in
                      FStar_Ident.lid_of_ids uu____13034 in
                    (uu____13033, Open_namespace) in
                  [uu____13028]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu____13065 = FStar_Ident.string_of_lid mname in
               let uu____13067 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env2.exported_ids uu____13065 uu____13067);
              (match () with
               | () ->
                   ((let uu____13072 = FStar_Ident.string_of_lid mname in
                     let uu____13074 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env2.trans_exported_ids uu____13072
                       uu____13074);
                    (match () with
                     | () ->
                         ((let uu____13079 = FStar_Ident.string_of_lid mname in
                           let uu____13081 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env2.includes uu____13079
                             uu____13081);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1477_13091 = env2 in
                                 let uu____13092 =
                                   FStar_List.map
                                     (fun x -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1477_13091.curmonad);
                                   modules = (uu___1477_13091.modules);
                                   scope_mods = uu____13092;
                                   exported_ids =
                                     (uu___1477_13091.exported_ids);
                                   trans_exported_ids =
                                     (uu___1477_13091.trans_exported_ids);
                                   includes = (uu___1477_13091.includes);
                                   sigaccum = (uu___1477_13091.sigaccum);
                                   sigmap = (env2.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1477_13091.expect_typ);
                                   remaining_iface_decls =
                                     (uu___1477_13091.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1477_13091.syntax_only);
                                   ds_hooks = (uu___1477_13091.ds_hooks);
                                   dep_graph = (uu___1477_13091.dep_graph)
                                 } in
                               (FStar_List.iter
                                  (fun op ->
                                     (env2.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu____13104 =
              FStar_All.pipe_right env1.modules
                (FStar_Util.find_opt
                   (fun uu____13130 ->
                      match uu____13130 with
                      | (l, uu____13137) -> FStar_Ident.lid_equals l mname)) in
            match uu____13104 with
            | FStar_Pervasives_Native.None ->
                let uu____13147 = prep env1 in (uu____13147, false)
            | FStar_Pervasives_Native.Some (uu____13150, m) ->
                ((let uu____13157 =
                    (let uu____13161 = FStar_Options.interactive () in
                     Prims.op_Negation uu____13161) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu____13157
                  then
                    let uu____13164 =
                      let uu____13170 =
                        let uu____13172 = FStar_Ident.string_of_lid mname in
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          uu____13172 in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13170) in
                    let uu____13176 = FStar_Ident.range_of_lid mname in
                    FStar_Errors.raise_error uu____13164 uu____13176
                  else ());
                 (let uu____13179 =
                    let uu____13180 = push env1 in prep uu____13180 in
                  (uu____13179, true)))
let (enter_monad_scope : env -> FStar_Ident.ident -> env) =
  fun env1 ->
    fun mname ->
      match env1.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          let uu____13195 =
            let uu____13201 =
              let uu____13203 =
                let uu____13205 = FStar_Ident.string_of_id mname in
                let uu____13207 =
                  let uu____13209 = FStar_Ident.string_of_id mname' in
                  Prims.op_Hat ", but already in monad scope " uu____13209 in
                Prims.op_Hat uu____13205 uu____13207 in
              Prims.op_Hat "Trying to define monad " uu____13203 in
            (FStar_Errors.Fatal_MonadAlreadyDefined, uu____13201) in
          let uu____13214 = FStar_Ident.range_of_id mname in
          FStar_Errors.raise_error uu____13195 uu____13214
      | FStar_Pervasives_Native.None ->
          let uu___1498_13215 = env1 in
          {
            curmodule = (uu___1498_13215.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1498_13215.modules);
            scope_mods = (uu___1498_13215.scope_mods);
            exported_ids = (uu___1498_13215.exported_ids);
            trans_exported_ids = (uu___1498_13215.trans_exported_ids);
            includes = (uu___1498_13215.includes);
            sigaccum = (uu___1498_13215.sigaccum);
            sigmap = (uu___1498_13215.sigmap);
            iface = (uu___1498_13215.iface);
            admitted_iface = (uu___1498_13215.admitted_iface);
            expect_typ = (uu___1498_13215.expect_typ);
            remaining_iface_decls = (uu___1498_13215.remaining_iface_decls);
            syntax_only = (uu___1498_13215.syntax_only);
            ds_hooks = (uu___1498_13215.ds_hooks);
            dep_graph = (uu___1498_13215.dep_graph)
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
        let uu____13250 = lookup lid in
        match uu____13250 with
        | FStar_Pervasives_Native.None ->
            let opened_modules =
              FStar_List.map
                (fun uu____13265 ->
                   match uu____13265 with
                   | (lid1, uu____13272) -> FStar_Ident.string_of_lid lid1)
                env1.modules in
            let msg =
              let uu____13275 = FStar_Ident.string_of_lid lid in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13275 in
            let msg1 =
              let uu____13280 =
                let uu____13282 =
                  let uu____13284 = FStar_Ident.ns_of_lid lid in
                  FStar_List.length uu____13284 in
                uu____13282 = Prims.int_zero in
              if uu____13280
              then msg
              else
                (let modul =
                   let uu____13294 =
                     let uu____13295 = FStar_Ident.ns_of_lid lid in
                     FStar_Ident.lid_of_ids uu____13295 in
                   let uu____13296 = FStar_Ident.range_of_lid lid in
                   FStar_Ident.set_lid_range uu____13294 uu____13296 in
                 let uu____13297 = resolve_module_name env1 modul true in
                 match uu____13297 with
                 | FStar_Pervasives_Native.None ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     let uu____13305 = FStar_Ident.string_of_lid modul in
                     FStar_Util.format3
                       "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                       msg uu____13305 opened_modules1
                 | FStar_Pervasives_Native.Some modul' when
                     Prims.op_Negation
                       (FStar_List.existsb
                          (fun m ->
                             let uu____13314 =
                               FStar_Ident.string_of_lid modul' in
                             m = uu____13314) opened_modules)
                     ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     let uu____13320 = FStar_Ident.string_of_lid modul in
                     let uu____13322 = FStar_Ident.string_of_lid modul' in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                       msg uu____13320 uu____13322 opened_modules1
                 | FStar_Pervasives_Native.Some modul' ->
                     let uu____13326 = FStar_Ident.string_of_lid modul in
                     let uu____13328 = FStar_Ident.string_of_lid modul' in
                     let uu____13330 =
                       let uu____13332 = FStar_Ident.ident_of_lid lid in
                       FStar_Ident.string_of_id uu____13332 in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, definition %s not found"
                       msg uu____13326 uu____13328 uu____13330) in
            let uu____13334 = FStar_Ident.range_of_lid lid in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13334
        | FStar_Pervasives_Native.Some r -> r
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup ->
    fun id ->
      let uu____13364 = lookup id in
      match uu____13364 with
      | FStar_Pervasives_Native.None ->
          let uu____13367 =
            let uu____13373 =
              let uu____13375 =
                let uu____13377 = FStar_Ident.string_of_id id in
                Prims.op_Hat uu____13377 "]" in
              Prims.op_Hat "Identifier not found [" uu____13375 in
            (FStar_Errors.Fatal_IdentifierNotFound, uu____13373) in
          let uu____13382 = FStar_Ident.range_of_id id in
          FStar_Errors.raise_error uu____13367 uu____13382
      | FStar_Pervasives_Native.Some r -> r