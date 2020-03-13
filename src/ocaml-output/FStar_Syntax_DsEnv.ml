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
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____59 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____70 -> false
  
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
  fun projectee  ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> typename
  
let (__proj__Mkrecord_or_dc__item__constrname :
  record_or_dc -> FStar_Ident.ident) =
  fun projectee  ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> constrname
  
let (__proj__Mkrecord_or_dc__item__parms :
  record_or_dc -> FStar_Syntax_Syntax.binders) =
  fun projectee  ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> parms
  
let (__proj__Mkrecord_or_dc__item__fields :
  record_or_dc -> (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list) =
  fun projectee  ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> fields
  
let (__proj__Mkrecord_or_dc__item__is_private_or_abstract :
  record_or_dc -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> is_private_or_abstract
  
let (__proj__Mkrecord_or_dc__item__is_record : record_or_dc -> Prims.bool) =
  fun projectee  ->
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
  fun projectee  ->
    match projectee with | Local_binding _0 -> true | uu____310 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____329 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____348 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____367 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____386 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____405 -> false
  
let (__proj__Record_or_dc__item___0 : scope_mod -> record_or_dc) =
  fun projectee  -> match projectee with | Record_or_dc _0 -> _0 
type string_set = Prims.string FStar_Util.set
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field 
let (uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____426 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____437 -> false
  
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
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmodule
  
let (__proj__Mkenv__item__curmonad :
  env -> FStar_Ident.ident FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmonad
  
let (__proj__Mkenv__item__modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> modules
  
let (__proj__Mkenv__item__scope_mods : env -> scope_mod Prims.list) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> scope_mods
  
let (__proj__Mkenv__item__exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> exported_ids
  
let (__proj__Mkenv__item__trans_exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> trans_exported_ids
  
let (__proj__Mkenv__item__includes :
  env -> FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> includes
  
let (__proj__Mkenv__item__sigaccum : env -> FStar_Syntax_Syntax.sigelts) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> sigaccum
  
let (__proj__Mkenv__item__sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> sigmap
  
let (__proj__Mkenv__item__iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> iface
  
let (__proj__Mkenv__item__admitted_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> admitted_iface
  
let (__proj__Mkenv__item__expect_typ : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> expect_typ
  
let (__proj__Mkenv__item__remaining_iface_decls :
  env -> (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> remaining_iface_decls
  
let (__proj__Mkenv__item__syntax_only : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> syntax_only
  
let (__proj__Mkenv__item__ds_hooks : env -> dsenv_hooks) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> ds_hooks
  
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> dep_graph
  
let (__proj__Mkdsenv_hooks__item__ds_push_open_hook :
  dsenv_hooks -> env -> open_module_or_namespace -> unit) =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_open_hook
  
let (__proj__Mkdsenv_hooks__item__ds_push_include_hook :
  dsenv_hooks -> env -> FStar_Ident.lident -> unit) =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_include_hook
  
let (__proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook :
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> unit) =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_module_abbrev_hook
  
type 'a withenv = env -> ('a * env)
let (default_ds_hooks : dsenv_hooks) =
  {
    ds_push_open_hook = (fun uu____1930  -> fun uu____1931  -> ());
    ds_push_include_hook = (fun uu____1934  -> fun uu____1935  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____1939  -> fun uu____1940  -> fun uu____1941  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____1978 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____2019 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___126_2053 = env  in
      {
        curmodule = (uu___126_2053.curmodule);
        curmonad = (uu___126_2053.curmonad);
        modules = (uu___126_2053.modules);
        scope_mods = (uu___126_2053.scope_mods);
        exported_ids = (uu___126_2053.exported_ids);
        trans_exported_ids = (uu___126_2053.trans_exported_ids);
        includes = (uu___126_2053.includes);
        sigaccum = (uu___126_2053.sigaccum);
        sigmap = (uu___126_2053.sigmap);
        iface = b;
        admitted_iface = (uu___126_2053.admitted_iface);
        expect_typ = (uu___126_2053.expect_typ);
        remaining_iface_decls = (uu___126_2053.remaining_iface_decls);
        syntax_only = (uu___126_2053.syntax_only);
        ds_hooks = (uu___126_2053.ds_hooks);
        dep_graph = (uu___126_2053.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___131_2074 = e  in
      {
        curmodule = (uu___131_2074.curmodule);
        curmonad = (uu___131_2074.curmonad);
        modules = (uu___131_2074.modules);
        scope_mods = (uu___131_2074.scope_mods);
        exported_ids = (uu___131_2074.exported_ids);
        trans_exported_ids = (uu___131_2074.trans_exported_ids);
        includes = (uu___131_2074.includes);
        sigaccum = (uu___131_2074.sigaccum);
        sigmap = (uu___131_2074.sigmap);
        iface = (uu___131_2074.iface);
        admitted_iface = b;
        expect_typ = (uu___131_2074.expect_typ);
        remaining_iface_decls = (uu___131_2074.remaining_iface_decls);
        syntax_only = (uu___131_2074.syntax_only);
        ds_hooks = (uu___131_2074.ds_hooks);
        dep_graph = (uu___131_2074.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___136_2095 = e  in
      {
        curmodule = (uu___136_2095.curmodule);
        curmonad = (uu___136_2095.curmonad);
        modules = (uu___136_2095.modules);
        scope_mods = (uu___136_2095.scope_mods);
        exported_ids = (uu___136_2095.exported_ids);
        trans_exported_ids = (uu___136_2095.trans_exported_ids);
        includes = (uu___136_2095.includes);
        sigaccum = (uu___136_2095.sigaccum);
        sigmap = (uu___136_2095.sigmap);
        iface = (uu___136_2095.iface);
        admitted_iface = (uu___136_2095.admitted_iface);
        expect_typ = b;
        remaining_iface_decls = (uu___136_2095.remaining_iface_decls);
        syntax_only = (uu___136_2095.syntax_only);
        ds_hooks = (uu___136_2095.ds_hooks);
        dep_graph = (uu___136_2095.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____2122 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____2122 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____2135 =
            let uu____2139 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____2139  in
          FStar_All.pipe_right uu____2135 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___0_2227  ->
         match uu___0_2227 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2232 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___155_2244 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___155_2244.curmonad);
        modules = (uu___155_2244.modules);
        scope_mods = (uu___155_2244.scope_mods);
        exported_ids = (uu___155_2244.exported_ids);
        trans_exported_ids = (uu___155_2244.trans_exported_ids);
        includes = (uu___155_2244.includes);
        sigaccum = (uu___155_2244.sigaccum);
        sigmap = (uu___155_2244.sigmap);
        iface = (uu___155_2244.iface);
        admitted_iface = (uu___155_2244.admitted_iface);
        expect_typ = (uu___155_2244.expect_typ);
        remaining_iface_decls = (uu___155_2244.remaining_iface_decls);
        syntax_only = (uu___155_2244.syntax_only);
        ds_hooks = (uu___155_2244.ds_hooks);
        dep_graph = (uu___155_2244.dep_graph)
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
      let uu____2268 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2302  ->
                match uu____2302 with
                | (m,uu____2311) -> FStar_Ident.lid_equals l m))
         in
      match uu____2268 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2328,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2362 =
          FStar_List.partition
            (fun uu____2392  ->
               match uu____2392 with
               | (m,uu____2401) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____2362 with
        | (uu____2406,rest) ->
            let uu___180_2440 = env  in
            {
              curmodule = (uu___180_2440.curmodule);
              curmonad = (uu___180_2440.curmonad);
              modules = (uu___180_2440.modules);
              scope_mods = (uu___180_2440.scope_mods);
              exported_ids = (uu___180_2440.exported_ids);
              trans_exported_ids = (uu___180_2440.trans_exported_ids);
              includes = (uu___180_2440.includes);
              sigaccum = (uu___180_2440.sigaccum);
              sigmap = (uu___180_2440.sigmap);
              iface = (uu___180_2440.iface);
              admitted_iface = (uu___180_2440.admitted_iface);
              expect_typ = (uu___180_2440.expect_typ);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___180_2440.syntax_only);
              ds_hooks = (uu___180_2440.ds_hooks);
              dep_graph = (uu___180_2440.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2469 = current_module env  in qual uu____2469 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2471 =
            let uu____2472 = current_module env  in qual uu____2472 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2471 id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___190_2493 = env  in
      {
        curmodule = (uu___190_2493.curmodule);
        curmonad = (uu___190_2493.curmonad);
        modules = (uu___190_2493.modules);
        scope_mods = (uu___190_2493.scope_mods);
        exported_ids = (uu___190_2493.exported_ids);
        trans_exported_ids = (uu___190_2493.trans_exported_ids);
        includes = (uu___190_2493.includes);
        sigaccum = (uu___190_2493.sigaccum);
        sigmap = (uu___190_2493.sigmap);
        iface = (uu___190_2493.iface);
        admitted_iface = (uu___190_2493.admitted_iface);
        expect_typ = (uu___190_2493.expect_typ);
        remaining_iface_decls = (uu___190_2493.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___190_2493.ds_hooks);
        dep_graph = (uu___190_2493.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___195_2511 = env  in
      {
        curmodule = (uu___195_2511.curmodule);
        curmonad = (uu___195_2511.curmonad);
        modules = (uu___195_2511.modules);
        scope_mods = (uu___195_2511.scope_mods);
        exported_ids = (uu___195_2511.exported_ids);
        trans_exported_ids = (uu___195_2511.trans_exported_ids);
        includes = (uu___195_2511.includes);
        sigaccum = (uu___195_2511.sigaccum);
        sigmap = (uu___195_2511.sigmap);
        iface = (uu___195_2511.iface);
        admitted_iface = (uu___195_2511.admitted_iface);
        expect_typ = (uu___195_2511.expect_typ);
        remaining_iface_decls = (uu___195_2511.remaining_iface_decls);
        syntax_only = (uu___195_2511.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___195_2511.dep_graph)
      }
  
let new_sigmap : 'Auu____2517 . unit -> 'Auu____2517 FStar_Util.smap =
  fun uu____2524  -> FStar_Util.smap_create (Prims.of_int (100)) 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____2532 = new_sigmap ()  in
    let uu____2537 = new_sigmap ()  in
    let uu____2542 = new_sigmap ()  in
    let uu____2553 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2532;
      trans_exported_ids = uu____2537;
      includes = uu____2542;
      sigaccum = [];
      sigmap = uu____2553;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___202_2597 = env  in
      {
        curmodule = (uu___202_2597.curmodule);
        curmonad = (uu___202_2597.curmonad);
        modules = (uu___202_2597.modules);
        scope_mods = (uu___202_2597.scope_mods);
        exported_ids = (uu___202_2597.exported_ids);
        trans_exported_ids = (uu___202_2597.trans_exported_ids);
        includes = (uu___202_2597.includes);
        sigaccum = (uu___202_2597.sigaccum);
        sigmap = (uu___202_2597.sigmap);
        iface = (uu___202_2597.iface);
        admitted_iface = (uu___202_2597.admitted_iface);
        expect_typ = (uu___202_2597.expect_typ);
        remaining_iface_decls = (uu___202_2597.remaining_iface_decls);
        syntax_only = (uu___202_2597.syntax_only);
        ds_hooks = (uu___202_2597.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____2625  ->
         match uu____2625 with
         | (m,uu____2632) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___211_2645 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___211_2645.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___214_2646 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___214_2646.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___214_2646.FStar_Syntax_Syntax.sort)
      }
  
let (bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r) 
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
  fun id1  ->
    FStar_Util.find_map unmangleMap
      (fun uu____2749  ->
         match uu____2749 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____2780 =
                 let uu____2781 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____2781 dd dq  in
               FStar_Pervasives_Native.Some uu____2780
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____2821 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2858 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____2879 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___1_2909  ->
      match uu___1_2909 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____2928 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____2928 cont_t) -> 'Auu____2928 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____2965 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____2965
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____2981  ->
                   match uu____2981 with
                   | (f,uu____2989) ->
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
  fun uu___2_3063  ->
    match uu___2_3063 with
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
              let rec aux uu___3_3139 =
                match uu___3_3139 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____3152 = get_exported_id_set env mname  in
                      match uu____3152 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____3179 = mex eikind  in
                            FStar_ST.op_Bang uu____3179  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____3241 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____3241 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3296 = qual modul id1  in
                        find_in_module uu____3296
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3301 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___4_3310  ->
    match uu___4_3310 with | Exported_id_field  -> true | uu____3313 -> false
  
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
                  let check_local_binding_id uu___5_3437 =
                    match uu___5_3437 with
                    | (id',uu____3440,uu____3441) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___6_3449 =
                    match uu___6_3449 with
                    | (id',uu____3452,uu____3453,uu____3454) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3459 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3459  in
                  let proc uu___7_3467 =
                    match uu___7_3467 with
                    | Local_binding l when check_local_binding_id l ->
                        let uu____3471 = l  in
                        (match uu____3471 with
                         | (uu____3474,uu____3475,used_marker) ->
                             (FStar_ST.op_Colon_Equals used_marker true;
                              k_local_binding l))
                    | Rec_binding r when check_rec_binding_id r ->
                        let uu____3501 = r  in
                        (match uu____3501 with
                         | (uu____3504,uu____3505,uu____3506,used_marker) ->
                             (FStar_ST.op_Colon_Equals used_marker true;
                              k_rec_binding r))
                    | Open_module_or_namespace (ns,Open_module ) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env ns id1
                    | Top_level_def id' when
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText ->
                        lookup_default_id Cont_ignore id1
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____3535 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3535 id1
                    | uu____3540 -> Cont_ignore  in
                  let rec aux uu___8_3550 =
                    match uu___8_3550 with
                    | a::q ->
                        let uu____3559 = proc a  in
                        option_of_cont (fun uu____3563  -> aux q) uu____3559
                    | [] ->
                        let uu____3564 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____3568  -> FStar_Pervasives_Native.None)
                          uu____3564
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____3578 'Auu____3579 .
    FStar_Range.range ->
      ('Auu____3578 * FStar_Syntax_Syntax.bv * 'Auu____3579) ->
        FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____3595  ->
      match uu____3595 with | (id',x,uu____3604) -> bv_to_name x r
  
let find_in_module :
  'Auu____3616 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____3616)
          -> 'Auu____3616 -> 'Auu____3616
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3657 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____3657 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____3701 = unmangleOpName id1  in
      match uu____3701 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3707 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3713 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3713) (fun uu____3715  -> Cont_fail)
            (fun uu____3717  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3724  -> fun uu____3725  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3733  -> fun uu____3734  -> Cont_fail)
  
let lookup_default_id :
  'a .
    env ->
      FStar_Ident.ident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'a cont_t)
          -> 'a cont_t -> 'a cont_t
  =
  fun env  ->
    fun id1  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let find_in_monad =
            match env.curmonad with
            | FStar_Pervasives_Native.Some uu____3808 ->
                let lid = qualify env id1  in
                let uu____3810 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3810 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3838 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3838
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3862 = current_module env  in qual uu____3862 id1
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
        let rec aux uu___9_3934 =
          match uu___9_3934 with
          | [] ->
              let uu____3939 = module_is_defined env lid  in
              if uu____3939
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____3951 =
                  let uu____3952 = FStar_Ident.path_of_lid ns  in
                  let uu____3956 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____3952 uu____3956  in
                let uu____3961 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____3951 uu____3961  in
              let uu____3962 = module_is_defined env new_lid  in
              if uu____3962
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____3971 when
              (nslen = Prims.int_zero) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____3977::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____3997 =
          let uu____3999 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____3999  in
        if uu____3997
        then
          let uu____4001 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____4001
           then ()
           else
             (let uu____4006 =
                let uu____4012 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____4012)
                 in
              let uu____4016 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____4006 uu____4016))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____4030 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____4034 = resolve_module_name env modul_orig true  in
          (match uu____4034 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____4039 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___10_4062  ->
             match uu___10_4062 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____4066 -> false) env.scope_mods
  
let (namespace_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  -> fun lid  -> is_open env lid Open_namespace 
let (module_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  -> (lid_is_curmod env lid) || (is_open env lid Open_module)
  
let (shorten_module_path :
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
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
                 let uu____4195 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____4195
                   (FStar_Util.map_option
                      (fun uu____4245  ->
                         match uu____4245 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4315 = aux ns_rev_prefix ns_last_id  in
              (match uu____4315 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > Prims.int_zero)
        then
          let uu____4378 =
            let uu____4381 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____4381 true  in
          match uu____4378 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4396 -> do_shorten env ids
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
                  | uu____4517::uu____4518 ->
                      let uu____4521 =
                        let uu____4524 =
                          let uu____4525 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4526 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4525 uu____4526  in
                        resolve_module_name env uu____4524 true  in
                      (match uu____4521 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4531 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4535  -> FStar_Pervasives_Native.None)
                             uu____4531)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___11_4559  ->
      match uu___11_4559 with
      | FStar_Pervasives_Native.Some v1 -> Cont_ok v1
      | FStar_Pervasives_Native.None  -> k_none
  
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
  fun env  ->
    fun lid  ->
      fun k_local_binding  ->
        fun k_rec_binding  ->
          fun k_global_def  ->
            let k_global_def' k lid1 def =
              let uu____4680 = k_global_def lid1 def  in
              cont_of_option k uu____4680  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4716 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4716)
              (fun r  ->
                 let uu____4722 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4722)
              (fun uu____4726  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4737,uu____4738,uu____4739,l,uu____4741,uu____4742) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___12_4755  ->
               match uu___12_4755 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4758,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4770 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4776,uu____4777,uu____4778)
        -> FStar_Pervasives_Native.None
    | uu____4779 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4795 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4803 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4803
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4795 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4826 =
         let uu____4827 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4827  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4826) &&
        (let uu____4831 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4831 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____4848 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___13_4855  ->
                     match uu___13_4855 with
                     | FStar_Syntax_Syntax.Projector uu____4857 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____4863 -> true
                     | uu____4865 -> false)))
           in
        if uu____4848
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____4870 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___14_4876  ->
                 match uu___14_4876 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____4879 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___15_4885  ->
                    match uu___15_4885 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____4888 -> false)))
             &&
             (let uu____4891 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___16_4897  ->
                        match uu___16_4897 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____4900 -> false))
                 in
              Prims.op_Negation uu____4891))
         in
      if uu____4870 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___19_4952 =
            match uu___19_4952 with
            | (uu____4960,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4964) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4969 ->
                     let uu____4986 =
                       let uu____4987 =
                         let uu____4994 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4994, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____4987  in
                     FStar_Pervasives_Native.Some uu____4986
                 | FStar_Syntax_Syntax.Sig_datacon uu____4997 ->
                     let uu____5013 =
                       let uu____5014 =
                         let uu____5021 =
                           let uu____5022 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____5022
                            in
                         (uu____5021, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____5014  in
                     FStar_Pervasives_Native.Some uu____5013
                 | FStar_Syntax_Syntax.Sig_let ((uu____5027,lbs),uu____5029)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____5041 =
                       let uu____5042 =
                         let uu____5049 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____5049, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____5042  in
                     FStar_Pervasives_Native.Some uu____5041
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____5053,uu____5054) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____5058 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___17_5064  ->
                                  match uu___17_5064 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____5067 -> false)))
                        in
                     if uu____5058
                     then
                       let lid2 =
                         let uu____5073 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____5073  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____5075 =
                         FStar_Util.find_map quals
                           (fun uu___18_5080  ->
                              match uu___18_5080 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____5084 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____5075 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range
                               in
                            FStar_Pervasives_Native.Some
                              (Term_name
                                 (refl_const,
                                   (se.FStar_Syntax_Syntax.sigattrs)))
                        | uu____5093 ->
                            let uu____5096 =
                              let uu____5097 =
                                let uu____5104 =
                                  let uu____5105 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____5105
                                   in
                                (uu____5104,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____5097  in
                            FStar_Pervasives_Native.Some uu____5096)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5113 =
                       let uu____5114 =
                         let uu____5119 =
                           let uu____5120 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____5120
                            in
                         (se, uu____5119)  in
                       Eff_name uu____5114  in
                     FStar_Pervasives_Native.Some uu____5113
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5121 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____5140 =
                       let uu____5141 =
                         let uu____5148 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                Prims.int_one) FStar_Pervasives_Native.None
                            in
                         (uu____5148, [])  in
                       Term_name uu____5141  in
                     FStar_Pervasives_Native.Some uu____5140
                 | uu____5152 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____5174 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____5174 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____5232 =
            match uu____5232 with
            | (id1,l,dd,used_marker) ->
                (FStar_ST.op_Colon_Equals used_marker true;
                 (let uu____5390 =
                    let uu____5391 =
                      let uu____5398 =
                        let uu____5399 =
                          let uu____5400 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range l uu____5400  in
                        FStar_Syntax_Syntax.fvar uu____5399 dd
                          FStar_Pervasives_Native.None
                         in
                      (uu____5398, [])  in
                    Term_name uu____5391  in
                  FStar_Pervasives_Native.Some uu____5390))
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____5408 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____5408 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____5416 -> FStar_Pervasives_Native.None)
            | uu____5419 -> FStar_Pervasives_Native.None  in
          match found_unmangled with
          | FStar_Pervasives_Native.None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
  
let (try_lookup_effect_name' :
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)
          FStar_Pervasives_Native.option)
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____5457 = try_lookup_name true exclude_interf env lid  in
        match uu____5457 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____5473 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5493 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5493 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5508 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5534 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5534 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5550;
             FStar_Syntax_Syntax.sigquals = uu____5551;
             FStar_Syntax_Syntax.sigmeta = uu____5552;
             FStar_Syntax_Syntax.sigattrs = uu____5553;
             FStar_Syntax_Syntax.sigopts = uu____5554;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5574,uu____5575,uu____5576,uu____5577,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5579;
             FStar_Syntax_Syntax.sigquals = uu____5580;
             FStar_Syntax_Syntax.sigmeta = uu____5581;
             FStar_Syntax_Syntax.sigattrs = uu____5582;
             FStar_Syntax_Syntax.sigopts = uu____5583;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5607 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5633 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5633 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5643;
             FStar_Syntax_Syntax.sigquals = uu____5644;
             FStar_Syntax_Syntax.sigmeta = uu____5645;
             FStar_Syntax_Syntax.sigattrs = uu____5646;
             FStar_Syntax_Syntax.sigopts = uu____5647;_},uu____5648)
          -> FStar_Pervasives_Native.Some ne
      | uu____5659 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____5678 = try_lookup_effect_name env lid  in
      match uu____5678 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5683 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5698 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5698 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5708,uu____5709,uu____5710,uu____5711);
             FStar_Syntax_Syntax.sigrng = uu____5712;
             FStar_Syntax_Syntax.sigquals = uu____5713;
             FStar_Syntax_Syntax.sigmeta = uu____5714;
             FStar_Syntax_Syntax.sigattrs = uu____5715;
             FStar_Syntax_Syntax.sigopts = uu____5716;_},uu____5717)
          ->
          let rec aux new_name =
            let uu____5740 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____5740 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5761) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5772 =
                       let uu____5773 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5773
                        in
                     FStar_Pervasives_Native.Some uu____5772
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5774,uu____5775,uu____5776,cmp,uu____5778) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5784 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5785,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5791 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals_and_attrs :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.qualifier Prims.list *
        FStar_Syntax_Syntax.attribute Prims.list))
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___20_5842 =
        match uu___20_5842 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5858,uu____5859,uu____5860);
             FStar_Syntax_Syntax.sigrng = uu____5861;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5863;
             FStar_Syntax_Syntax.sigattrs = attrs;
             FStar_Syntax_Syntax.sigopts = uu____5865;_},uu____5866)
            -> FStar_Pervasives_Native.Some (quals, attrs)
        | uu____5887 -> FStar_Pervasives_Native.None  in
      let uu____5901 =
        resolve_in_open_namespaces' env lid
          (fun uu____5921  -> FStar_Pervasives_Native.None)
          (fun uu____5931  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5901 with
      | FStar_Pervasives_Native.Some qa -> qa
      | uu____5965 -> ([], [])
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5993 =
        FStar_List.tryFind
          (fun uu____6008  ->
             match uu____6008 with
             | (mlid,modul) ->
                 let uu____6016 = FStar_Ident.path_of_lid mlid  in
                 uu____6016 = path) env.modules
         in
      match uu____5993 with
      | FStar_Pervasives_Native.Some (uu____6019,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___21_6059 =
        match uu___21_6059 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____6067,lbs),uu____6069);
             FStar_Syntax_Syntax.sigrng = uu____6070;
             FStar_Syntax_Syntax.sigquals = uu____6071;
             FStar_Syntax_Syntax.sigmeta = uu____6072;
             FStar_Syntax_Syntax.sigattrs = uu____6073;
             FStar_Syntax_Syntax.sigopts = uu____6074;_},uu____6075)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____6095 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____6095
        | uu____6096 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6103  -> FStar_Pervasives_Native.None)
        (fun uu____6105  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___22_6138 =
        match uu___22_6138 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____6149);
             FStar_Syntax_Syntax.sigrng = uu____6150;
             FStar_Syntax_Syntax.sigquals = uu____6151;
             FStar_Syntax_Syntax.sigmeta = uu____6152;
             FStar_Syntax_Syntax.sigattrs = uu____6153;
             FStar_Syntax_Syntax.sigopts = uu____6154;_},uu____6155)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____6183 -> FStar_Pervasives_Native.None)
        | uu____6190 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6201  -> FStar_Pervasives_Native.None)
        (fun uu____6205  -> FStar_Pervasives_Native.None) k_global_def
  
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
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let uu____6265 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____6265 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____6290 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____6328) ->
        FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_with_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l 
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____6386 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____6386 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____6418 = try_lookup_lid env l  in
      match uu____6418 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____6424 =
            let uu____6425 = FStar_Syntax_Subst.compress e  in
            uu____6425.FStar_Syntax_Syntax.n  in
          (match uu____6424 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____6431 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____6443 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____6443 with
      | (uu____6453,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____6474 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____6478 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____6478 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____6483 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___882_6514 = env  in
        {
          curmodule = (uu___882_6514.curmodule);
          curmonad = (uu___882_6514.curmonad);
          modules = (uu___882_6514.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___882_6514.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___882_6514.sigaccum);
          sigmap = (uu___882_6514.sigmap);
          iface = (uu___882_6514.iface);
          admitted_iface = (uu___882_6514.admitted_iface);
          expect_typ = (uu___882_6514.expect_typ);
          remaining_iface_decls = (uu___882_6514.remaining_iface_decls);
          syntax_only = (uu___882_6514.syntax_only);
          ds_hooks = (uu___882_6514.ds_hooks);
          dep_graph = (uu___882_6514.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____6530 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____6530 drop_attributes
  
let (try_lookup_datacon :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 se =
        match se with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____6587,uu____6588,uu____6589);
             FStar_Syntax_Syntax.sigrng = uu____6590;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6592;
             FStar_Syntax_Syntax.sigattrs = uu____6593;
             FStar_Syntax_Syntax.sigopts = uu____6594;_},uu____6595)
            ->
            let uu____6604 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___23_6610  ->
                      match uu___23_6610 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6613 -> false))
               in
            if uu____6604
            then
              let uu____6618 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6618
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6621;
             FStar_Syntax_Syntax.sigrng = uu____6622;
             FStar_Syntax_Syntax.sigquals = uu____6623;
             FStar_Syntax_Syntax.sigmeta = uu____6624;
             FStar_Syntax_Syntax.sigattrs = uu____6625;
             FStar_Syntax_Syntax.sigopts = uu____6626;_},uu____6627)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____6655 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____6655
        | uu____6656 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6663  -> FStar_Pervasives_Native.None)
        (fun uu____6665  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___24_6700 =
        match uu___24_6700 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6710,uu____6711,uu____6712,uu____6713,datas,uu____6715);
             FStar_Syntax_Syntax.sigrng = uu____6716;
             FStar_Syntax_Syntax.sigquals = uu____6717;
             FStar_Syntax_Syntax.sigmeta = uu____6718;
             FStar_Syntax_Syntax.sigattrs = uu____6719;
             FStar_Syntax_Syntax.sigopts = uu____6720;_},uu____6721)
            -> FStar_Pervasives_Native.Some datas
        | uu____6740 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6751  -> FStar_Pervasives_Native.None)
        (fun uu____6755  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____6834 =
    let uu____6835 =
      let uu____6840 =
        let uu____6843 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6843  in
      let uu____6877 = FStar_ST.op_Bang record_cache  in uu____6840 ::
        uu____6877
       in
    FStar_ST.op_Colon_Equals record_cache uu____6835  in
  let pop1 uu____6943 =
    let uu____6944 =
      let uu____6949 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6949  in
    FStar_ST.op_Colon_Equals record_cache uu____6944  in
  let snapshot1 uu____7020 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____7044 =
    let uu____7045 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____7045  in
  let insert r =
    let uu____7085 =
      let uu____7090 = let uu____7093 = peek1 ()  in r :: uu____7093  in
      let uu____7096 =
        let uu____7101 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____7101  in
      uu____7090 :: uu____7096  in
    FStar_ST.op_Colon_Equals record_cache uu____7085  in
  let filter1 uu____7169 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____7178 =
      let uu____7183 =
        let uu____7188 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____7188  in
      filtered :: uu____7183  in
    FStar_ST.op_Colon_Equals record_cache uu____7178  in
  let aux = ((push1, pop1), ((snapshot1, rollback1), (peek1, insert)))  in
  (aux, filter1) 
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
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____8114) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___25_8133  ->
                   match uu___25_8133 with
                   | FStar_Syntax_Syntax.RecordType uu____8135 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____8145 -> true
                   | uu____8155 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___26_8181  ->
                      match uu___26_8181 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____8184,uu____8185,uu____8186,uu____8187,uu____8188);
                          FStar_Syntax_Syntax.sigrng = uu____8189;
                          FStar_Syntax_Syntax.sigquals = uu____8190;
                          FStar_Syntax_Syntax.sigmeta = uu____8191;
                          FStar_Syntax_Syntax.sigattrs = uu____8192;
                          FStar_Syntax_Syntax.sigopts = uu____8193;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____8206 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___27_8244  ->
                    match uu___27_8244 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____8248,uu____8249,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____8251;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____8253;
                        FStar_Syntax_Syntax.sigattrs = uu____8254;
                        FStar_Syntax_Syntax.sigopts = uu____8255;_} ->
                        let uu____8268 =
                          let uu____8269 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____8269  in
                        (match uu____8268 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____8275,t,uu____8277,uu____8278,uu____8279);
                             FStar_Syntax_Syntax.sigrng = uu____8280;
                             FStar_Syntax_Syntax.sigquals = uu____8281;
                             FStar_Syntax_Syntax.sigmeta = uu____8282;
                             FStar_Syntax_Syntax.sigattrs = uu____8283;
                             FStar_Syntax_Syntax.sigopts = uu____8284;_} ->
                             let uu____8297 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____8297 with
                              | (formals,uu____8313) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____8367  ->
                                            match uu____8367 with
                                            | (x,q) ->
                                                let uu____8380 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____8380
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____8435  ->
                                            match uu____8435 with
                                            | (x,q) ->
                                                ((x.FStar_Syntax_Syntax.ppname),
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
                                  ((let uu____8459 =
                                      let uu____8462 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____8462  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____8459);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____8521 =
                                            match uu____8521 with
                                            | (id1,uu____8527) ->
                                                let modul =
                                                  let uu____8530 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____8530.FStar_Ident.str
                                                   in
                                                let uu____8531 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____8531 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____8554 =
                                                         let uu____8555 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8555
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8554);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8600 =
                                                               let uu____8601
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8601.FStar_Ident.ident
                                                                in
                                                             uu____8600.FStar_Ident.idText
                                                              in
                                                           let uu____8603 =
                                                             let uu____8604 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8604
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8603))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8656 -> ())
                    | uu____8657 -> ()))
        | uu____8658 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8680 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8680 with
        | (ns,id1) ->
            let uu____8697 = peek_record_cache ()  in
            FStar_Util.find_map uu____8697
              (fun record  ->
                 let uu____8703 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8709  -> FStar_Pervasives_Native.None)
                   uu____8703)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8711  -> Cont_ignore) (fun uu____8713  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8719 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8719)
        (fun k  -> fun uu____8725  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8741 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8741 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8747 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8767 = try_lookup_record_by_field_name env lid  in
        match uu____8767 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8772 =
              let uu____8774 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8774  in
            let uu____8775 =
              let uu____8777 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8777  in
            uu____8772 = uu____8775 ->
            let uu____8779 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8783  -> Cont_ok ())
               in
            (match uu____8779 with
             | Cont_ok uu____8785 -> true
             | uu____8787 -> false)
        | uu____8791 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8813 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8813 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8824 =
            let uu____8830 =
              let uu____8831 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8832 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8831 uu____8832  in
            (uu____8830, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8824
      | uu____8839 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8857  ->
    let uu____8858 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8858
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8879  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___28_8892  ->
      match uu___28_8892 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___29_8930 =
            match uu___29_8930 with
            | Rec_binding uu____8932 -> true
            | uu____8934 -> false  in
          let this_env =
            let uu___1112_8937 = env  in
            let uu____8938 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1112_8937.curmodule);
              curmonad = (uu___1112_8937.curmonad);
              modules = (uu___1112_8937.modules);
              scope_mods = uu____8938;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1112_8937.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1112_8937.sigaccum);
              sigmap = (uu___1112_8937.sigmap);
              iface = (uu___1112_8937.iface);
              admitted_iface = (uu___1112_8937.admitted_iface);
              expect_typ = (uu___1112_8937.expect_typ);
              remaining_iface_decls = (uu___1112_8937.remaining_iface_decls);
              syntax_only = (uu___1112_8937.syntax_only);
              ds_hooks = (uu___1112_8937.ds_hooks);
              dep_graph = (uu___1112_8937.dep_graph)
            }  in
          let uu____8941 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8941 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8958 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1120_8983 = env  in
      {
        curmodule = (uu___1120_8983.curmodule);
        curmonad = (uu___1120_8983.curmonad);
        modules = (uu___1120_8983.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1120_8983.exported_ids);
        trans_exported_ids = (uu___1120_8983.trans_exported_ids);
        includes = (uu___1120_8983.includes);
        sigaccum = (uu___1120_8983.sigaccum);
        sigmap = (uu___1120_8983.sigmap);
        iface = (uu___1120_8983.iface);
        admitted_iface = (uu___1120_8983.admitted_iface);
        expect_typ = (uu___1120_8983.expect_typ);
        remaining_iface_decls = (uu___1120_8983.remaining_iface_decls);
        syntax_only = (uu___1120_8983.syntax_only);
        ds_hooks = (uu___1120_8983.ds_hooks);
        dep_graph = (uu___1120_8983.dep_graph)
      }
  
let (push_bv' :
  env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv * used_marker)) =
  fun env  ->
    fun x  ->
      let bv =
        FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
          (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange))
          FStar_Syntax_Syntax.tun
         in
      let used_marker = FStar_Util.mk_ref false  in
      ((push_scope_mod env (Local_binding (x, bv, used_marker))), bv,
        used_marker)
  
let (push_bv : env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv)) =
  fun env  ->
    fun x  ->
      let uu____9023 = push_bv' env x  in
      match uu____9023 with | (env1,bv,uu____9036) -> (env1, bv)
  
let (push_top_level_rec_binding :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.delta_depth -> (env * Prims.bool FStar_ST.ref))
  =
  fun env0  ->
    fun x  ->
      fun dd  ->
        let l = qualify env0 x  in
        let uu____9068 =
          (unique false true env0 l) || (FStar_Options.interactive ())  in
        if uu____9068
        then
          let used_marker = FStar_Util.mk_ref false  in
          ((push_scope_mod env0 (Rec_binding (x, l, dd, used_marker))),
            used_marker)
        else
          (let uu____9091 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____9091)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____9142) ->
                let uu____9150 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____9150 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____9155 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____9155
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____9164 =
            let uu____9170 =
              let uu____9172 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____9172 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____9170)  in
          let uu____9176 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____9164 uu____9176  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____9185 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____9198 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____9209 -> (false, true)
            | uu____9222 -> (false, false)  in
          match uu____9185 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____9236 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____9242 =
                       let uu____9244 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____9244  in
                     if uu____9242
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____9236 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____9252 ->
                   (extract_record env globals s;
                    (let uu___1169_9256 = env  in
                     {
                       curmodule = (uu___1169_9256.curmodule);
                       curmonad = (uu___1169_9256.curmonad);
                       modules = (uu___1169_9256.modules);
                       scope_mods = (uu___1169_9256.scope_mods);
                       exported_ids = (uu___1169_9256.exported_ids);
                       trans_exported_ids =
                         (uu___1169_9256.trans_exported_ids);
                       includes = (uu___1169_9256.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1169_9256.sigmap);
                       iface = (uu___1169_9256.iface);
                       admitted_iface = (uu___1169_9256.admitted_iface);
                       expect_typ = (uu___1169_9256.expect_typ);
                       remaining_iface_decls =
                         (uu___1169_9256.remaining_iface_decls);
                       syntax_only = (uu___1169_9256.syntax_only);
                       ds_hooks = (uu___1169_9256.ds_hooks);
                       dep_graph = (uu___1169_9256.dep_graph)
                     })))
           in
        let env2 =
          let uu___1172_9258 = env1  in
          let uu____9259 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1172_9258.curmodule);
            curmonad = (uu___1172_9258.curmonad);
            modules = (uu___1172_9258.modules);
            scope_mods = uu____9259;
            exported_ids = (uu___1172_9258.exported_ids);
            trans_exported_ids = (uu___1172_9258.trans_exported_ids);
            includes = (uu___1172_9258.includes);
            sigaccum = (uu___1172_9258.sigaccum);
            sigmap = (uu___1172_9258.sigmap);
            iface = (uu___1172_9258.iface);
            admitted_iface = (uu___1172_9258.admitted_iface);
            expect_typ = (uu___1172_9258.expect_typ);
            remaining_iface_decls = (uu___1172_9258.remaining_iface_decls);
            syntax_only = (uu___1172_9258.syntax_only);
            ds_hooks = (uu___1172_9258.ds_hooks);
            dep_graph = (uu___1172_9258.dep_graph)
          }  in
        let uu____9285 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9311) ->
              let uu____9320 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____9320)
          | uu____9347 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____9285 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____9406  ->
                     match uu____9406 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____9428 =
                                    let uu____9431 = FStar_ST.op_Bang globals
                                       in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____9431
                                     in
                                  FStar_ST.op_Colon_Equals globals uu____9428);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____9482 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____9482.FStar_Ident.str  in
                                      ((let uu____9484 =
                                          get_exported_id_set env3 modul  in
                                        match uu____9484 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____9506 =
                                              let uu____9507 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____9507
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____9506
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
                let uu___1197_9564 = env3  in
                let uu____9565 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1197_9564.curmodule);
                  curmonad = (uu___1197_9564.curmonad);
                  modules = (uu___1197_9564.modules);
                  scope_mods = uu____9565;
                  exported_ids = (uu___1197_9564.exported_ids);
                  trans_exported_ids = (uu___1197_9564.trans_exported_ids);
                  includes = (uu___1197_9564.includes);
                  sigaccum = (uu___1197_9564.sigaccum);
                  sigmap = (uu___1197_9564.sigmap);
                  iface = (uu___1197_9564.iface);
                  admitted_iface = (uu___1197_9564.admitted_iface);
                  expect_typ = (uu___1197_9564.expect_typ);
                  remaining_iface_decls =
                    (uu___1197_9564.remaining_iface_decls);
                  syntax_only = (uu___1197_9564.syntax_only);
                  ds_hooks = (uu___1197_9564.ds_hooks);
                  dep_graph = (uu___1197_9564.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9626 =
        let uu____9631 = resolve_module_name env ns false  in
        match uu____9631 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9646 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9664  ->
                      match uu____9664 with
                      | (m,uu____9671) ->
                          let uu____9672 =
                            let uu____9674 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____9674 "."  in
                          let uu____9677 =
                            let uu____9679 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____9679 "."  in
                          FStar_Util.starts_with uu____9672 uu____9677))
               in
            if uu____9646
            then (ns, Open_namespace)
            else
              (let uu____9689 =
                 let uu____9695 =
                   let uu____9697 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9697
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9695)  in
               let uu____9701 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9689 uu____9701)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____9626 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9723 = resolve_module_name env ns false  in
      match uu____9723 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9733 = current_module env1  in
              uu____9733.FStar_Ident.str  in
            (let uu____9735 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9735 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9759 =
                   let uu____9762 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9762
                    in
                 FStar_ST.op_Colon_Equals incl uu____9759);
            (match () with
             | () ->
                 let uu____9811 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____9811 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9831 =
                          let uu____9928 = get_exported_id_set env1 curmod
                             in
                          let uu____9975 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____9928, uu____9975)  in
                        match uu____9831 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10391 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10391  in
                              let ex = cur_exports k  in
                              (let uu____10492 =
                                 let uu____10496 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____10496 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____10492);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____10588 =
                                     let uu____10592 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____10592 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10588)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10641 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____10743 =
                        let uu____10749 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10749)
                         in
                      let uu____10753 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____10743 uu____10753))))
      | uu____10754 ->
          let uu____10757 =
            let uu____10763 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____10763)  in
          let uu____10767 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____10757 uu____10767
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____10784 = module_is_defined env l  in
        if uu____10784
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____10791 =
             let uu____10797 =
               let uu____10799 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____10799  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____10797)  in
           let uu____10803 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____10791 uu____10803)
  
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
                      let uu____10846 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____10846 ->
                      let uu____10851 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____10851 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____10866;
                              FStar_Syntax_Syntax.sigrng = uu____10867;
                              FStar_Syntax_Syntax.sigquals = uu____10868;
                              FStar_Syntax_Syntax.sigmeta = uu____10869;
                              FStar_Syntax_Syntax.sigattrs = uu____10870;
                              FStar_Syntax_Syntax.sigopts = uu____10871;_},uu____10872)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____10892;
                              FStar_Syntax_Syntax.sigrng = uu____10893;
                              FStar_Syntax_Syntax.sigquals = uu____10894;
                              FStar_Syntax_Syntax.sigmeta = uu____10895;
                              FStar_Syntax_Syntax.sigattrs = uu____10896;
                              FStar_Syntax_Syntax.sigopts = uu____10897;_},uu____10898)
                           -> lids
                       | uu____10928 ->
                           ((let uu____10937 =
                               let uu____10939 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____10939  in
                             if uu____10937
                             then
                               let uu____10942 = FStar_Ident.range_of_lid l
                                  in
                               let uu____10943 =
                                 let uu____10949 =
                                   let uu____10951 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____10951
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____10949)
                                  in
                               FStar_Errors.log_issue uu____10942 uu____10943
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1291_10968 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1291_10968.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1291_10968.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1291_10968.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1291_10968.FStar_Syntax_Syntax.sigattrs);
                                   FStar_Syntax_Syntax.sigopts =
                                     (uu___1291_10968.FStar_Syntax_Syntax.sigopts)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____10970 -> lids) [])
         in
      let uu___1296_10971 = m  in
      let uu____10972 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____10982,uu____10983) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1305_10986 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1305_10986.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1305_10986.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1305_10986.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1305_10986.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1305_10986.FStar_Syntax_Syntax.sigopts)
                    }
                | uu____10987 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1296_10971.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____10972;
        FStar_Syntax_Syntax.exports =
          (uu___1296_10971.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1296_10971.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11011) ->
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
                                (lid,uu____11032,uu____11033,uu____11034,uu____11035,uu____11036)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____11052,uu____11053)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11070 =
                                        let uu____11077 =
                                          let uu____11078 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____11079 =
                                            let uu____11086 =
                                              let uu____11087 =
                                                let uu____11102 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11102)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11087
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11086
                                             in
                                          uu____11079
                                            FStar_Pervasives_Native.None
                                            uu____11078
                                           in
                                        (lid, univ_names, uu____11077)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11070
                                       in
                                    let se2 =
                                      let uu___1337_11116 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1337_11116.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1337_11116.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1337_11116.FStar_Syntax_Syntax.sigattrs);
                                        FStar_Syntax_Syntax.sigopts =
                                          (uu___1337_11116.FStar_Syntax_Syntax.sigopts)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11126 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11130,uu____11131) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11140,lbs),uu____11142)
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
                             let uu____11160 =
                               let uu____11162 =
                                 let uu____11163 =
                                   let uu____11166 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11166.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11163.FStar_Syntax_Syntax.v  in
                               uu____11162.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____11160))
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
                               let uu____11183 =
                                 let uu____11186 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11186.FStar_Syntax_Syntax.fv_name  in
                               uu____11183.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1360_11191 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1360_11191.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1360_11191.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1360_11191.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___1360_11191.FStar_Syntax_Syntax.sigopts)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11201 -> ()));
      (let curmod =
         let uu____11204 = current_module env  in uu____11204.FStar_Ident.str
          in
       (let uu____11206 =
          let uu____11303 = get_exported_id_set env curmod  in
          let uu____11350 = get_trans_exported_id_set env curmod  in
          (uu____11303, uu____11350)  in
        match uu____11206 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____11769 = cur_ex eikind  in
                FStar_ST.op_Bang uu____11769  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____11875 =
                let uu____11879 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____11879  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____11875  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____11928 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1378_12026 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1378_12026.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1378_12026.exported_ids);
                    trans_exported_ids = (uu___1378_12026.trans_exported_ids);
                    includes = (uu___1378_12026.includes);
                    sigaccum = [];
                    sigmap = (uu___1378_12026.sigmap);
                    iface = (uu___1378_12026.iface);
                    admitted_iface = (uu___1378_12026.admitted_iface);
                    expect_typ = (uu___1378_12026.expect_typ);
                    remaining_iface_decls =
                      (uu___1378_12026.remaining_iface_decls);
                    syntax_only = (uu___1378_12026.syntax_only);
                    ds_hooks = (uu___1378_12026.ds_hooks);
                    dep_graph = (uu___1378_12026.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____12052  ->
         push_record_cache ();
         (let uu____12055 =
            let uu____12058 = FStar_ST.op_Bang stack  in env :: uu____12058
             in
          FStar_ST.op_Colon_Equals stack uu____12055);
         (let uu___1384_12107 = env  in
          let uu____12108 = FStar_Util.smap_copy env.exported_ids  in
          let uu____12113 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____12118 = FStar_Util.smap_copy env.includes  in
          let uu____12129 = FStar_Util.smap_copy env.sigmap  in
          {
            curmodule = (uu___1384_12107.curmodule);
            curmonad = (uu___1384_12107.curmonad);
            modules = (uu___1384_12107.modules);
            scope_mods = (uu___1384_12107.scope_mods);
            exported_ids = uu____12108;
            trans_exported_ids = uu____12113;
            includes = uu____12118;
            sigaccum = (uu___1384_12107.sigaccum);
            sigmap = uu____12129;
            iface = (uu___1384_12107.iface);
            admitted_iface = (uu___1384_12107.admitted_iface);
            expect_typ = (uu___1384_12107.expect_typ);
            remaining_iface_decls = (uu___1384_12107.remaining_iface_decls);
            syntax_only = (uu___1384_12107.syntax_only);
            ds_hooks = (uu___1384_12107.ds_hooks);
            dep_graph = (uu___1384_12107.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____12147  ->
    FStar_Util.atomically
      (fun uu____12154  ->
         let uu____12155 = FStar_ST.op_Bang stack  in
         match uu____12155 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____12210 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12257 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____12261 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____12303 = FStar_Util.smap_try_find sm' k  in
              match uu____12303 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1419_12334 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1419_12334.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1419_12334.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1419_12334.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1419_12334.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___1419_12334.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____12335 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12343 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____12370 = finish env modul1  in (uu____12370, modul1)
  
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list ;
  exported_id_fields: Prims.string Prims.list }
let (__proj__Mkexported_ids__item__exported_id_terms :
  exported_ids -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { exported_id_terms; exported_id_fields;_} -> exported_id_terms
  
let (__proj__Mkexported_ids__item__exported_id_fields :
  exported_ids -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { exported_id_terms; exported_id_fields;_} -> exported_id_fields
  
let (as_exported_ids : exported_id_set -> exported_ids) =
  fun e  ->
    let terms =
      let uu____12439 =
        let uu____12443 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____12443  in
      FStar_Util.set_elements uu____12439  in
    let fields =
      let uu____12506 =
        let uu____12510 = e Exported_id_field  in
        FStar_ST.op_Bang uu____12510  in
      FStar_Util.set_elements uu____12506  in
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
          let uu____12602 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____12602  in
        let fields =
          let uu____12616 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____12616  in
        (fun uu___30_12624  ->
           match uu___30_12624 with
           | Exported_id_term_type  -> terms
           | Exported_id_field  -> fields)
  
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option }
let (__proj__Mkmodule_inclusion_info__item__mii_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids; mii_trans_exported_ids; mii_includes;_} ->
        mii_exported_ids
  
let (__proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids; mii_trans_exported_ids; mii_includes;_} ->
        mii_trans_exported_ids
  
let (__proj__Mkmodule_inclusion_info__item__mii_includes :
  module_inclusion_info ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee  ->
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
  'Auu____12728 .
    'Auu____12728 Prims.list FStar_Pervasives_Native.option ->
      'Auu____12728 Prims.list FStar_ST.ref
  =
  fun uu___31_12741  ->
    match uu___31_12741 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____12784 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____12784 as_exported_ids  in
      let uu____12790 = as_ids_opt env.exported_ids  in
      let uu____12793 = as_ids_opt env.trans_exported_ids  in
      let uu____12796 =
        let uu____12801 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____12801 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____12790;
        mii_trans_exported_ids = uu____12793;
        mii_includes = uu____12796
      }
  
let (prepare_module_or_interface :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident -> module_inclusion_info -> (env * Prims.bool))
  =
  fun intf  ->
    fun admitted  ->
      fun env  ->
        fun mname  ->
          fun mii  ->
            let prep env1 =
              let filename =
                let uu____12890 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____12890 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___32_12912 =
                  match uu___32_12912 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____12924  ->
                     match uu____12924 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if (FStar_List.length mname.FStar_Ident.ns) > Prims.int_zero
                then
                  let uu____12950 =
                    let uu____12955 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____12955, Open_namespace)  in
                  [uu____12950]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____12986 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____12986);
              (match () with
               | () ->
                   ((let uu____12991 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____12991);
                    (match () with
                     | () ->
                         ((let uu____12996 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____12996);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1489_13006 = env1  in
                                 let uu____13007 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1489_13006.curmonad);
                                   modules = (uu___1489_13006.modules);
                                   scope_mods = uu____13007;
                                   exported_ids =
                                     (uu___1489_13006.exported_ids);
                                   trans_exported_ids =
                                     (uu___1489_13006.trans_exported_ids);
                                   includes = (uu___1489_13006.includes);
                                   sigaccum = (uu___1489_13006.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1489_13006.expect_typ);
                                   remaining_iface_decls =
                                     (uu___1489_13006.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1489_13006.syntax_only);
                                   ds_hooks = (uu___1489_13006.ds_hooks);
                                   dep_graph = (uu___1489_13006.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____13019 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____13045  ->
                      match uu____13045 with
                      | (l,uu____13052) -> FStar_Ident.lid_equals l mname))
               in
            match uu____13019 with
            | FStar_Pervasives_Native.None  ->
                let uu____13062 = prep env  in (uu____13062, false)
            | FStar_Pervasives_Native.Some (uu____13065,m) ->
                ((let uu____13072 =
                    (let uu____13076 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____13076) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____13072
                  then
                    let uu____13079 =
                      let uu____13085 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13085)
                       in
                    let uu____13089 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____13079 uu____13089
                  else ());
                 (let uu____13092 =
                    let uu____13093 = push env  in prep uu____13093  in
                  (uu____13092, true)))
  
let (enter_monad_scope : env -> FStar_Ident.ident -> env) =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MonadAlreadyDefined,
              (Prims.op_Hat "Trying to define monad "
                 (Prims.op_Hat mname.FStar_Ident.idText
                    (Prims.op_Hat ", but already in monad scope "
                       mname'.FStar_Ident.idText))))
            mname.FStar_Ident.idRange
      | FStar_Pervasives_Native.None  ->
          let uu___1510_13111 = env  in
          {
            curmodule = (uu___1510_13111.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1510_13111.modules);
            scope_mods = (uu___1510_13111.scope_mods);
            exported_ids = (uu___1510_13111.exported_ids);
            trans_exported_ids = (uu___1510_13111.trans_exported_ids);
            includes = (uu___1510_13111.includes);
            sigaccum = (uu___1510_13111.sigaccum);
            sigmap = (uu___1510_13111.sigmap);
            iface = (uu___1510_13111.iface);
            admitted_iface = (uu___1510_13111.admitted_iface);
            expect_typ = (uu___1510_13111.expect_typ);
            remaining_iface_decls = (uu___1510_13111.remaining_iface_decls);
            syntax_only = (uu___1510_13111.syntax_only);
            ds_hooks = (uu___1510_13111.ds_hooks);
            dep_graph = (uu___1510_13111.dep_graph)
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
        let uu____13146 = lookup1 lid  in
        match uu____13146 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____13161  ->
                   match uu____13161 with
                   | (lid1,uu____13168) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____13171 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13171  in
            let msg1 =
              if (FStar_List.length lid.FStar_Ident.ns) = Prims.int_zero
              then msg
              else
                (let modul =
                   let uu____13183 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____13184 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____13183 uu____13184  in
                 let uu____13185 = resolve_module_name env modul true  in
                 match uu____13185 with
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
            let uu____13206 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13206
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____13236 = lookup1 id1  in
      match uu____13236 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  