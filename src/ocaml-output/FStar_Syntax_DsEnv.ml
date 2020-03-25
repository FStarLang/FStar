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
  
let new_sigmap : 'uu____2517 . unit -> 'uu____2517 FStar_Util.smap =
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
  'uu____2928 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'uu____2928 cont_t) -> 'uu____2928 cont_t
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
  'uu____3578 'uu____3579 .
    FStar_Range.range ->
      ('uu____3578 * FStar_Syntax_Syntax.bv * 'uu____3579) ->
        FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____3595  ->
      match uu____3595 with | (id',x,uu____3604) -> bv_to_name x r
  
let find_in_module :
  'uu____3616 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'uu____3616)
          -> 'uu____3616 -> 'uu____3616
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
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___10_4001  ->
             match uu___10_4001 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____4005 -> false) env.scope_mods
  
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
                 let uu____4134 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____4134
                   (FStar_Util.map_option
                      (fun uu____4184  ->
                         match uu____4184 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4254 = aux ns_rev_prefix ns_last_id  in
              (match uu____4254 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > Prims.int_zero)
        then
          let uu____4317 =
            let uu____4320 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____4320 true  in
          match uu____4317 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4335 -> do_shorten env ids
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
                  | uu____4456::uu____4457 ->
                      let uu____4460 =
                        let uu____4463 =
                          let uu____4464 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4465 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4464 uu____4465  in
                        resolve_module_name env uu____4463 true  in
                      (match uu____4460 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4470 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4474  -> FStar_Pervasives_Native.None)
                             uu____4470)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___11_4498  ->
      match uu___11_4498 with
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
              let uu____4619 = k_global_def lid1 def  in
              cont_of_option k uu____4619  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4655 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4655)
              (fun r  ->
                 let uu____4661 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4661)
              (fun uu____4665  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4676,uu____4677,uu____4678,l,uu____4680,uu____4681) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___12_4694  ->
               match uu___12_4694 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4697,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4709 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4715,uu____4716,uu____4717)
        -> FStar_Pervasives_Native.None
    | uu____4718 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4734 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4742 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4742
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4734 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4765 =
         let uu____4766 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4766  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4765) &&
        (let uu____4770 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4770 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____4787 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___13_4794  ->
                     match uu___13_4794 with
                     | FStar_Syntax_Syntax.Projector uu____4796 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____4802 -> true
                     | uu____4804 -> false)))
           in
        if uu____4787
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____4809 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___14_4815  ->
                 match uu___14_4815 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____4818 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___15_4824  ->
                    match uu___15_4824 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____4827 -> false)))
             &&
             (let uu____4830 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___16_4836  ->
                        match uu___16_4836 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____4839 -> false))
                 in
              Prims.op_Negation uu____4830))
         in
      if uu____4809 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___19_4891 =
            match uu___19_4891 with
            | (uu____4899,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____4903) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____4908 ->
                     let uu____4925 =
                       let uu____4926 =
                         let uu____4933 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____4933, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____4926  in
                     FStar_Pervasives_Native.Some uu____4925
                 | FStar_Syntax_Syntax.Sig_datacon uu____4936 ->
                     let uu____4952 =
                       let uu____4953 =
                         let uu____4960 =
                           let uu____4961 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____4961
                            in
                         (uu____4960, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____4953  in
                     FStar_Pervasives_Native.Some uu____4952
                 | FStar_Syntax_Syntax.Sig_let ((uu____4966,lbs),uu____4968)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____4980 =
                       let uu____4981 =
                         let uu____4988 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____4988, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____4981  in
                     FStar_Pervasives_Native.Some uu____4980
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____4992,uu____4993) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____4997 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___17_5003  ->
                                  match uu___17_5003 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____5006 -> false)))
                        in
                     if uu____4997
                     then
                       let lid2 =
                         let uu____5012 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____5012  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____5014 =
                         FStar_Util.find_map quals
                           (fun uu___18_5019  ->
                              match uu___18_5019 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____5023 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____5014 with
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
                        | uu____5032 ->
                            let uu____5035 =
                              let uu____5036 =
                                let uu____5043 =
                                  let uu____5044 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____5044
                                   in
                                (uu____5043,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____5036  in
                            FStar_Pervasives_Native.Some uu____5035)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5052 =
                       let uu____5053 =
                         let uu____5058 =
                           let uu____5059 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____5059
                            in
                         (se, uu____5058)  in
                       Eff_name uu____5053  in
                     FStar_Pervasives_Native.Some uu____5052
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5060 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____5079 =
                       let uu____5080 =
                         let uu____5087 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                Prims.int_one) FStar_Pervasives_Native.None
                            in
                         (uu____5087, [])  in
                       Term_name uu____5080  in
                     FStar_Pervasives_Native.Some uu____5079
                 | uu____5091 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____5113 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____5113 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____5171 =
            match uu____5171 with
            | (id1,l,dd,used_marker) ->
                (FStar_ST.op_Colon_Equals used_marker true;
                 (let uu____5329 =
                    let uu____5330 =
                      let uu____5337 =
                        let uu____5338 =
                          let uu____5339 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range l uu____5339  in
                        FStar_Syntax_Syntax.fvar uu____5338 dd
                          FStar_Pervasives_Native.None
                         in
                      (uu____5337, [])  in
                    Term_name uu____5330  in
                  FStar_Pervasives_Native.Some uu____5329))
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____5347 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____5347 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____5355 -> FStar_Pervasives_Native.None)
            | uu____5358 -> FStar_Pervasives_Native.None  in
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
        let uu____5396 = try_lookup_name true exclude_interf env lid  in
        match uu____5396 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____5412 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5432 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5432 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5447 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5473 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5473 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5489;
             FStar_Syntax_Syntax.sigquals = uu____5490;
             FStar_Syntax_Syntax.sigmeta = uu____5491;
             FStar_Syntax_Syntax.sigattrs = uu____5492;
             FStar_Syntax_Syntax.sigopts = uu____5493;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5513,uu____5514,uu____5515,uu____5516,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5518;
             FStar_Syntax_Syntax.sigquals = uu____5519;
             FStar_Syntax_Syntax.sigmeta = uu____5520;
             FStar_Syntax_Syntax.sigattrs = uu____5521;
             FStar_Syntax_Syntax.sigopts = uu____5522;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5546 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5572 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5572 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5582;
             FStar_Syntax_Syntax.sigquals = uu____5583;
             FStar_Syntax_Syntax.sigmeta = uu____5584;
             FStar_Syntax_Syntax.sigattrs = uu____5585;
             FStar_Syntax_Syntax.sigopts = uu____5586;_},uu____5587)
          -> FStar_Pervasives_Native.Some ne
      | uu____5598 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____5617 = try_lookup_effect_name env lid  in
      match uu____5617 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5622 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5637 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5637 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5647,uu____5648,uu____5649,uu____5650);
             FStar_Syntax_Syntax.sigrng = uu____5651;
             FStar_Syntax_Syntax.sigquals = uu____5652;
             FStar_Syntax_Syntax.sigmeta = uu____5653;
             FStar_Syntax_Syntax.sigattrs = uu____5654;
             FStar_Syntax_Syntax.sigopts = uu____5655;_},uu____5656)
          ->
          let rec aux new_name =
            let uu____5679 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____5679 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5700) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5711 =
                       let uu____5712 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5712
                        in
                     FStar_Pervasives_Native.Some uu____5711
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5713,uu____5714,uu____5715,cmp,uu____5717) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5723 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5724,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5730 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals_and_attrs :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.qualifier Prims.list *
        FStar_Syntax_Syntax.attribute Prims.list))
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___20_5781 =
        match uu___20_5781 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5797,uu____5798,uu____5799);
             FStar_Syntax_Syntax.sigrng = uu____5800;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5802;
             FStar_Syntax_Syntax.sigattrs = attrs;
             FStar_Syntax_Syntax.sigopts = uu____5804;_},uu____5805)
            -> FStar_Pervasives_Native.Some (quals, attrs)
        | uu____5826 -> FStar_Pervasives_Native.None  in
      let uu____5840 =
        resolve_in_open_namespaces' env lid
          (fun uu____5860  -> FStar_Pervasives_Native.None)
          (fun uu____5870  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5840 with
      | FStar_Pervasives_Native.Some qa -> qa
      | uu____5904 -> ([], [])
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5932 =
        FStar_List.tryFind
          (fun uu____5947  ->
             match uu____5947 with
             | (mlid,modul) ->
                 let uu____5955 = FStar_Ident.path_of_lid mlid  in
                 uu____5955 = path) env.modules
         in
      match uu____5932 with
      | FStar_Pervasives_Native.Some (uu____5958,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___21_5998 =
        match uu___21_5998 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____6006,lbs),uu____6008);
             FStar_Syntax_Syntax.sigrng = uu____6009;
             FStar_Syntax_Syntax.sigquals = uu____6010;
             FStar_Syntax_Syntax.sigmeta = uu____6011;
             FStar_Syntax_Syntax.sigattrs = uu____6012;
             FStar_Syntax_Syntax.sigopts = uu____6013;_},uu____6014)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____6034 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____6034
        | uu____6035 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6042  -> FStar_Pervasives_Native.None)
        (fun uu____6044  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___22_6077 =
        match uu___22_6077 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____6088);
             FStar_Syntax_Syntax.sigrng = uu____6089;
             FStar_Syntax_Syntax.sigquals = uu____6090;
             FStar_Syntax_Syntax.sigmeta = uu____6091;
             FStar_Syntax_Syntax.sigattrs = uu____6092;
             FStar_Syntax_Syntax.sigopts = uu____6093;_},uu____6094)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____6122 -> FStar_Pervasives_Native.None)
        | uu____6129 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6140  -> FStar_Pervasives_Native.None)
        (fun uu____6144  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____6204 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____6204 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____6229 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____6267) ->
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
      let uu____6325 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____6325 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____6357 = try_lookup_lid env l  in
      match uu____6357 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____6363 =
            let uu____6364 = FStar_Syntax_Subst.compress e  in
            uu____6364.FStar_Syntax_Syntax.n  in
          (match uu____6363 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____6370 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____6382 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____6382 with
      | (uu____6392,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____6413 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____6417 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____6417 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____6422 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___869_6453 = env  in
        {
          curmodule = (uu___869_6453.curmodule);
          curmonad = (uu___869_6453.curmonad);
          modules = (uu___869_6453.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___869_6453.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___869_6453.sigaccum);
          sigmap = (uu___869_6453.sigmap);
          iface = (uu___869_6453.iface);
          admitted_iface = (uu___869_6453.admitted_iface);
          expect_typ = (uu___869_6453.expect_typ);
          remaining_iface_decls = (uu___869_6453.remaining_iface_decls);
          syntax_only = (uu___869_6453.syntax_only);
          ds_hooks = (uu___869_6453.ds_hooks);
          dep_graph = (uu___869_6453.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____6469 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____6469 drop_attributes
  
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
               (uu____6526,uu____6527,uu____6528);
             FStar_Syntax_Syntax.sigrng = uu____6529;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6531;
             FStar_Syntax_Syntax.sigattrs = uu____6532;
             FStar_Syntax_Syntax.sigopts = uu____6533;_},uu____6534)
            ->
            let uu____6543 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___23_6549  ->
                      match uu___23_6549 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6552 -> false))
               in
            if uu____6543
            then
              let uu____6557 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6557
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6560;
             FStar_Syntax_Syntax.sigrng = uu____6561;
             FStar_Syntax_Syntax.sigquals = uu____6562;
             FStar_Syntax_Syntax.sigmeta = uu____6563;
             FStar_Syntax_Syntax.sigattrs = uu____6564;
             FStar_Syntax_Syntax.sigopts = uu____6565;_},uu____6566)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____6594 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____6594
        | uu____6595 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6602  -> FStar_Pervasives_Native.None)
        (fun uu____6604  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___24_6639 =
        match uu___24_6639 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6649,uu____6650,uu____6651,uu____6652,datas,uu____6654);
             FStar_Syntax_Syntax.sigrng = uu____6655;
             FStar_Syntax_Syntax.sigquals = uu____6656;
             FStar_Syntax_Syntax.sigmeta = uu____6657;
             FStar_Syntax_Syntax.sigattrs = uu____6658;
             FStar_Syntax_Syntax.sigopts = uu____6659;_},uu____6660)
            -> FStar_Pervasives_Native.Some datas
        | uu____6679 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6690  -> FStar_Pervasives_Native.None)
        (fun uu____6694  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____6773 =
    let uu____6774 =
      let uu____6779 =
        let uu____6782 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6782  in
      let uu____6816 = FStar_ST.op_Bang record_cache  in uu____6779 ::
        uu____6816
       in
    FStar_ST.op_Colon_Equals record_cache uu____6774  in
  let pop1 uu____6882 =
    let uu____6883 =
      let uu____6888 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6888  in
    FStar_ST.op_Colon_Equals record_cache uu____6883  in
  let snapshot1 uu____6959 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____6983 =
    let uu____6984 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____6984  in
  let insert r =
    let uu____7024 =
      let uu____7029 = let uu____7032 = peek1 ()  in r :: uu____7032  in
      let uu____7035 =
        let uu____7040 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____7040  in
      uu____7029 :: uu____7035  in
    FStar_ST.op_Colon_Equals record_cache uu____7024  in
  let filter1 uu____7108 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____7117 =
      let uu____7122 =
        let uu____7127 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____7127  in
      filtered :: uu____7122  in
    FStar_ST.op_Colon_Equals record_cache uu____7117  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____8053) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___25_8072  ->
                   match uu___25_8072 with
                   | FStar_Syntax_Syntax.RecordType uu____8074 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____8084 -> true
                   | uu____8094 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___26_8120  ->
                      match uu___26_8120 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____8123,uu____8124,uu____8125,uu____8126,uu____8127);
                          FStar_Syntax_Syntax.sigrng = uu____8128;
                          FStar_Syntax_Syntax.sigquals = uu____8129;
                          FStar_Syntax_Syntax.sigmeta = uu____8130;
                          FStar_Syntax_Syntax.sigattrs = uu____8131;
                          FStar_Syntax_Syntax.sigopts = uu____8132;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____8145 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___27_8183  ->
                    match uu___27_8183 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____8187,uu____8188,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____8190;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____8192;
                        FStar_Syntax_Syntax.sigattrs = uu____8193;
                        FStar_Syntax_Syntax.sigopts = uu____8194;_} ->
                        let uu____8207 =
                          let uu____8208 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____8208  in
                        (match uu____8207 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____8214,t,uu____8216,uu____8217,uu____8218);
                             FStar_Syntax_Syntax.sigrng = uu____8219;
                             FStar_Syntax_Syntax.sigquals = uu____8220;
                             FStar_Syntax_Syntax.sigmeta = uu____8221;
                             FStar_Syntax_Syntax.sigattrs = uu____8222;
                             FStar_Syntax_Syntax.sigopts = uu____8223;_} ->
                             let uu____8236 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____8236 with
                              | (formals,uu____8252) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____8306  ->
                                            match uu____8306 with
                                            | (x,q) ->
                                                let uu____8319 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____8319
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____8374  ->
                                            match uu____8374 with
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
                                  ((let uu____8398 =
                                      let uu____8401 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____8401  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____8398);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____8460 =
                                            match uu____8460 with
                                            | (id1,uu____8466) ->
                                                let modul =
                                                  let uu____8469 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____8469.FStar_Ident.str
                                                   in
                                                let uu____8470 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____8470 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____8493 =
                                                         let uu____8494 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8494
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8493);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8539 =
                                                               let uu____8540
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8540.FStar_Ident.ident
                                                                in
                                                             uu____8539.FStar_Ident.idText
                                                              in
                                                           let uu____8542 =
                                                             let uu____8543 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8543
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8542))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8595 -> ())
                    | uu____8596 -> ()))
        | uu____8597 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8619 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8619 with
        | (ns,id1) ->
            let uu____8636 = peek_record_cache ()  in
            FStar_Util.find_map uu____8636
              (fun record  ->
                 let uu____8642 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8648  -> FStar_Pervasives_Native.None)
                   uu____8642)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8650  -> Cont_ignore) (fun uu____8652  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8658 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8658)
        (fun k  -> fun uu____8664  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____8680 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8680 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8686 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____8706 = try_lookup_record_by_field_name env lid  in
        match uu____8706 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8711 =
              let uu____8713 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8713  in
            let uu____8714 =
              let uu____8716 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8716  in
            uu____8711 = uu____8714 ->
            let uu____8718 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8722  -> Cont_ok ())
               in
            (match uu____8718 with
             | Cont_ok uu____8724 -> true
             | uu____8726 -> false)
        | uu____8730 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____8752 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____8752 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8763 =
            let uu____8769 =
              let uu____8770 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8771 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8770 uu____8771  in
            (uu____8769, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8763
      | uu____8778 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8796  ->
    let uu____8797 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8797
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8818  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___28_8831  ->
      match uu___28_8831 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___29_8869 =
            match uu___29_8869 with
            | Rec_binding uu____8871 -> true
            | uu____8873 -> false  in
          let this_env =
            let uu___1099_8876 = env  in
            let uu____8877 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1099_8876.curmodule);
              curmonad = (uu___1099_8876.curmonad);
              modules = (uu___1099_8876.modules);
              scope_mods = uu____8877;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1099_8876.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1099_8876.sigaccum);
              sigmap = (uu___1099_8876.sigmap);
              iface = (uu___1099_8876.iface);
              admitted_iface = (uu___1099_8876.admitted_iface);
              expect_typ = (uu___1099_8876.expect_typ);
              remaining_iface_decls = (uu___1099_8876.remaining_iface_decls);
              syntax_only = (uu___1099_8876.syntax_only);
              ds_hooks = (uu___1099_8876.ds_hooks);
              dep_graph = (uu___1099_8876.dep_graph)
            }  in
          let uu____8880 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8880 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____8897 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1107_8922 = env  in
      {
        curmodule = (uu___1107_8922.curmodule);
        curmonad = (uu___1107_8922.curmonad);
        modules = (uu___1107_8922.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1107_8922.exported_ids);
        trans_exported_ids = (uu___1107_8922.trans_exported_ids);
        includes = (uu___1107_8922.includes);
        sigaccum = (uu___1107_8922.sigaccum);
        sigmap = (uu___1107_8922.sigmap);
        iface = (uu___1107_8922.iface);
        admitted_iface = (uu___1107_8922.admitted_iface);
        expect_typ = (uu___1107_8922.expect_typ);
        remaining_iface_decls = (uu___1107_8922.remaining_iface_decls);
        syntax_only = (uu___1107_8922.syntax_only);
        ds_hooks = (uu___1107_8922.ds_hooks);
        dep_graph = (uu___1107_8922.dep_graph)
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
      let uu____8962 = push_bv' env x  in
      match uu____8962 with | (env1,bv,uu____8975) -> (env1, bv)
  
let (push_top_level_rec_binding :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.delta_depth -> (env * Prims.bool FStar_ST.ref))
  =
  fun env0  ->
    fun x  ->
      fun dd  ->
        let l = qualify env0 x  in
        let uu____9007 =
          (unique false true env0 l) || (FStar_Options.interactive ())  in
        if uu____9007
        then
          let used_marker = FStar_Util.mk_ref false  in
          ((push_scope_mod env0 (Rec_binding (x, l, dd, used_marker))),
            used_marker)
        else
          (let uu____9030 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____9030)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____9081) ->
                let uu____9089 =
                  let uu____9092 = FStar_Syntax_Util.lids_of_sigelt se  in
                  FStar_Util.find_opt (FStar_Ident.lid_equals l) uu____9092
                   in
                (match uu____9089 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____9097 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____9097
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____9106 =
            let uu____9112 =
              let uu____9114 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____9114 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____9112)  in
          let uu____9118 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____9106 uu____9118  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____9127 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____9140 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____9151 -> (false, true)
            | uu____9164 -> (false, false)  in
          match uu____9127 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____9178 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____9184 =
                       let uu____9186 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____9186  in
                     if uu____9184
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____9178 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____9194 ->
                   (extract_record env globals s;
                    (let uu___1156_9198 = env  in
                     {
                       curmodule = (uu___1156_9198.curmodule);
                       curmonad = (uu___1156_9198.curmonad);
                       modules = (uu___1156_9198.modules);
                       scope_mods = (uu___1156_9198.scope_mods);
                       exported_ids = (uu___1156_9198.exported_ids);
                       trans_exported_ids =
                         (uu___1156_9198.trans_exported_ids);
                       includes = (uu___1156_9198.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1156_9198.sigmap);
                       iface = (uu___1156_9198.iface);
                       admitted_iface = (uu___1156_9198.admitted_iface);
                       expect_typ = (uu___1156_9198.expect_typ);
                       remaining_iface_decls =
                         (uu___1156_9198.remaining_iface_decls);
                       syntax_only = (uu___1156_9198.syntax_only);
                       ds_hooks = (uu___1156_9198.ds_hooks);
                       dep_graph = (uu___1156_9198.dep_graph)
                     })))
           in
        let env2 =
          let uu___1159_9200 = env1  in
          let uu____9201 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1159_9200.curmodule);
            curmonad = (uu___1159_9200.curmonad);
            modules = (uu___1159_9200.modules);
            scope_mods = uu____9201;
            exported_ids = (uu___1159_9200.exported_ids);
            trans_exported_ids = (uu___1159_9200.trans_exported_ids);
            includes = (uu___1159_9200.includes);
            sigaccum = (uu___1159_9200.sigaccum);
            sigmap = (uu___1159_9200.sigmap);
            iface = (uu___1159_9200.iface);
            admitted_iface = (uu___1159_9200.admitted_iface);
            expect_typ = (uu___1159_9200.expect_typ);
            remaining_iface_decls = (uu___1159_9200.remaining_iface_decls);
            syntax_only = (uu___1159_9200.syntax_only);
            ds_hooks = (uu___1159_9200.ds_hooks);
            dep_graph = (uu___1159_9200.dep_graph)
          }  in
        let uu____9227 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9253) ->
              let uu____9262 =
                FStar_List.map
                  (fun se  ->
                     let uu____9280 = FStar_Syntax_Util.lids_of_sigelt se  in
                     (uu____9280, se)) ses
                 in
              (env2, uu____9262)
          | uu____9293 ->
              let uu____9294 =
                let uu____9303 =
                  let uu____9310 = FStar_Syntax_Util.lids_of_sigelt s  in
                  (uu____9310, s)  in
                [uu____9303]  in
              (env2, uu____9294)
           in
        match uu____9227 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____9371  ->
                     match uu____9371 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____9393 =
                                    let uu____9396 = FStar_ST.op_Bang globals
                                       in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____9396
                                     in
                                  FStar_ST.op_Colon_Equals globals uu____9393);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____9447 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____9447.FStar_Ident.str  in
                                      ((let uu____9449 =
                                          get_exported_id_set env3 modul  in
                                        match uu____9449 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____9471 =
                                              let uu____9472 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____9472
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____9471
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
                let uu___1184_9529 = env3  in
                let uu____9530 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1184_9529.curmodule);
                  curmonad = (uu___1184_9529.curmonad);
                  modules = (uu___1184_9529.modules);
                  scope_mods = uu____9530;
                  exported_ids = (uu___1184_9529.exported_ids);
                  trans_exported_ids = (uu___1184_9529.trans_exported_ids);
                  includes = (uu___1184_9529.includes);
                  sigaccum = (uu___1184_9529.sigaccum);
                  sigmap = (uu___1184_9529.sigmap);
                  iface = (uu___1184_9529.iface);
                  admitted_iface = (uu___1184_9529.admitted_iface);
                  expect_typ = (uu___1184_9529.expect_typ);
                  remaining_iface_decls =
                    (uu___1184_9529.remaining_iface_decls);
                  syntax_only = (uu___1184_9529.syntax_only);
                  ds_hooks = (uu___1184_9529.ds_hooks);
                  dep_graph = (uu___1184_9529.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____9591 =
        let uu____9596 = resolve_module_name env ns false  in
        match uu____9596 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____9611 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9629  ->
                      match uu____9629 with
                      | (m,uu____9636) ->
                          let uu____9637 =
                            let uu____9639 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____9639 "."  in
                          let uu____9642 =
                            let uu____9644 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____9644 "."  in
                          FStar_Util.starts_with uu____9637 uu____9642))
               in
            if uu____9611
            then (ns, Open_namespace)
            else
              (let uu____9654 =
                 let uu____9660 =
                   let uu____9662 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9662
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9660)  in
               let uu____9666 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9654 uu____9666)
        | FStar_Pervasives_Native.Some ns' -> (ns', Open_module)  in
      match uu____9591 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9687 = resolve_module_name env ns false  in
      match uu____9687 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9696 = current_module env1  in
              uu____9696.FStar_Ident.str  in
            (let uu____9698 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____9698 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9722 =
                   let uu____9725 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9725
                    in
                 FStar_ST.op_Colon_Equals incl uu____9722);
            (match () with
             | () ->
                 let uu____9774 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____9774 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9794 =
                          let uu____9891 = get_exported_id_set env1 curmod
                             in
                          let uu____9938 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____9891, uu____9938)  in
                        match uu____9794 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10354 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10354  in
                              let ex = cur_exports k  in
                              (let uu____10455 =
                                 let uu____10459 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____10459 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____10455);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____10551 =
                                     let uu____10555 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____10555 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10551)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10604 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____10706 =
                        let uu____10712 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10712)
                         in
                      let uu____10716 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____10706 uu____10716))))
      | uu____10717 ->
          let uu____10720 =
            let uu____10726 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____10726)  in
          let uu____10730 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____10720 uu____10730
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____10747 = module_is_defined env l  in
        if uu____10747
        then
          ((env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____10753 =
             let uu____10759 =
               let uu____10761 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____10761  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____10759)  in
           let uu____10765 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____10753 uu____10765)
  
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
                      let uu____10808 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____10808 ->
                      let uu____10813 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____10813 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____10828;
                              FStar_Syntax_Syntax.sigrng = uu____10829;
                              FStar_Syntax_Syntax.sigquals = uu____10830;
                              FStar_Syntax_Syntax.sigmeta = uu____10831;
                              FStar_Syntax_Syntax.sigattrs = uu____10832;
                              FStar_Syntax_Syntax.sigopts = uu____10833;_},uu____10834)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____10854;
                              FStar_Syntax_Syntax.sigrng = uu____10855;
                              FStar_Syntax_Syntax.sigquals = uu____10856;
                              FStar_Syntax_Syntax.sigmeta = uu____10857;
                              FStar_Syntax_Syntax.sigattrs = uu____10858;
                              FStar_Syntax_Syntax.sigopts = uu____10859;_},uu____10860)
                           -> lids
                       | uu____10890 ->
                           ((let uu____10899 =
                               let uu____10901 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____10901  in
                             if uu____10899
                             then
                               let uu____10904 = FStar_Ident.range_of_lid l
                                  in
                               let uu____10905 =
                                 let uu____10911 =
                                   let uu____10913 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____10913
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____10911)
                                  in
                               FStar_Errors.log_issue uu____10904 uu____10905
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1275_10930 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1275_10930.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1275_10930.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1275_10930.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1275_10930.FStar_Syntax_Syntax.sigattrs);
                                   FStar_Syntax_Syntax.sigopts =
                                     (uu___1275_10930.FStar_Syntax_Syntax.sigopts)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____10932 -> lids) [])
         in
      let uu___1280_10933 = m  in
      let uu____10934 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____10944,uu____10945) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1289_10948 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1289_10948.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1289_10948.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1289_10948.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1289_10948.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1289_10948.FStar_Syntax_Syntax.sigopts)
                    }
                | uu____10949 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1280_10933.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____10934;
        FStar_Syntax_Syntax.exports =
          (uu___1280_10933.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1280_10933.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10973) ->
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
                                (lid,uu____10994,uu____10995,uu____10996,uu____10997,uu____10998)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____11014,uu____11015)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11032 =
                                        let uu____11039 =
                                          let uu____11040 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____11041 =
                                            let uu____11048 =
                                              let uu____11049 =
                                                let uu____11064 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11064)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11049
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11048
                                             in
                                          uu____11041
                                            FStar_Pervasives_Native.None
                                            uu____11040
                                           in
                                        (lid, univ_names, uu____11039)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11032
                                       in
                                    let se2 =
                                      let uu___1321_11078 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1321_11078.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1321_11078.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1321_11078.FStar_Syntax_Syntax.sigattrs);
                                        FStar_Syntax_Syntax.sigopts =
                                          (uu___1321_11078.FStar_Syntax_Syntax.sigopts)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11088 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11092,uu____11093) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11102,lbs),uu____11104)
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
                             let uu____11122 =
                               let uu____11124 =
                                 let uu____11125 =
                                   let uu____11128 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11128.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11125.FStar_Syntax_Syntax.v  in
                               uu____11124.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____11122))
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
                               let uu____11145 =
                                 let uu____11148 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11148.FStar_Syntax_Syntax.fv_name  in
                               uu____11145.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1344_11153 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1344_11153.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1344_11153.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1344_11153.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___1344_11153.FStar_Syntax_Syntax.sigopts)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11163 -> ()));
      (let curmod =
         let uu____11166 = current_module env  in uu____11166.FStar_Ident.str
          in
       (let uu____11168 =
          let uu____11265 = get_exported_id_set env curmod  in
          let uu____11312 = get_trans_exported_id_set env curmod  in
          (uu____11265, uu____11312)  in
        match uu____11168 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____11731 = cur_ex eikind  in
                FStar_ST.op_Bang uu____11731  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____11837 =
                let uu____11841 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____11841  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____11837  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____11890 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1362_11988 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1362_11988.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1362_11988.exported_ids);
                    trans_exported_ids = (uu___1362_11988.trans_exported_ids);
                    includes = (uu___1362_11988.includes);
                    sigaccum = [];
                    sigmap = (uu___1362_11988.sigmap);
                    iface = (uu___1362_11988.iface);
                    admitted_iface = (uu___1362_11988.admitted_iface);
                    expect_typ = (uu___1362_11988.expect_typ);
                    remaining_iface_decls =
                      (uu___1362_11988.remaining_iface_decls);
                    syntax_only = (uu___1362_11988.syntax_only);
                    ds_hooks = (uu___1362_11988.ds_hooks);
                    dep_graph = (uu___1362_11988.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____12014  ->
         push_record_cache ();
         (let uu____12017 =
            let uu____12020 = FStar_ST.op_Bang stack  in env :: uu____12020
             in
          FStar_ST.op_Colon_Equals stack uu____12017);
         (let uu___1368_12069 = env  in
          let uu____12070 = FStar_Util.smap_copy env.exported_ids  in
          let uu____12075 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____12080 = FStar_Util.smap_copy env.includes  in
          let uu____12091 = FStar_Util.smap_copy env.sigmap  in
          {
            curmodule = (uu___1368_12069.curmodule);
            curmonad = (uu___1368_12069.curmonad);
            modules = (uu___1368_12069.modules);
            scope_mods = (uu___1368_12069.scope_mods);
            exported_ids = uu____12070;
            trans_exported_ids = uu____12075;
            includes = uu____12080;
            sigaccum = (uu___1368_12069.sigaccum);
            sigmap = uu____12091;
            iface = (uu___1368_12069.iface);
            admitted_iface = (uu___1368_12069.admitted_iface);
            expect_typ = (uu___1368_12069.expect_typ);
            remaining_iface_decls = (uu___1368_12069.remaining_iface_decls);
            syntax_only = (uu___1368_12069.syntax_only);
            ds_hooks = (uu___1368_12069.ds_hooks);
            dep_graph = (uu___1368_12069.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____12109  ->
    FStar_Util.atomically
      (fun uu____12116  ->
         let uu____12117 = FStar_ST.op_Bang stack  in
         match uu____12117 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____12172 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        let uu____12217 = FStar_Syntax_Util.lids_of_sigelt se  in
        match uu____12217 with
        | l::uu____12222 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____12226 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____12268 = FStar_Util.smap_try_find sm' k  in
              match uu____12268 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1403_12299 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1403_12299.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1403_12299.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1403_12299.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1403_12299.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___1403_12299.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____12300 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12308 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____12335 = finish env modul1  in (uu____12335, modul1)
  
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
      let uu____12404 =
        let uu____12408 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____12408  in
      FStar_Util.set_elements uu____12404  in
    let fields =
      let uu____12471 =
        let uu____12475 = e Exported_id_field  in
        FStar_ST.op_Bang uu____12475  in
      FStar_Util.set_elements uu____12471  in
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
          let uu____12567 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____12567  in
        let fields =
          let uu____12581 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____12581  in
        (fun uu___30_12589  ->
           match uu___30_12589 with
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
  'uu____12693 .
    'uu____12693 Prims.list FStar_Pervasives_Native.option ->
      'uu____12693 Prims.list FStar_ST.ref
  =
  fun uu___31_12706  ->
    match uu___31_12706 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____12749 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____12749 as_exported_ids  in
      let uu____12755 = as_ids_opt env.exported_ids  in
      let uu____12758 = as_ids_opt env.trans_exported_ids  in
      let uu____12761 =
        let uu____12766 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____12766 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____12755;
        mii_trans_exported_ids = uu____12758;
        mii_includes = uu____12761
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
                let uu____12855 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____12855 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___32_12877 =
                  match uu___32_12877 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____12889  ->
                     match uu____12889 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if (FStar_List.length mname.FStar_Ident.ns) > Prims.int_zero
                then
                  let uu____12915 =
                    let uu____12920 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____12920, Open_namespace)  in
                  [uu____12915]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____12951 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____12951);
              (match () with
               | () ->
                   ((let uu____12956 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____12956);
                    (match () with
                     | () ->
                         ((let uu____12961 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____12961);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1473_12971 = env1  in
                                 let uu____12972 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1473_12971.curmonad);
                                   modules = (uu___1473_12971.modules);
                                   scope_mods = uu____12972;
                                   exported_ids =
                                     (uu___1473_12971.exported_ids);
                                   trans_exported_ids =
                                     (uu___1473_12971.trans_exported_ids);
                                   includes = (uu___1473_12971.includes);
                                   sigaccum = (uu___1473_12971.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1473_12971.expect_typ);
                                   remaining_iface_decls =
                                     (uu___1473_12971.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1473_12971.syntax_only);
                                   ds_hooks = (uu___1473_12971.ds_hooks);
                                   dep_graph = (uu___1473_12971.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____12984 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____13010  ->
                      match uu____13010 with
                      | (l,uu____13017) -> FStar_Ident.lid_equals l mname))
               in
            match uu____12984 with
            | FStar_Pervasives_Native.None  ->
                let uu____13027 = prep env  in (uu____13027, false)
            | FStar_Pervasives_Native.Some (uu____13030,m) ->
                ((let uu____13037 =
                    (let uu____13041 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____13041) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____13037
                  then
                    let uu____13044 =
                      let uu____13050 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13050)
                       in
                    let uu____13054 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____13044 uu____13054
                  else ());
                 (let uu____13057 =
                    let uu____13058 = push env  in prep uu____13058  in
                  (uu____13057, true)))
  
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
          let uu___1494_13076 = env  in
          {
            curmodule = (uu___1494_13076.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1494_13076.modules);
            scope_mods = (uu___1494_13076.scope_mods);
            exported_ids = (uu___1494_13076.exported_ids);
            trans_exported_ids = (uu___1494_13076.trans_exported_ids);
            includes = (uu___1494_13076.includes);
            sigaccum = (uu___1494_13076.sigaccum);
            sigmap = (uu___1494_13076.sigmap);
            iface = (uu___1494_13076.iface);
            admitted_iface = (uu___1494_13076.admitted_iface);
            expect_typ = (uu___1494_13076.expect_typ);
            remaining_iface_decls = (uu___1494_13076.remaining_iface_decls);
            syntax_only = (uu___1494_13076.syntax_only);
            ds_hooks = (uu___1494_13076.ds_hooks);
            dep_graph = (uu___1494_13076.dep_graph)
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
        let uu____13111 = lookup1 lid  in
        match uu____13111 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____13126  ->
                   match uu____13126 with
                   | (lid1,uu____13133) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____13136 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13136  in
            let msg1 =
              if (FStar_List.length lid.FStar_Ident.ns) = Prims.int_zero
              then msg
              else
                (let modul =
                   let uu____13148 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____13149 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____13148 uu____13149  in
                 let uu____13150 = resolve_module_name env modul true  in
                 match uu____13150 with
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
            let uu____13171 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13171
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____13201 = lookup1 id1  in
      match uu____13201 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  