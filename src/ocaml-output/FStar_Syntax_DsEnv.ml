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
    match projectee with | Local_binding _0 -> true | uu____362 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____381 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____400 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____419 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____438 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____457 -> false
  
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
    | uu____478 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____489 -> false
  
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
    ds_push_open_hook = (fun uu____2060  -> fun uu____2061  -> ());
    ds_push_include_hook = (fun uu____2064  -> fun uu____2065  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____2069  -> fun uu____2070  -> fun uu____2071  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____2108 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____2149 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env1  ->
    fun b  ->
      let uu___126_2183 = env1  in
      {
        curmodule = (uu___126_2183.curmodule);
        curmonad = (uu___126_2183.curmonad);
        modules = (uu___126_2183.modules);
        scope_mods = (uu___126_2183.scope_mods);
        exported_ids = (uu___126_2183.exported_ids);
        trans_exported_ids = (uu___126_2183.trans_exported_ids);
        includes = (uu___126_2183.includes);
        sigaccum = (uu___126_2183.sigaccum);
        sigmap = (uu___126_2183.sigmap);
        iface = b;
        admitted_iface = (uu___126_2183.admitted_iface);
        expect_typ = (uu___126_2183.expect_typ);
        remaining_iface_decls = (uu___126_2183.remaining_iface_decls);
        syntax_only = (uu___126_2183.syntax_only);
        ds_hooks = (uu___126_2183.ds_hooks);
        dep_graph = (uu___126_2183.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___131_2204 = e  in
      {
        curmodule = (uu___131_2204.curmodule);
        curmonad = (uu___131_2204.curmonad);
        modules = (uu___131_2204.modules);
        scope_mods = (uu___131_2204.scope_mods);
        exported_ids = (uu___131_2204.exported_ids);
        trans_exported_ids = (uu___131_2204.trans_exported_ids);
        includes = (uu___131_2204.includes);
        sigaccum = (uu___131_2204.sigaccum);
        sigmap = (uu___131_2204.sigmap);
        iface = (uu___131_2204.iface);
        admitted_iface = b;
        expect_typ = (uu___131_2204.expect_typ);
        remaining_iface_decls = (uu___131_2204.remaining_iface_decls);
        syntax_only = (uu___131_2204.syntax_only);
        ds_hooks = (uu___131_2204.ds_hooks);
        dep_graph = (uu___131_2204.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___136_2225 = e  in
      {
        curmodule = (uu___136_2225.curmodule);
        curmonad = (uu___136_2225.curmonad);
        modules = (uu___136_2225.modules);
        scope_mods = (uu___136_2225.scope_mods);
        exported_ids = (uu___136_2225.exported_ids);
        trans_exported_ids = (uu___136_2225.trans_exported_ids);
        includes = (uu___136_2225.includes);
        sigaccum = (uu___136_2225.sigaccum);
        sigmap = (uu___136_2225.sigmap);
        iface = (uu___136_2225.iface);
        admitted_iface = (uu___136_2225.admitted_iface);
        expect_typ = b;
        remaining_iface_decls = (uu___136_2225.remaining_iface_decls);
        syntax_only = (uu___136_2225.syntax_only);
        ds_hooks = (uu___136_2225.ds_hooks);
        dep_graph = (uu___136_2225.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env1  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____2252 =
        FStar_Util.smap_try_find env1.trans_exported_ids module_name  in
      match uu____2252 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set1 ->
          let uu____2265 =
            let uu____2269 = exported_id_set1 Exported_id_term_type  in
            FStar_ST.op_Bang uu____2269  in
          FStar_All.pipe_right uu____2265 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env1  ->
    FStar_List.filter_map
      (fun uu___0_2357  ->
         match uu___0_2357 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2362 -> FStar_Pervasives_Native.None) env1.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___155_2374 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___155_2374.curmonad);
        modules = (uu___155_2374.modules);
        scope_mods = (uu___155_2374.scope_mods);
        exported_ids = (uu___155_2374.exported_ids);
        trans_exported_ids = (uu___155_2374.trans_exported_ids);
        includes = (uu___155_2374.includes);
        sigaccum = (uu___155_2374.sigaccum);
        sigmap = (uu___155_2374.sigmap);
        iface = (uu___155_2374.iface);
        admitted_iface = (uu___155_2374.admitted_iface);
        expect_typ = (uu___155_2374.expect_typ);
        remaining_iface_decls = (uu___155_2374.remaining_iface_decls);
        syntax_only = (uu___155_2374.syntax_only);
        ds_hooks = (uu___155_2374.ds_hooks);
        dep_graph = (uu___155_2374.dep_graph)
      }
  
let (current_module : env -> FStar_Ident.lident) =
  fun env1  ->
    match env1.curmodule with
    | FStar_Pervasives_Native.None  -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
  
let (iface_decls :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____2398 =
        FStar_All.pipe_right env1.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2432  ->
                match uu____2432 with
                | (m,uu____2441) -> FStar_Ident.lid_equals l m))
         in
      match uu____2398 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2458,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env1  ->
    fun l  ->
      fun ds  ->
        let uu____2492 =
          FStar_List.partition
            (fun uu____2522  ->
               match uu____2522 with
               | (m,uu____2531) -> FStar_Ident.lid_equals l m)
            env1.remaining_iface_decls
           in
        match uu____2492 with
        | (uu____2536,rest) ->
            let uu___180_2570 = env1  in
            {
              curmodule = (uu___180_2570.curmodule);
              curmonad = (uu___180_2570.curmonad);
              modules = (uu___180_2570.modules);
              scope_mods = (uu___180_2570.scope_mods);
              exported_ids = (uu___180_2570.exported_ids);
              trans_exported_ids = (uu___180_2570.trans_exported_ids);
              includes = (uu___180_2570.includes);
              sigaccum = (uu___180_2570.sigaccum);
              sigmap = (uu___180_2570.sigmap);
              iface = (uu___180_2570.iface);
              admitted_iface = (uu___180_2570.admitted_iface);
              expect_typ = (uu___180_2570.expect_typ);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___180_2570.syntax_only);
              ds_hooks = (uu___180_2570.ds_hooks);
              dep_graph = (uu___180_2570.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Ident.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env1  ->
    fun id  ->
      match env1.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2599 = current_module env1  in qual uu____2599 id
      | FStar_Pervasives_Native.Some monad ->
          let uu____2601 =
            let uu____2602 = current_module env1  in qual uu____2602 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2601 id
  
let (syntax_only : env -> Prims.bool) = fun env1  -> env1.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env1  ->
    fun b  ->
      let uu___190_2623 = env1  in
      {
        curmodule = (uu___190_2623.curmodule);
        curmonad = (uu___190_2623.curmonad);
        modules = (uu___190_2623.modules);
        scope_mods = (uu___190_2623.scope_mods);
        exported_ids = (uu___190_2623.exported_ids);
        trans_exported_ids = (uu___190_2623.trans_exported_ids);
        includes = (uu___190_2623.includes);
        sigaccum = (uu___190_2623.sigaccum);
        sigmap = (uu___190_2623.sigmap);
        iface = (uu___190_2623.iface);
        admitted_iface = (uu___190_2623.admitted_iface);
        expect_typ = (uu___190_2623.expect_typ);
        remaining_iface_decls = (uu___190_2623.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___190_2623.ds_hooks);
        dep_graph = (uu___190_2623.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env1  -> env1.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env1  ->
    fun hooks  ->
      let uu___195_2641 = env1  in
      {
        curmodule = (uu___195_2641.curmodule);
        curmonad = (uu___195_2641.curmonad);
        modules = (uu___195_2641.modules);
        scope_mods = (uu___195_2641.scope_mods);
        exported_ids = (uu___195_2641.exported_ids);
        trans_exported_ids = (uu___195_2641.trans_exported_ids);
        includes = (uu___195_2641.includes);
        sigaccum = (uu___195_2641.sigaccum);
        sigmap = (uu___195_2641.sigmap);
        iface = (uu___195_2641.iface);
        admitted_iface = (uu___195_2641.admitted_iface);
        expect_typ = (uu___195_2641.expect_typ);
        remaining_iface_decls = (uu___195_2641.remaining_iface_decls);
        syntax_only = (uu___195_2641.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___195_2641.dep_graph)
      }
  
let new_sigmap : 'uuuuuu2647 . unit -> 'uuuuuu2647 FStar_Util.smap =
  fun uu____2654  -> FStar_Util.smap_create (Prims.of_int (100)) 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____2662 = new_sigmap ()  in
    let uu____2667 = new_sigmap ()  in
    let uu____2672 = new_sigmap ()  in
    let uu____2683 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2662;
      trans_exported_ids = uu____2667;
      includes = uu____2672;
      sigaccum = [];
      sigmap = uu____2683;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env1  -> env1.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env1  ->
    fun ds  ->
      let uu___202_2727 = env1  in
      {
        curmodule = (uu___202_2727.curmodule);
        curmonad = (uu___202_2727.curmonad);
        modules = (uu___202_2727.modules);
        scope_mods = (uu___202_2727.scope_mods);
        exported_ids = (uu___202_2727.exported_ids);
        trans_exported_ids = (uu___202_2727.trans_exported_ids);
        includes = (uu___202_2727.includes);
        sigaccum = (uu___202_2727.sigaccum);
        sigmap = (uu___202_2727.sigmap);
        iface = (uu___202_2727.iface);
        admitted_iface = (uu___202_2727.admitted_iface);
        expect_typ = (uu___202_2727.expect_typ);
        remaining_iface_decls = (uu___202_2727.remaining_iface_decls);
        syntax_only = (uu___202_2727.syntax_only);
        ds_hooks = (uu___202_2727.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env1  -> env1.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env1  ->
    FStar_List.existsb
      (fun uu____2755  ->
         match uu____2755 with
         | (m,uu____2762) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
      env1.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id = FStar_Ident.set_id_range r bv.FStar_Syntax_Syntax.ppname  in
      let uu___212_2775 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___212_2775.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___212_2775.FStar_Syntax_Syntax.sort)
      }
  
let (bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun bv  ->
    fun r  ->
      let uu____2787 = set_bv_range bv r  in
      FStar_Syntax_Syntax.bv_to_name uu____2787
  
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
  fun id  ->
    FStar_Util.find_map unmangleMap
      (fun uu____2880  ->
         match uu____2880 with
         | (x,y,dd,dq) ->
             let uu____2907 =
               let uu____2909 = FStar_Ident.text_of_id id  in uu____2909 = x
                in
             if uu____2907
             then
               let uu____2915 =
                 let uu____2916 =
                   let uu____2917 = FStar_Ident.range_of_id id  in
                   FStar_Ident.lid_of_path ["Prims"; y] uu____2917  in
                 FStar_Syntax_Syntax.fvar uu____2916 dd dq  in
               FStar_Pervasives_Native.Some uu____2915
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____2957 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2994 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____3015 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___1_3045  ->
      match uu___1_3045 with
      | Cont_ok a1 -> FStar_Pervasives_Native.Some a1
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'uuuuuu3064 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'uuuuuu3064 cont_t) -> 'uuuuuu3064 cont_t
  =
  fun ns  ->
    fun id  ->
      fun record  ->
        fun cont  ->
          let typename' =
            let uu____3101 =
              let uu____3102 =
                let uu____3105 = FStar_Ident.ident_of_lid record.typename  in
                [uu____3105]  in
              FStar_List.append ns uu____3102  in
            FStar_Ident.lid_of_ids uu____3101  in
          let uu____3106 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____3106
          then
            let fname =
              let uu____3112 =
                let uu____3113 = FStar_Ident.ns_of_lid record.typename  in
                FStar_List.append uu____3113 [id]  in
              FStar_Ident.lid_of_ids uu____3112  in
            let find =
              FStar_Util.find_map record.fields
                (fun uu____3127  ->
                   match uu____3127 with
                   | (f,uu____3135) ->
                       let uu____3136 =
                         let uu____3138 = FStar_Ident.text_of_id id  in
                         let uu____3140 = FStar_Ident.text_of_id f  in
                         uu____3138 = uu____3140  in
                       if uu____3136
                       then FStar_Pervasives_Native.Some record
                       else FStar_Pervasives_Native.None)
               in
            match find with
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
  fun uu___2_3215  ->
    match uu___2_3215 with
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
        fun env1  ->
          fun ns  ->
            fun id  ->
              let idstr = FStar_Ident.text_of_id id  in
              let rec aux uu___3_3291 =
                match uu___3_3291 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = FStar_Ident.string_of_lid modul  in
                    let not_shadowed =
                      let uu____3304 = get_exported_id_set env1 mname  in
                      match uu____3304 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____3331 = mex eikind  in
                            FStar_ST.op_Bang uu____3331  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____3393 =
                        FStar_Util.smap_try_find env1.includes mname  in
                      match uu____3393 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3448 = qual modul id  in
                        find_in_module uu____3448
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3453 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___4_3462  ->
    match uu___4_3462 with | Exported_id_field  -> true | uu____3465 -> false
  
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
  fun env1  ->
    fun id  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun find_in_module  ->
                fun lookup_default_id  ->
                  let check_local_binding_id uu___5_3589 =
                    match uu___5_3589 with
                    | (id',uu____3592,uu____3593) ->
                        let uu____3594 = FStar_Ident.text_of_id id'  in
                        let uu____3596 = FStar_Ident.text_of_id id  in
                        uu____3594 = uu____3596
                     in
                  let check_rec_binding_id uu___6_3605 =
                    match uu___6_3605 with
                    | (id',uu____3608,uu____3609,uu____3610) ->
                        let uu____3611 = FStar_Ident.text_of_id id'  in
                        let uu____3613 = FStar_Ident.text_of_id id  in
                        uu____3611 = uu____3613
                     in
                  let curmod_ns =
                    let uu____3617 = current_module env1  in
                    FStar_Ident.ids_of_lid uu____3617  in
                  let proc uu___7_3625 =
                    match uu___7_3625 with
                    | Local_binding l when check_local_binding_id l ->
                        let uu____3629 = l  in
                        (match uu____3629 with
                         | (uu____3632,uu____3633,used_marker1) ->
                             (FStar_ST.op_Colon_Equals used_marker1 true;
                              k_local_binding l))
                    | Rec_binding r when check_rec_binding_id r ->
                        let uu____3659 = r  in
                        (match uu____3659 with
                         | (uu____3662,uu____3663,uu____3664,used_marker1) ->
                             (FStar_ST.op_Colon_Equals used_marker1 true;
                              k_rec_binding r))
                    | Open_module_or_namespace (ns,Open_module ) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env1 ns id
                    | Top_level_def id' when
                        let uu____3691 = FStar_Ident.text_of_id id'  in
                        let uu____3693 = FStar_Ident.text_of_id id  in
                        uu____3691 = uu____3693 ->
                        lookup_default_id Cont_ignore id
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____3697 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id1 = FStar_Ident.ident_of_lid lid  in
                             let uu____3703 = FStar_Ident.ns_of_lid lid  in
                             find_in_record uu____3703 id1 r k_record)
                          Cont_ignore env1 uu____3697 id
                    | uu____3706 -> Cont_ignore  in
                  let rec aux uu___8_3716 =
                    match uu___8_3716 with
                    | a1::q ->
                        let uu____3725 = proc a1  in
                        option_of_cont (fun uu____3729  -> aux q) uu____3725
                    | [] ->
                        let uu____3730 = lookup_default_id Cont_fail id  in
                        option_of_cont
                          (fun uu____3734  -> FStar_Pervasives_Native.None)
                          uu____3730
                     in
                  aux env1.scope_mods
  
let found_local_binding :
  'uuuuuu3744 'uuuuuu3745 .
    FStar_Range.range ->
      ('uuuuuu3744 * FStar_Syntax_Syntax.bv * 'uuuuuu3745) ->
        FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____3761  ->
      match uu____3761 with | (id',x,uu____3770) -> bv_to_name x r
  
let find_in_module :
  'uuuuuu3782 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'uuuuuu3782)
          -> 'uuuuuu3782 -> 'uuuuuu3782
  =
  fun env1  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3823 =
            let uu____3831 = FStar_Ident.string_of_lid lid  in
            FStar_Util.smap_try_find (sigmap env1) uu____3831  in
          match uu____3823 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun id  ->
      let uu____3869 = unmangleOpName id  in
      match uu____3869 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3875 ->
          try_lookup_id'' env1 id Exported_id_term_type
            (fun r  ->
               let uu____3881 =
                 let uu____3882 = FStar_Ident.range_of_id id  in
                 found_local_binding uu____3882 r  in
               Cont_ok uu____3881) (fun uu____3884  -> Cont_fail)
            (fun uu____3886  -> Cont_ignore)
            (fun i  ->
               find_in_module env1 i
                 (fun uu____3893  -> fun uu____3894  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3902  -> fun uu____3903  -> Cont_fail)
  
let lookup_default_id :
  'a .
    env ->
      FStar_Ident.ident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'a cont_t)
          -> 'a cont_t -> 'a cont_t
  =
  fun env1  ->
    fun id  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let find_in_monad =
            match env1.curmonad with
            | FStar_Pervasives_Native.Some uu____3977 ->
                let lid = qualify env1 id  in
                let uu____3979 =
                  let uu____3987 = FStar_Ident.string_of_lid lid  in
                  FStar_Util.smap_try_find (sigmap env1) uu____3987  in
                (match uu____3979 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____4009 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____4009
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v -> v
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____4033 = current_module env1  in qual uu____4033 id
                 in
              find_in_module env1 lid k_global_def k_not_found
  
let (lid_is_curmod : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      match env1.curmodule with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some m -> FStar_Ident.lid_equals lid m
  
let (module_is_defined : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      (lid_is_curmod env1 lid) ||
        (FStar_List.existsb
           (fun x  ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env1.modules)
  
let (resolve_module_name :
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen =
          let uu____4096 = FStar_Ident.ns_of_lid lid  in
          FStar_List.length uu____4096  in
        let rec aux uu___9_4108 =
          match uu___9_4108 with
          | [] ->
              let uu____4113 = module_is_defined env1 lid  in
              if uu____4113
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____4125 =
                  let uu____4126 = FStar_Ident.path_of_lid ns  in
                  let uu____4130 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____4126 uu____4130  in
                let uu____4135 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____4125 uu____4135  in
              let uu____4136 = module_is_defined env1 new_lid  in
              if uu____4136
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____4145 when
              (nslen = Prims.int_zero) &&
                (let uu____4152 = FStar_Ident.text_of_id name  in
                 let uu____4154 =
                   let uu____4156 = FStar_Ident.ident_of_lid lid  in
                   FStar_Ident.text_of_id uu____4156  in
                 uu____4152 = uu____4154)
              -> FStar_Pervasives_Native.Some modul
          | uu____4158::q -> aux q  in
        aux env1.scope_mods
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      fun open_kind1  ->
        FStar_List.existsb
          (fun uu___10_4182  ->
             match uu___10_4182 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind1) && (FStar_Ident.lid_equals lid ns)
             | uu____4186 -> false) env1.scope_mods
  
let (namespace_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  -> fun lid  -> is_open env1 lid Open_namespace 
let (module_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  -> (lid_is_curmod env1 lid) || (is_open env1 lid Open_module)
  
let (shorten_module_path :
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  =
  fun env1  ->
    fun ids  ->
      fun is_full_path  ->
        let rec aux revns id =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id
             in
          if namespace_is_open env1 lid
          then
            FStar_Pervasives_Native.Some ((FStar_List.rev (id :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu____4315 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____4315
                   (FStar_Util.map_option
                      (fun uu____4365  ->
                         match uu____4365 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids)))))
           in
        let do_shorten env2 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4435 = aux ns_rev_prefix ns_last_id  in
              (match uu____4435 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > Prims.int_zero)
        then
          let uu____4498 =
            let uu____4501 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env1 uu____4501 true  in
          match uu____4498 with
          | FStar_Pervasives_Native.Some m when module_is_open env1 m ->
              (ids, [])
          | uu____4516 -> do_shorten env1 ids
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
  fun env1  ->
    fun lid  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun f_module  ->
                fun l_default  ->
                  let uu____4637 = FStar_Ident.ns_of_lid lid  in
                  match uu____4637 with
                  | uu____4640::uu____4641 ->
                      let uu____4644 =
                        let uu____4647 =
                          let uu____4648 =
                            let uu____4649 = FStar_Ident.ns_of_lid lid  in
                            FStar_Ident.lid_of_ids uu____4649  in
                          let uu____4650 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4648 uu____4650  in
                        resolve_module_name env1 uu____4647 true  in
                      (match uu____4644 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4655 =
                             let uu____4658 = FStar_Ident.ident_of_lid lid
                                in
                             find_in_module_with_includes eikind f_module
                               Cont_fail env1 modul uu____4658
                              in
                           option_of_cont
                             (fun uu____4660  -> FStar_Pervasives_Native.None)
                             uu____4655)
                  | [] ->
                      let uu____4661 = FStar_Ident.ident_of_lid lid  in
                      try_lookup_id'' env1 uu____4661 eikind k_local_binding
                        k_rec_binding k_record f_module l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___11_4685  ->
      match uu___11_4685 with
      | FStar_Pervasives_Native.Some v -> Cont_ok v
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
  fun env1  ->
    fun lid  ->
      fun k_local_binding  ->
        fun k_rec_binding  ->
          fun k_global_def  ->
            let k_global_def' k lid1 def =
              let uu____4806 = k_global_def lid1 def  in
              cont_of_option k uu____4806  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env1 lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env1 i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env1 lid Exported_id_term_type
              (fun l  ->
                 let uu____4842 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4842)
              (fun r  ->
                 let uu____4848 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4848)
              (fun uu____4852  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4863,uu____4864,uu____4865,l,uu____4867,uu____4868) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___12_4881  ->
               match uu___12_4881 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4884,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4896 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4902,uu____4903,uu____4904)
        -> FStar_Pervasives_Native.None
    | uu____4905 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4921 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4929 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4929
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4921 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4954 =
         let uu____4955 = FStar_Ident.ns_of_lid lid  in
         FStar_List.length uu____4955  in
       let uu____4958 =
         let uu____4959 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4959  in
       uu____4954 = uu____4958) &&
        (let uu____4963 =
           let uu____4964 = FStar_Ident.ns_of_lid lid  in
           FStar_Ident.lid_of_ids uu____4964  in
         FStar_Ident.lid_equals uu____4963 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____4981 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___13_4988  ->
                     match uu___13_4988 with
                     | FStar_Syntax_Syntax.Projector uu____4990 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____4996 -> true
                     | uu____4998 -> false)))
           in
        if uu____4981
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____5003 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___14_5009  ->
                 match uu___14_5009 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____5012 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___15_5018  ->
                    match uu___15_5018 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____5021 -> false)))
             &&
             (let uu____5024 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___16_5030  ->
                        match uu___16_5030 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____5033 -> false))
                 in
              Prims.op_Negation uu____5024))
         in
      if uu____5003 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
let (try_lookup_name :
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option)
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env1  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid  in
          let k_global_def source_lid uu___19_5085 =
            match uu___19_5085 with
            | (uu____5093,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____5097) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____5102 ->
                     let uu____5119 =
                       let uu____5120 =
                         let uu____5127 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____5127, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____5120  in
                     FStar_Pervasives_Native.Some uu____5119
                 | FStar_Syntax_Syntax.Sig_datacon uu____5130 ->
                     let uu____5146 =
                       let uu____5147 =
                         let uu____5154 =
                           let uu____5155 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____5155
                            in
                         (uu____5154, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____5147  in
                     FStar_Pervasives_Native.Some uu____5146
                 | FStar_Syntax_Syntax.Sig_let ((uu____5160,lbs),uu____5162)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____5174 =
                       let uu____5175 =
                         let uu____5182 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____5182, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____5175  in
                     FStar_Pervasives_Native.Some uu____5174
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____5186,uu____5187) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____5191 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___17_5197  ->
                                  match uu___17_5197 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____5200 -> false)))
                        in
                     if uu____5191
                     then
                       let lid2 =
                         let uu____5206 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____5206  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____5208 =
                         FStar_Util.find_map quals
                           (fun uu___18_5213  ->
                              match uu___18_5213 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____5217 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____5208 with
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
                        | uu____5226 ->
                            let uu____5229 =
                              let uu____5230 =
                                let uu____5237 =
                                  let uu____5238 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____5238
                                   in
                                (uu____5237,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____5230  in
                            FStar_Pervasives_Native.Some uu____5229)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5246 =
                       let uu____5247 =
                         let uu____5252 =
                           let uu____5253 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____5253
                            in
                         (se, uu____5252)  in
                       Eff_name uu____5247  in
                     FStar_Pervasives_Native.Some uu____5246
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5254 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____5273 =
                       let uu____5274 =
                         let uu____5281 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                Prims.int_one) FStar_Pervasives_Native.None
                            in
                         (uu____5281, [])  in
                       Term_name uu____5274  in
                     FStar_Pervasives_Native.Some uu____5273
                 | uu____5285 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____5307 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____5307 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____5365 =
            match uu____5365 with
            | (id,l,dd,used_marker1) ->
                (FStar_ST.op_Colon_Equals used_marker1 true;
                 (let uu____5523 =
                    let uu____5524 =
                      let uu____5531 =
                        let uu____5532 =
                          let uu____5533 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range l uu____5533  in
                        FStar_Syntax_Syntax.fvar uu____5532 dd
                          FStar_Pervasives_Native.None
                         in
                      (uu____5531, [])  in
                    Term_name uu____5524  in
                  FStar_Pervasives_Native.Some uu____5523))
             in
          let found_unmangled =
            let uu____5539 = FStar_Ident.ns_of_lid lid  in
            match uu____5539 with
            | [] ->
                let uu____5542 =
                  let uu____5545 = FStar_Ident.ident_of_lid lid  in
                  unmangleOpName uu____5545  in
                (match uu____5542 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____5551 -> FStar_Pervasives_Native.None)
            | uu____5554 -> FStar_Pervasives_Native.None  in
          match found_unmangled with
          | FStar_Pervasives_Native.None  ->
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
  fun exclude_interf  ->
    fun env1  ->
      fun lid  ->
        let uu____5590 = try_lookup_name true exclude_interf env1 lid  in
        match uu____5590 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____5606 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____5626 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l  in
      match uu____5626 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5641 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____5667 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l  in
      match uu____5667 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5683;
             FStar_Syntax_Syntax.sigquals = uu____5684;
             FStar_Syntax_Syntax.sigmeta = uu____5685;
             FStar_Syntax_Syntax.sigattrs = uu____5686;
             FStar_Syntax_Syntax.sigopts = uu____5687;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5707,uu____5708,uu____5709,uu____5710,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5712;
             FStar_Syntax_Syntax.sigquals = uu____5713;
             FStar_Syntax_Syntax.sigmeta = uu____5714;
             FStar_Syntax_Syntax.sigattrs = uu____5715;
             FStar_Syntax_Syntax.sigopts = uu____5716;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5740 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____5766 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l  in
      match uu____5766 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5776;
             FStar_Syntax_Syntax.sigquals = uu____5777;
             FStar_Syntax_Syntax.sigmeta = uu____5778;
             FStar_Syntax_Syntax.sigattrs = uu____5779;
             FStar_Syntax_Syntax.sigopts = uu____5780;_},uu____5781)
          -> FStar_Pervasives_Native.Some ne
      | uu____5792 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____5811 = try_lookup_effect_name env1 lid  in
      match uu____5811 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5816 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____5831 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l  in
      match uu____5831 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5841,uu____5842,uu____5843,uu____5844);
             FStar_Syntax_Syntax.sigrng = uu____5845;
             FStar_Syntax_Syntax.sigquals = uu____5846;
             FStar_Syntax_Syntax.sigmeta = uu____5847;
             FStar_Syntax_Syntax.sigattrs = uu____5848;
             FStar_Syntax_Syntax.sigopts = uu____5849;_},uu____5850)
          ->
          let rec aux new_name =
            let uu____5873 =
              let uu____5881 = FStar_Ident.string_of_lid new_name  in
              FStar_Util.smap_try_find (sigmap env1) uu____5881  in
            match uu____5873 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5896) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5907 =
                       let uu____5908 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5908
                        in
                     FStar_Pervasives_Native.Some uu____5907
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5909,uu____5910,uu____5911,cmp,uu____5913) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5919 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5920,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5926 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals_and_attrs :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.qualifier Prims.list *
        FStar_Syntax_Syntax.attribute Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let k_global_def lid1 uu___20_5977 =
        match uu___20_5977 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5993,uu____5994,uu____5995);
             FStar_Syntax_Syntax.sigrng = uu____5996;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5998;
             FStar_Syntax_Syntax.sigattrs = attrs;
             FStar_Syntax_Syntax.sigopts = uu____6000;_},uu____6001)
            -> FStar_Pervasives_Native.Some (quals, attrs)
        | uu____6022 -> FStar_Pervasives_Native.None  in
      let uu____6036 =
        resolve_in_open_namespaces' env1 lid
          (fun uu____6056  -> FStar_Pervasives_Native.None)
          (fun uu____6066  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____6036 with
      | FStar_Pervasives_Native.Some qa -> qa
      | uu____6100 -> ([], [])
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun path  ->
      let uu____6128 =
        FStar_List.tryFind
          (fun uu____6143  ->
             match uu____6143 with
             | (mlid,modul) ->
                 let uu____6151 = FStar_Ident.path_of_lid mlid  in
                 uu____6151 = path) env1.modules
         in
      match uu____6128 with
      | FStar_Pervasives_Native.Some (uu____6154,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let k_global_def lid1 uu___21_6194 =
        match uu___21_6194 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____6202,lbs),uu____6204);
             FStar_Syntax_Syntax.sigrng = uu____6205;
             FStar_Syntax_Syntax.sigquals = uu____6206;
             FStar_Syntax_Syntax.sigmeta = uu____6207;
             FStar_Syntax_Syntax.sigattrs = uu____6208;
             FStar_Syntax_Syntax.sigopts = uu____6209;_},uu____6210)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____6230 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____6230
        | uu____6231 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6238  -> FStar_Pervasives_Native.None)
        (fun uu____6240  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let k_global_def lid1 uu___22_6273 =
        match uu___22_6273 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____6284);
             FStar_Syntax_Syntax.sigrng = uu____6285;
             FStar_Syntax_Syntax.sigquals = uu____6286;
             FStar_Syntax_Syntax.sigmeta = uu____6287;
             FStar_Syntax_Syntax.sigattrs = uu____6288;
             FStar_Syntax_Syntax.sigopts = uu____6289;_},uu____6290)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____6318 -> FStar_Pervasives_Native.None)
        | uu____6325 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6336  -> FStar_Pervasives_Native.None)
        (fun uu____6340  -> FStar_Pervasives_Native.None) k_global_def
  
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
      fun env1  ->
        fun lid  ->
          let uu____6400 = try_lookup_name any_val exclude_interface env1 lid
             in
          match uu____6400 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____6425 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____6463) ->
        FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_with_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  = fun env1  -> fun l  -> try_lookup_lid' env1.iface false env1 l 
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____6521 = try_lookup_lid_with_attributes env1 l  in
      FStar_All.pipe_right uu____6521 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____6553 = try_lookup_lid env1 l  in
      match uu____6553 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____6559 =
            let uu____6560 = FStar_Syntax_Subst.compress e  in
            uu____6560.FStar_Syntax_Syntax.n  in
          (match uu____6559 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____6566 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____6578 =
        let uu____6587 = FStar_Ident.ns_of_lid lid  in
        shorten_module_path env1 uu____6587 true  in
      match uu____6578 with
      | (uu____6591,short) ->
          let uu____6601 = FStar_Ident.ident_of_lid lid  in
          FStar_Ident.lid_of_ns_and_id short uu____6601
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env1  ->
    fun lid  ->
      match env1.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env1 lid
      | uu____6613 ->
          let lid_without_ns =
            let uu____6617 = FStar_Ident.ident_of_lid lid  in
            FStar_Ident.lid_of_ns_and_id [] uu____6617  in
          let uu____6618 =
            resolve_to_fully_qualified_name env1 lid_without_ns  in
          (match uu____6618 with
           | FStar_Pervasives_Native.Some lid' when
               let uu____6622 = FStar_Ident.string_of_lid lid'  in
               let uu____6624 = FStar_Ident.string_of_lid lid  in
               uu____6622 = uu____6624 -> lid_without_ns
           | uu____6627 -> shorten_lid' env1 lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let env' =
        let uu___867_6658 = env1  in
        {
          curmodule = (uu___867_6658.curmodule);
          curmonad = (uu___867_6658.curmonad);
          modules = (uu___867_6658.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___867_6658.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___867_6658.sigaccum);
          sigmap = (uu___867_6658.sigmap);
          iface = (uu___867_6658.iface);
          admitted_iface = (uu___867_6658.admitted_iface);
          expect_typ = (uu___867_6658.expect_typ);
          remaining_iface_decls = (uu___867_6658.remaining_iface_decls);
          syntax_only = (uu___867_6658.syntax_only);
          ds_hooks = (uu___867_6658.ds_hooks);
          dep_graph = (uu___867_6658.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____6674 = try_lookup_lid_with_attributes_no_resolve env1 l  in
      FStar_All.pipe_right uu____6674 drop_attributes
  
let (try_lookup_datacon :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let k_global_def lid1 se =
        match se with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____6731,uu____6732,uu____6733);
             FStar_Syntax_Syntax.sigrng = uu____6734;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6736;
             FStar_Syntax_Syntax.sigattrs = uu____6737;
             FStar_Syntax_Syntax.sigopts = uu____6738;_},uu____6739)
            ->
            let uu____6748 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___23_6754  ->
                      match uu___23_6754 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6757 -> false))
               in
            if uu____6748
            then
              let uu____6762 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6762
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6765;
             FStar_Syntax_Syntax.sigrng = uu____6766;
             FStar_Syntax_Syntax.sigquals = uu____6767;
             FStar_Syntax_Syntax.sigmeta = uu____6768;
             FStar_Syntax_Syntax.sigattrs = uu____6769;
             FStar_Syntax_Syntax.sigopts = uu____6770;_},uu____6771)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____6799 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____6799
        | uu____6800 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6807  -> FStar_Pervasives_Native.None)
        (fun uu____6809  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let k_global_def lid1 uu___24_6844 =
        match uu___24_6844 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6854,uu____6855,uu____6856,uu____6857,datas,uu____6859);
             FStar_Syntax_Syntax.sigrng = uu____6860;
             FStar_Syntax_Syntax.sigquals = uu____6861;
             FStar_Syntax_Syntax.sigmeta = uu____6862;
             FStar_Syntax_Syntax.sigattrs = uu____6863;
             FStar_Syntax_Syntax.sigopts = uu____6864;_},uu____6865)
            -> FStar_Pervasives_Native.Some datas
        | uu____6884 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6895  -> FStar_Pervasives_Native.None)
        (fun uu____6899  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push uu____6978 =
    let uu____6979 =
      let uu____6984 =
        let uu____6987 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6987  in
      let uu____7021 = FStar_ST.op_Bang record_cache  in uu____6984 ::
        uu____7021
       in
    FStar_ST.op_Colon_Equals record_cache uu____6979  in
  let pop uu____7087 =
    let uu____7088 =
      let uu____7093 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____7093  in
    FStar_ST.op_Colon_Equals record_cache uu____7088  in
  let snapshot uu____7164 = FStar_Common.snapshot push record_cache ()  in
  let rollback depth = FStar_Common.rollback pop record_cache depth  in
  let peek uu____7188 =
    let uu____7189 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____7189  in
  let insert r =
    let uu____7229 =
      let uu____7234 = let uu____7237 = peek ()  in r :: uu____7237  in
      let uu____7240 =
        let uu____7245 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____7245  in
      uu____7234 :: uu____7240  in
    FStar_ST.op_Colon_Equals record_cache uu____7229  in
  let filter uu____7313 =
    let rc = peek ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____7322 =
      let uu____7327 =
        let uu____7332 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____7332  in
      filtered :: uu____7327  in
    FStar_ST.op_Colon_Equals record_cache uu____7322  in
  let aux = ((push, pop), ((snapshot, rollback), (peek, insert)))  in
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
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____8258) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___25_8277  ->
                   match uu___25_8277 with
                   | FStar_Syntax_Syntax.RecordType uu____8279 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____8289 -> true
                   | uu____8299 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___26_8325  ->
                      match uu___26_8325 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____8328,uu____8329,uu____8330,uu____8331,uu____8332);
                          FStar_Syntax_Syntax.sigrng = uu____8333;
                          FStar_Syntax_Syntax.sigquals = uu____8334;
                          FStar_Syntax_Syntax.sigmeta = uu____8335;
                          FStar_Syntax_Syntax.sigattrs = uu____8336;
                          FStar_Syntax_Syntax.sigopts = uu____8337;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____8350 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___27_8391  ->
                    match uu___27_8391 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____8395,uu____8396,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____8398;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____8400;
                        FStar_Syntax_Syntax.sigattrs = uu____8401;
                        FStar_Syntax_Syntax.sigopts = uu____8402;_} ->
                        let uu____8415 =
                          let uu____8416 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____8416  in
                        (match uu____8415 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____8422,t,uu____8424,n,uu____8426);
                             FStar_Syntax_Syntax.sigrng = uu____8427;
                             FStar_Syntax_Syntax.sigquals = uu____8428;
                             FStar_Syntax_Syntax.sigmeta = uu____8429;
                             FStar_Syntax_Syntax.sigattrs = uu____8430;
                             FStar_Syntax_Syntax.sigopts = uu____8431;_} ->
                             let uu____8444 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____8444 with
                              | (all_formals,uu____8452) ->
                                  let uu____8457 =
                                    FStar_Util.first_N n all_formals  in
                                  (match uu____8457 with
                                   | (_params,formals) ->
                                       let is_rec = is_record typename_quals
                                          in
                                       let formals' =
                                         FStar_All.pipe_right formals
                                           (FStar_List.collect
                                              (fun uu____8551  ->
                                                 match uu____8551 with
                                                 | (x,q) ->
                                                     let uu____8564 =
                                                       (FStar_Syntax_Syntax.is_null_bv
                                                          x)
                                                         ||
                                                         (is_rec &&
                                                            (FStar_Syntax_Syntax.is_implicit
                                                               q))
                                                        in
                                                     if uu____8564
                                                     then []
                                                     else [(x, q)]))
                                          in
                                       let fields' =
                                         FStar_All.pipe_right formals'
                                           (FStar_List.map
                                              (fun uu____8619  ->
                                                 match uu____8619 with
                                                 | (x,q) ->
                                                     ((x.FStar_Syntax_Syntax.ppname),
                                                       (x.FStar_Syntax_Syntax.sort))))
                                          in
                                       let fields = fields'  in
                                       let record =
                                         let uu____8642 =
                                           FStar_Ident.ident_of_lid
                                             constrname
                                            in
                                         {
                                           typename;
                                           constrname = uu____8642;
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
                                       ((let uu____8644 =
                                           let uu____8647 =
                                             FStar_ST.op_Bang new_globs  in
                                           (Record_or_dc record) ::
                                             uu____8647
                                            in
                                         FStar_ST.op_Colon_Equals new_globs
                                           uu____8644);
                                        (match () with
                                         | () ->
                                             ((let add_field uu____8706 =
                                                 match uu____8706 with
                                                 | (id,uu____8712) ->
                                                     let modul =
                                                       let uu____8715 =
                                                         let uu____8716 =
                                                           FStar_Ident.ns_of_lid
                                                             constrname
                                                            in
                                                         FStar_Ident.lid_of_ids
                                                           uu____8716
                                                          in
                                                       FStar_Ident.string_of_lid
                                                         uu____8715
                                                        in
                                                     let uu____8717 =
                                                       get_exported_id_set e
                                                         modul
                                                        in
                                                     (match uu____8717 with
                                                      | FStar_Pervasives_Native.Some
                                                          my_ex ->
                                                          let my_exported_ids
                                                            =
                                                            my_ex
                                                              Exported_id_field
                                                             in
                                                          ((let uu____8740 =
                                                              let uu____8741
                                                                =
                                                                FStar_Ident.text_of_id
                                                                  id
                                                                 in
                                                              let uu____8743
                                                                =
                                                                FStar_ST.op_Bang
                                                                  my_exported_ids
                                                                 in
                                                              FStar_Util.set_add
                                                                uu____8741
                                                                uu____8743
                                                               in
                                                            FStar_ST.op_Colon_Equals
                                                              my_exported_ids
                                                              uu____8740);
                                                           (match () with
                                                            | () ->
                                                                let projname
                                                                  =
                                                                  let uu____8788
                                                                    =
                                                                    let uu____8789
                                                                    =
                                                                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                    constrname
                                                                    id  in
                                                                    FStar_All.pipe_right
                                                                    uu____8789
                                                                    FStar_Ident.ident_of_lid
                                                                     in
                                                                  FStar_All.pipe_right
                                                                    uu____8788
                                                                    FStar_Ident.text_of_id
                                                                   in
                                                                let uu____8792
                                                                  =
                                                                  let uu____8793
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    my_exported_ids
                                                                     in
                                                                  FStar_Util.set_add
                                                                    projname
                                                                    uu____8793
                                                                   in
                                                                FStar_ST.op_Colon_Equals
                                                                  my_exported_ids
                                                                  uu____8792))
                                                      | FStar_Pervasives_Native.None
                                                           -> ())
                                                  in
                                               FStar_List.iter add_field
                                                 fields');
                                              (match () with
                                               | () ->
                                                   insert_record_cache record))))))
                         | uu____8845 -> ())
                    | uu____8846 -> ()))
        | uu____8847 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env1  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8869 =
          let uu____8876 = FStar_Ident.ns_of_lid fieldname1  in
          let uu____8879 = FStar_Ident.ident_of_lid fieldname1  in
          (uu____8876, uu____8879)  in
        match uu____8869 with
        | (ns,id) ->
            let uu____8890 = peek_record_cache ()  in
            FStar_Util.find_map uu____8890
              (fun record  ->
                 let uu____8896 =
                   find_in_record ns id record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8902  -> FStar_Pervasives_Native.None)
                   uu____8896)
         in
      resolve_in_open_namespaces'' env1 fieldname Exported_id_field
        (fun uu____8904  -> Cont_ignore) (fun uu____8906  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8912 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8912)
        (fun k  -> fun uu____8918  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env1  ->
    fun fieldname  ->
      let uu____8934 = try_lookup_record_or_dc_by_field_name env1 fieldname
         in
      match uu____8934 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8940 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      fun record  ->
        let uu____8960 = try_lookup_record_by_field_name env1 lid  in
        match uu____8960 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8965 = FStar_Ident.nsstr record.typename  in
            let uu____8967 = FStar_Ident.nsstr record'.typename  in
            uu____8965 = uu____8967 ->
            let uu____8970 =
              let uu____8973 = FStar_Ident.ns_of_lid record.typename  in
              let uu____8976 = FStar_Ident.ident_of_lid lid  in
              find_in_record uu____8973 uu____8976 record
                (fun uu____8978  -> Cont_ok ())
               in
            (match uu____8970 with
             | Cont_ok uu____8980 -> true
             | uu____8982 -> false)
        | uu____8986 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fieldname  ->
      let uu____9008 = try_lookup_record_or_dc_by_field_name env1 fieldname
         in
      match uu____9008 with
      | FStar_Pervasives_Native.Some r ->
          let uu____9019 =
            let uu____9025 =
              let uu____9026 =
                let uu____9027 =
                  let uu____9028 = FStar_Ident.ns_of_lid r.typename  in
                  FStar_List.append uu____9028 [r.constrname]  in
                FStar_Ident.lid_of_ids uu____9027  in
              let uu____9031 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____9026 uu____9031  in
            (uu____9025, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____9019
      | uu____9038 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____9056  ->
    let uu____9057 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____9057
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____9078  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___28_9091  ->
      match uu___28_9091 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env1  ->
        fun lid  ->
          let filter_scope_mods uu___29_9129 =
            match uu___29_9129 with
            | Rec_binding uu____9131 -> true
            | uu____9133 -> false  in
          let this_env =
            let uu___1100_9136 = env1  in
            let uu____9137 =
              FStar_List.filter filter_scope_mods env1.scope_mods  in
            {
              curmodule = (uu___1100_9136.curmodule);
              curmonad = (uu___1100_9136.curmonad);
              modules = (uu___1100_9136.modules);
              scope_mods = uu____9137;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1100_9136.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1100_9136.sigaccum);
              sigmap = (uu___1100_9136.sigmap);
              iface = (uu___1100_9136.iface);
              admitted_iface = (uu___1100_9136.admitted_iface);
              expect_typ = (uu___1100_9136.expect_typ);
              remaining_iface_decls = (uu___1100_9136.remaining_iface_decls);
              syntax_only = (uu___1100_9136.syntax_only);
              ds_hooks = (uu___1100_9136.ds_hooks);
              dep_graph = (uu___1100_9136.dep_graph)
            }  in
          let uu____9140 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____9140 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____9157 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env1  ->
    fun scope_mod1  ->
      let uu___1108_9182 = env1  in
      {
        curmodule = (uu___1108_9182.curmodule);
        curmonad = (uu___1108_9182.curmonad);
        modules = (uu___1108_9182.modules);
        scope_mods = (scope_mod1 :: (env1.scope_mods));
        exported_ids = (uu___1108_9182.exported_ids);
        trans_exported_ids = (uu___1108_9182.trans_exported_ids);
        includes = (uu___1108_9182.includes);
        sigaccum = (uu___1108_9182.sigaccum);
        sigmap = (uu___1108_9182.sigmap);
        iface = (uu___1108_9182.iface);
        admitted_iface = (uu___1108_9182.admitted_iface);
        expect_typ = (uu___1108_9182.expect_typ);
        remaining_iface_decls = (uu___1108_9182.remaining_iface_decls);
        syntax_only = (uu___1108_9182.syntax_only);
        ds_hooks = (uu___1108_9182.ds_hooks);
        dep_graph = (uu___1108_9182.dep_graph)
      }
  
let (push_bv' :
  env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv * used_marker)) =
  fun env1  ->
    fun x  ->
      let bv =
        let uu____9201 = FStar_Ident.text_of_id x  in
        let uu____9203 =
          let uu____9206 = FStar_Ident.range_of_id x  in
          FStar_Pervasives_Native.Some uu____9206  in
        FStar_Syntax_Syntax.gen_bv uu____9201 uu____9203
          FStar_Syntax_Syntax.tun
         in
      let used_marker1 = FStar_Util.mk_ref false  in
      ((push_scope_mod env1 (Local_binding (x, bv, used_marker1))), bv,
        used_marker1)
  
let (push_bv : env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv)) =
  fun env1  ->
    fun x  ->
      let uu____9228 = push_bv' env1 x  in
      match uu____9228 with | (env2,bv,uu____9241) -> (env2, bv)
  
let (push_top_level_rec_binding :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.delta_depth -> (env * Prims.bool FStar_ST.ref))
  =
  fun env0  ->
    fun x  ->
      fun dd  ->
        let l = qualify env0 x  in
        let uu____9273 =
          (unique false true env0 l) || (FStar_Options.interactive ())  in
        if uu____9273
        then
          let used_marker1 = FStar_Util.mk_ref false  in
          ((push_scope_mod env0 (Rec_binding (x, l, dd, used_marker1))),
            used_marker1)
        else
          (let uu____9296 =
             let uu____9302 =
               let uu____9304 = FStar_Ident.string_of_lid l  in
               Prims.op_Hat "Duplicate top-level names " uu____9304  in
             (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____9302)  in
           let uu____9308 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____9296 uu____9308)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env1  ->
      fun s  ->
        let err l =
          let sopt =
            let uu____9348 = FStar_Ident.string_of_lid l  in
            FStar_Util.smap_try_find (sigmap env1) uu____9348  in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____9359) ->
                let uu____9367 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____9367 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____9372 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____9372
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____9381 =
            let uu____9387 =
              let uu____9389 = FStar_Ident.string_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____9389 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____9387)  in
          let uu____9393 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____9381 uu____9393  in
        let globals = FStar_Util.mk_ref env1.scope_mods  in
        let env2 =
          let uu____9402 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____9415 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____9426 -> (false, true)
            | uu____9439 -> (false, false)  in
          match uu____9402 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____9453 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____9459 =
                       let uu____9461 =
                         unique any_val exclude_interface env1 l  in
                       Prims.op_Negation uu____9461  in
                     if uu____9459
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____9453 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____9469 ->
                   (extract_record env1 globals s;
                    (let uu___1157_9473 = env1  in
                     {
                       curmodule = (uu___1157_9473.curmodule);
                       curmonad = (uu___1157_9473.curmonad);
                       modules = (uu___1157_9473.modules);
                       scope_mods = (uu___1157_9473.scope_mods);
                       exported_ids = (uu___1157_9473.exported_ids);
                       trans_exported_ids =
                         (uu___1157_9473.trans_exported_ids);
                       includes = (uu___1157_9473.includes);
                       sigaccum = (s :: (env1.sigaccum));
                       sigmap = (uu___1157_9473.sigmap);
                       iface = (uu___1157_9473.iface);
                       admitted_iface = (uu___1157_9473.admitted_iface);
                       expect_typ = (uu___1157_9473.expect_typ);
                       remaining_iface_decls =
                         (uu___1157_9473.remaining_iface_decls);
                       syntax_only = (uu___1157_9473.syntax_only);
                       ds_hooks = (uu___1157_9473.ds_hooks);
                       dep_graph = (uu___1157_9473.dep_graph)
                     })))
           in
        let env3 =
          let uu___1160_9475 = env2  in
          let uu____9476 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1160_9475.curmodule);
            curmonad = (uu___1160_9475.curmonad);
            modules = (uu___1160_9475.modules);
            scope_mods = uu____9476;
            exported_ids = (uu___1160_9475.exported_ids);
            trans_exported_ids = (uu___1160_9475.trans_exported_ids);
            includes = (uu___1160_9475.includes);
            sigaccum = (uu___1160_9475.sigaccum);
            sigmap = (uu___1160_9475.sigmap);
            iface = (uu___1160_9475.iface);
            admitted_iface = (uu___1160_9475.admitted_iface);
            expect_typ = (uu___1160_9475.expect_typ);
            remaining_iface_decls = (uu___1160_9475.remaining_iface_decls);
            syntax_only = (uu___1160_9475.syntax_only);
            ds_hooks = (uu___1160_9475.ds_hooks);
            dep_graph = (uu___1160_9475.dep_graph)
          }  in
        let uu____9502 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9528) ->
              let uu____9537 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env3, uu____9537)
          | uu____9564 -> (env3, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____9502 with
        | (env4,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____9623  ->
                     match uu____9623 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____9646 =
                                    let uu____9649 =
                                      let uu____9650 =
                                        FStar_Ident.ident_of_lid lid  in
                                      Top_level_def uu____9650  in
                                    let uu____9651 = FStar_ST.op_Bang globals
                                       in
                                    uu____9649 :: uu____9651  in
                                  FStar_ST.op_Colon_Equals globals uu____9646);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____9702 =
                                          let uu____9703 =
                                            FStar_Ident.ns_of_lid lid  in
                                          FStar_Ident.lid_of_ids uu____9703
                                           in
                                        FStar_Ident.string_of_lid uu____9702
                                         in
                                      ((let uu____9705 =
                                          get_exported_id_set env4 modul  in
                                        match uu____9705 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____9727 =
                                              let uu____9728 =
                                                let uu____9730 =
                                                  FStar_Ident.ident_of_lid
                                                    lid
                                                   in
                                                FStar_Ident.text_of_id
                                                  uu____9730
                                                 in
                                              let uu____9731 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add uu____9728
                                                uu____9731
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____9727
                                        | FStar_Pervasives_Native.None  -> ());
                                       (match () with
                                        | () ->
                                            let is_iface =
                                              env4.iface &&
                                                (Prims.op_Negation
                                                   env4.admitted_iface)
                                               in
                                            let uu____9781 =
                                              FStar_Ident.string_of_lid lid
                                               in
                                            FStar_Util.smap_add (sigmap env4)
                                              uu____9781
                                              (se,
                                                (env4.iface &&
                                                   (Prims.op_Negation
                                                      env4.admitted_iface))))))))));
             (let env5 =
                let uu___1185_9790 = env4  in
                let uu____9791 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1185_9790.curmodule);
                  curmonad = (uu___1185_9790.curmonad);
                  modules = (uu___1185_9790.modules);
                  scope_mods = uu____9791;
                  exported_ids = (uu___1185_9790.exported_ids);
                  trans_exported_ids = (uu___1185_9790.trans_exported_ids);
                  includes = (uu___1185_9790.includes);
                  sigaccum = (uu___1185_9790.sigaccum);
                  sigmap = (uu___1185_9790.sigmap);
                  iface = (uu___1185_9790.iface);
                  admitted_iface = (uu___1185_9790.admitted_iface);
                  expect_typ = (uu___1185_9790.expect_typ);
                  remaining_iface_decls =
                    (uu___1185_9790.remaining_iface_decls);
                  syntax_only = (uu___1185_9790.syntax_only);
                  ds_hooks = (uu___1185_9790.ds_hooks);
                  dep_graph = (uu___1185_9790.dep_graph)
                }  in
              env5))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  -> fun se  -> push_sigelt' true env1 se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  -> fun se  -> push_sigelt' false env1 se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun ns  ->
      let uu____9852 =
        let uu____9857 = resolve_module_name env1 ns false  in
        match uu____9857 with
        | FStar_Pervasives_Native.None  ->
            let modules = env1.modules  in
            let uu____9872 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9890  ->
                      match uu____9890 with
                      | (m,uu____9897) ->
                          let uu____9898 =
                            let uu____9900 = FStar_Ident.string_of_lid m  in
                            Prims.op_Hat uu____9900 "."  in
                          let uu____9903 =
                            let uu____9905 = FStar_Ident.string_of_lid ns  in
                            Prims.op_Hat uu____9905 "."  in
                          FStar_Util.starts_with uu____9898 uu____9903))
               in
            if uu____9872
            then (ns, Open_namespace)
            else
              (let uu____9915 =
                 let uu____9921 =
                   let uu____9923 = FStar_Ident.string_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9923
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9921)  in
               let uu____9927 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9915 uu____9927)
        | FStar_Pervasives_Native.Some ns' -> (ns', Open_module)  in
      match uu____9852 with
      | (ns',kd) ->
          ((env1.ds_hooks).ds_push_open_hook env1 (ns', kd);
           push_scope_mod env1 (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9948 = resolve_module_name env1 ns false  in
      match uu____9948 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env1.ds_hooks).ds_push_include_hook env1 ns1;
           (let env2 =
              push_scope_mod env1
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9957 = current_module env2  in
              FStar_Ident.string_of_lid uu____9957  in
            (let uu____9959 = FStar_Util.smap_try_find env2.includes curmod
                in
             match uu____9959 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9983 =
                   let uu____9986 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9986
                    in
                 FStar_ST.op_Colon_Equals incl uu____9983);
            (match () with
             | () ->
                 let uu____10035 =
                   let uu____10043 = FStar_Ident.string_of_lid ns1  in
                   get_trans_exported_id_set env2 uu____10043  in
                 (match uu____10035 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____10057 =
                          let uu____10154 = get_exported_id_set env2 curmod
                             in
                          let uu____10201 =
                            get_trans_exported_id_set env2 curmod  in
                          (uu____10154, uu____10201)  in
                        match uu____10057 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10617 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10617  in
                              let ex = cur_exports k  in
                              (let uu____10718 =
                                 let uu____10722 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____10722 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____10718);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____10814 =
                                     let uu____10818 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____10818 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10814)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10867 -> ());
                       (match () with | () -> env2))
                  | FStar_Pervasives_Native.None  ->
                      let uu____10969 =
                        let uu____10975 =
                          let uu____10977 = FStar_Ident.string_of_lid ns1  in
                          FStar_Util.format1
                            "include: Module %s was not prepared" uu____10977
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10975)
                         in
                      let uu____10981 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____10969 uu____10981))))
      | uu____10982 ->
          let uu____10985 =
            let uu____10991 =
              let uu____10993 = FStar_Ident.string_of_lid ns  in
              FStar_Util.format1 "include: Module %s cannot be found"
                uu____10993
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____10991)  in
          let uu____10997 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____10985 uu____10997
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun x  ->
      fun l  ->
        let uu____11014 = module_is_defined env1 l  in
        if uu____11014
        then
          ((env1.ds_hooks).ds_push_module_abbrev_hook env1 x l;
           push_scope_mod env1 (Module_abbrev (x, l)))
        else
          (let uu____11020 =
             let uu____11026 =
               let uu____11028 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____11028  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____11026)  in
           let uu____11032 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____11020 uu____11032)
  
let (check_admits :
  env -> FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul) =
  fun env1  ->
    fun m  ->
      let admitted_sig_lids =
        FStar_All.pipe_right env1.sigaccum
          (FStar_List.fold_left
             (fun lids  ->
                fun se  ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) when
                      let uu____11075 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____11075 ->
                      let uu____11080 =
                        let uu____11088 = FStar_Ident.string_of_lid l  in
                        FStar_Util.smap_try_find (sigmap env1) uu____11088
                         in
                      (match uu____11080 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____11097;
                              FStar_Syntax_Syntax.sigrng = uu____11098;
                              FStar_Syntax_Syntax.sigquals = uu____11099;
                              FStar_Syntax_Syntax.sigmeta = uu____11100;
                              FStar_Syntax_Syntax.sigattrs = uu____11101;
                              FStar_Syntax_Syntax.sigopts = uu____11102;_},uu____11103)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____11123;
                              FStar_Syntax_Syntax.sigrng = uu____11124;
                              FStar_Syntax_Syntax.sigquals = uu____11125;
                              FStar_Syntax_Syntax.sigmeta = uu____11126;
                              FStar_Syntax_Syntax.sigattrs = uu____11127;
                              FStar_Syntax_Syntax.sigopts = uu____11128;_},uu____11129)
                           -> lids
                       | uu____11159 ->
                           ((let uu____11168 =
                               let uu____11170 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____11170  in
                             if uu____11168
                             then
                               let uu____11173 = FStar_Ident.range_of_lid l
                                  in
                               let uu____11174 =
                                 let uu____11180 =
                                   let uu____11182 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____11182
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____11180)
                                  in
                               FStar_Errors.log_issue uu____11173 uu____11174
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             (let uu____11192 = FStar_Ident.string_of_lid l
                                 in
                              FStar_Util.smap_add (sigmap env1) uu____11192
                                ((let uu___1276_11201 = se  in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (uu___1276_11201.FStar_Syntax_Syntax.sigel);
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___1276_11201.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals = quals;
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___1276_11201.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___1276_11201.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___1276_11201.FStar_Syntax_Syntax.sigopts)
                                  }), false));
                             l
                             ::
                             lids)))
                  | uu____11203 -> lids) [])
         in
      let uu___1281_11204 = m  in
      let uu____11205 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____11215,uu____11216) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1290_11219 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1290_11219.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1290_11219.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1290_11219.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1290_11219.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1290_11219.FStar_Syntax_Syntax.sigopts)
                    }
                | uu____11220 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1281_11204.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11205;
        FStar_Syntax_Syntax.exports =
          (uu___1281_11204.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1281_11204.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env1  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11244) ->
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
                                (lid,uu____11266,uu____11267,uu____11268,uu____11269,uu____11270)
                                ->
                                let uu____11277 =
                                  FStar_Ident.string_of_lid lid  in
                                FStar_Util.smap_remove (sigmap env1)
                                  uu____11277
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____11288,uu____11289)
                                ->
                                ((let uu____11299 =
                                    FStar_Ident.string_of_lid lid  in
                                  FStar_Util.smap_remove (sigmap env1)
                                    uu____11299);
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11308 =
                                        let uu____11315 =
                                          let uu____11316 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____11317 =
                                            let uu____11324 =
                                              let uu____11325 =
                                                let uu____11340 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11340)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11325
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11324
                                             in
                                          uu____11317
                                            FStar_Pervasives_Native.None
                                            uu____11316
                                           in
                                        (lid, univ_names, uu____11315)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11308
                                       in
                                    let se2 =
                                      let uu___1322_11354 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1322_11354.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1322_11354.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1322_11354.FStar_Syntax_Syntax.sigattrs);
                                        FStar_Syntax_Syntax.sigopts =
                                          (uu___1322_11354.FStar_Syntax_Syntax.sigopts)
                                      }  in
                                    let uu____11355 =
                                      FStar_Ident.string_of_lid lid  in
                                    FStar_Util.smap_add (sigmap env1)
                                      uu____11355 (se2, false))
                                 else ())
                            | uu____11366 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11370,uu____11371) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    let uu____11373 = FStar_Ident.string_of_lid lid  in
                    FStar_Util.smap_remove (sigmap env1) uu____11373
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11382,lbs),uu____11384)
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
                             let uu____11402 =
                               let uu____11404 =
                                 let uu____11405 =
                                   let uu____11408 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11408.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11405.FStar_Syntax_Syntax.v  in
                               FStar_Ident.string_of_lid uu____11404  in
                             FStar_Util.smap_remove (sigmap env1) uu____11402))
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
                               let uu____11426 =
                                 let uu____11429 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11429.FStar_Syntax_Syntax.fv_name  in
                               uu____11426.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1345_11434 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1345_11434.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1345_11434.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1345_11434.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___1345_11434.FStar_Syntax_Syntax.sigopts)
                               }  in
                             let uu____11435 = FStar_Ident.string_of_lid lid
                                in
                             FStar_Util.smap_add (sigmap env1) uu____11435
                               (decl, false)))
                   else ())
              | uu____11446 -> ()));
      (let curmod =
         let uu____11449 = current_module env1  in
         FStar_Ident.string_of_lid uu____11449  in
       (let uu____11451 =
          let uu____11548 = get_exported_id_set env1 curmod  in
          let uu____11595 = get_trans_exported_id_set env1 curmod  in
          (uu____11548, uu____11595)  in
        match uu____11451 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____12014 = cur_ex eikind  in
                FStar_ST.op_Bang uu____12014  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____12120 =
                let uu____12124 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____12124  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____12120  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____12173 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1363_12271 = env1  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1363_12271.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env1.modules));
                    scope_mods = [];
                    exported_ids = (uu___1363_12271.exported_ids);
                    trans_exported_ids = (uu___1363_12271.trans_exported_ids);
                    includes = (uu___1363_12271.includes);
                    sigaccum = [];
                    sigmap = (uu___1363_12271.sigmap);
                    iface = (uu___1363_12271.iface);
                    admitted_iface = (uu___1363_12271.admitted_iface);
                    expect_typ = (uu___1363_12271.expect_typ);
                    remaining_iface_decls =
                      (uu___1363_12271.remaining_iface_decls);
                    syntax_only = (uu___1363_12271.syntax_only);
                    ds_hooks = (uu___1363_12271.ds_hooks);
                    dep_graph = (uu___1363_12271.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env1  ->
    FStar_Util.atomically
      (fun uu____12297  ->
         push_record_cache ();
         (let uu____12300 =
            let uu____12303 = FStar_ST.op_Bang stack  in env1 :: uu____12303
             in
          FStar_ST.op_Colon_Equals stack uu____12300);
         (let uu___1369_12352 = env1  in
          let uu____12353 = FStar_Util.smap_copy env1.exported_ids  in
          let uu____12358 = FStar_Util.smap_copy env1.trans_exported_ids  in
          let uu____12363 = FStar_Util.smap_copy env1.includes  in
          let uu____12374 = FStar_Util.smap_copy env1.sigmap  in
          {
            curmodule = (uu___1369_12352.curmodule);
            curmonad = (uu___1369_12352.curmonad);
            modules = (uu___1369_12352.modules);
            scope_mods = (uu___1369_12352.scope_mods);
            exported_ids = uu____12353;
            trans_exported_ids = uu____12358;
            includes = uu____12363;
            sigaccum = (uu___1369_12352.sigaccum);
            sigmap = uu____12374;
            iface = (uu___1369_12352.iface);
            admitted_iface = (uu___1369_12352.admitted_iface);
            expect_typ = (uu___1369_12352.expect_typ);
            remaining_iface_decls = (uu___1369_12352.remaining_iface_decls);
            syntax_only = (uu___1369_12352.syntax_only);
            ds_hooks = (uu___1369_12352.ds_hooks);
            dep_graph = (uu___1369_12352.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____12392  ->
    FStar_Util.atomically
      (fun uu____12399  ->
         let uu____12400 = FStar_ST.op_Bang stack  in
         match uu____12400 with
         | env1::tl ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl; env1)
         | uu____12455 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env1  -> FStar_Common.snapshot push stack env1 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env1  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12502 ->
            let uu____12505 = FStar_Ident.nsstr l  in
            let uu____12507 = FStar_Ident.string_of_lid m  in
            uu____12505 = uu____12507
        | uu____12510 -> false  in
      let sm = sigmap env1  in
      let env2 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env2  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____12552 = FStar_Util.smap_try_find sm' k  in
              match uu____12552 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1404_12583 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1404_12583.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1404_12583.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1404_12583.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1404_12583.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___1404_12583.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____12584 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12592 -> ()));
      env2
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env1  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env1 modul
        else modul  in
      let uu____12619 = finish env1 modul1  in (uu____12619, modul1)
  
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
      let uu____12688 =
        let uu____12692 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____12692  in
      FStar_Util.set_elements uu____12688  in
    let fields =
      let uu____12755 =
        let uu____12759 = e Exported_id_field  in
        FStar_ST.op_Bang uu____12759  in
      FStar_Util.set_elements uu____12755  in
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
          let uu____12851 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____12851  in
        let fields =
          let uu____12865 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____12865  in
        (fun uu___30_12873  ->
           match uu___30_12873 with
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
  'uuuuuu12977 .
    'uuuuuu12977 Prims.list FStar_Pervasives_Native.option ->
      'uuuuuu12977 Prims.list FStar_ST.ref
  =
  fun uu___31_12990  ->
    match uu___31_12990 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env1  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____13033 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____13033 as_exported_ids  in
      let uu____13039 = as_ids_opt env1.exported_ids  in
      let uu____13042 = as_ids_opt env1.trans_exported_ids  in
      let uu____13045 =
        let uu____13050 = FStar_Util.smap_try_find env1.includes mname  in
        FStar_Util.map_opt uu____13050 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____13039;
        mii_trans_exported_ids = uu____13042;
        mii_includes = uu____13045
      }
  
let (prepare_module_or_interface :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident -> module_inclusion_info -> (env * Prims.bool))
  =
  fun intf  ->
    fun admitted  ->
      fun env1  ->
        fun mname  ->
          fun mii  ->
            let prep env2 =
              let filename =
                let uu____13139 = FStar_Ident.string_of_lid mname  in
                FStar_Util.strcat uu____13139 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___32_13161 =
                  match uu___32_13161 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____13173  ->
                     match uu____13173 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                let uu____13191 =
                  let uu____13193 =
                    let uu____13195 = FStar_Ident.ns_of_lid mname  in
                    FStar_List.length uu____13195  in
                  uu____13193 > Prims.int_zero  in
                if uu____13191
                then
                  let uu____13206 =
                    let uu____13211 =
                      let uu____13212 = FStar_Ident.ns_of_lid mname  in
                      FStar_Ident.lid_of_ids uu____13212  in
                    (uu____13211, Open_namespace)  in
                  [uu____13206]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____13243 = FStar_Ident.string_of_lid mname  in
               let uu____13245 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env2.exported_ids uu____13243 uu____13245);
              (match () with
               | () ->
                   ((let uu____13250 = FStar_Ident.string_of_lid mname  in
                     let uu____13252 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env2.trans_exported_ids uu____13250
                       uu____13252);
                    (match () with
                     | () ->
                         ((let uu____13257 = FStar_Ident.string_of_lid mname
                              in
                           let uu____13259 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env2.includes uu____13257
                             uu____13259);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1474_13269 = env2  in
                                 let uu____13270 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1474_13269.curmonad);
                                   modules = (uu___1474_13269.modules);
                                   scope_mods = uu____13270;
                                   exported_ids =
                                     (uu___1474_13269.exported_ids);
                                   trans_exported_ids =
                                     (uu___1474_13269.trans_exported_ids);
                                   includes = (uu___1474_13269.includes);
                                   sigaccum = (uu___1474_13269.sigaccum);
                                   sigmap = (env2.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1474_13269.expect_typ);
                                   remaining_iface_decls =
                                     (uu___1474_13269.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1474_13269.syntax_only);
                                   ds_hooks = (uu___1474_13269.ds_hooks);
                                   dep_graph = (uu___1474_13269.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env2.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____13282 =
              FStar_All.pipe_right env1.modules
                (FStar_Util.find_opt
                   (fun uu____13308  ->
                      match uu____13308 with
                      | (l,uu____13315) -> FStar_Ident.lid_equals l mname))
               in
            match uu____13282 with
            | FStar_Pervasives_Native.None  ->
                let uu____13325 = prep env1  in (uu____13325, false)
            | FStar_Pervasives_Native.Some (uu____13328,m) ->
                ((let uu____13335 =
                    (let uu____13339 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____13339) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____13335
                  then
                    let uu____13342 =
                      let uu____13348 =
                        let uu____13350 = FStar_Ident.string_of_lid mname  in
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          uu____13350
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13348)
                       in
                    let uu____13354 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____13342 uu____13354
                  else ());
                 (let uu____13357 =
                    let uu____13358 = push env1  in prep uu____13358  in
                  (uu____13357, true)))
  
let (enter_monad_scope : env -> FStar_Ident.ident -> env) =
  fun env1  ->
    fun mname  ->
      match env1.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          let uu____13373 =
            let uu____13379 =
              let uu____13381 =
                let uu____13383 = FStar_Ident.text_of_id mname  in
                let uu____13385 =
                  let uu____13387 = FStar_Ident.text_of_id mname'  in
                  Prims.op_Hat ", but already in monad scope " uu____13387
                   in
                Prims.op_Hat uu____13383 uu____13385  in
              Prims.op_Hat "Trying to define monad " uu____13381  in
            (FStar_Errors.Fatal_MonadAlreadyDefined, uu____13379)  in
          let uu____13392 = FStar_Ident.range_of_id mname  in
          FStar_Errors.raise_error uu____13373 uu____13392
      | FStar_Pervasives_Native.None  ->
          let uu___1495_13393 = env1  in
          {
            curmodule = (uu___1495_13393.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1495_13393.modules);
            scope_mods = (uu___1495_13393.scope_mods);
            exported_ids = (uu___1495_13393.exported_ids);
            trans_exported_ids = (uu___1495_13393.trans_exported_ids);
            includes = (uu___1495_13393.includes);
            sigaccum = (uu___1495_13393.sigaccum);
            sigmap = (uu___1495_13393.sigmap);
            iface = (uu___1495_13393.iface);
            admitted_iface = (uu___1495_13393.admitted_iface);
            expect_typ = (uu___1495_13393.expect_typ);
            remaining_iface_decls = (uu___1495_13393.remaining_iface_decls);
            syntax_only = (uu___1495_13393.syntax_only);
            ds_hooks = (uu___1495_13393.ds_hooks);
            dep_graph = (uu___1495_13393.dep_graph)
          }
  
let fail_or :
  'a .
    env ->
      (FStar_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStar_Ident.lident -> 'a
  =
  fun env1  ->
    fun lookup  ->
      fun lid  ->
        let uu____13428 = lookup lid  in
        match uu____13428 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____13443  ->
                   match uu____13443 with
                   | (lid1,uu____13450) -> FStar_Ident.string_of_lid lid1)
                env1.modules
               in
            let msg =
              let uu____13453 = FStar_Ident.string_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13453  in
            let msg1 =
              let uu____13458 =
                let uu____13460 =
                  let uu____13462 = FStar_Ident.ns_of_lid lid  in
                  FStar_List.length uu____13462  in
                uu____13460 = Prims.int_zero  in
              if uu____13458
              then msg
              else
                (let modul =
                   let uu____13472 =
                     let uu____13473 = FStar_Ident.ns_of_lid lid  in
                     FStar_Ident.lid_of_ids uu____13473  in
                   let uu____13474 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____13472 uu____13474  in
                 let uu____13475 = resolve_module_name env1 modul true  in
                 match uu____13475 with
                 | FStar_Pervasives_Native.None  ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules  in
                     let uu____13483 = FStar_Ident.string_of_lid modul  in
                     FStar_Util.format3
                       "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                       msg uu____13483 opened_modules1
                 | FStar_Pervasives_Native.Some modul' when
                     Prims.op_Negation
                       (FStar_List.existsb
                          (fun m  ->
                             let uu____13492 =
                               FStar_Ident.string_of_lid modul'  in
                             m = uu____13492) opened_modules)
                     ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules  in
                     let uu____13498 = FStar_Ident.string_of_lid modul  in
                     let uu____13500 = FStar_Ident.string_of_lid modul'  in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                       msg uu____13498 uu____13500 opened_modules1
                 | FStar_Pervasives_Native.Some modul' ->
                     let uu____13504 = FStar_Ident.string_of_lid modul  in
                     let uu____13506 = FStar_Ident.string_of_lid modul'  in
                     let uu____13508 =
                       let uu____13510 = FStar_Ident.ident_of_lid lid  in
                       FStar_Ident.text_of_id uu____13510  in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, definition %s not found"
                       msg uu____13504 uu____13506 uu____13508)
               in
            let uu____13512 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13512
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup  ->
    fun id  ->
      let uu____13542 = lookup id  in
      match uu____13542 with
      | FStar_Pervasives_Native.None  ->
          let uu____13545 =
            let uu____13551 =
              let uu____13553 =
                let uu____13555 = FStar_Ident.text_of_id id  in
                Prims.op_Hat uu____13555 "]"  in
              Prims.op_Hat "Identifier not found [" uu____13553  in
            (FStar_Errors.Fatal_IdentifierNotFound, uu____13551)  in
          let uu____13560 = FStar_Ident.range_of_id id  in
          FStar_Errors.raise_error uu____13545 uu____13560
      | FStar_Pervasives_Native.Some r -> r
  