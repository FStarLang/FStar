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
  FStar_Syntax_Util.qual_id 
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
      let id =
        let uu___211_2775 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___211_2775.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___214_2776 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___214_2776.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___214_2776.FStar_Syntax_Syntax.sort)
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
  fun id  ->
    FStar_Util.find_map unmangleMap
      (fun uu____2879  ->
         match uu____2879 with
         | (x,y,dd,dq) ->
             if id.FStar_Ident.idText = x
             then
               let uu____2910 =
                 let uu____2911 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____2911 dd dq  in
               FStar_Pervasives_Native.Some uu____2910
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____2951 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2988 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____3009 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___1_3039  ->
      match uu___1_3039 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'uuuuuu3058 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'uuuuuu3058 cont_t) -> 'uuuuuu3058 cont_t
  =
  fun ns  ->
    fun id  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____3095 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____3095
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id])
               in
            let find =
              FStar_Util.find_map record.fields
                (fun uu____3111  ->
                   match uu____3111 with
                   | (f,uu____3119) ->
                       if id.FStar_Ident.idText = f.FStar_Ident.idText
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
  fun uu___2_3193  ->
    match uu___2_3193 with
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
              let idstr = id.FStar_Ident.idText  in
              let rec aux uu___3_3269 =
                match uu___3_3269 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____3282 = get_exported_id_set env1 mname  in
                      match uu____3282 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____3309 = mex eikind  in
                            FStar_ST.op_Bang uu____3309  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____3371 =
                        FStar_Util.smap_try_find env1.includes mname  in
                      match uu____3371 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3426 = qual modul id  in
                        find_in_module uu____3426
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3431 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___4_3440  ->
    match uu___4_3440 with | Exported_id_field  -> true | uu____3443 -> false
  
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
                  let check_local_binding_id uu___5_3567 =
                    match uu___5_3567 with
                    | (id',uu____3570,uu____3571) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___6_3579 =
                    match uu___6_3579 with
                    | (id',uu____3582,uu____3583,uu____3584) ->
                        id'.FStar_Ident.idText = id.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3589 = current_module env1  in
                    FStar_Ident.ids_of_lid uu____3589  in
                  let proc uu___7_3597 =
                    match uu___7_3597 with
                    | Local_binding l when check_local_binding_id l ->
                        let uu____3601 = l  in
                        (match uu____3601 with
                         | (uu____3604,uu____3605,used_marker1) ->
                             (FStar_ST.op_Colon_Equals used_marker1 true;
                              k_local_binding l))
                    | Rec_binding r when check_rec_binding_id r ->
                        let uu____3631 = r  in
                        (match uu____3631 with
                         | (uu____3634,uu____3635,uu____3636,used_marker1) ->
                             (FStar_ST.op_Colon_Equals used_marker1 true;
                              k_rec_binding r))
                    | Open_module_or_namespace (ns,Open_module ) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env1 ns id
                    | Top_level_def id' when
                        id'.FStar_Ident.idText = id.FStar_Ident.idText ->
                        lookup_default_id Cont_ignore id
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____3665 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id1 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id1 r k_record)
                          Cont_ignore env1 uu____3665 id
                    | uu____3670 -> Cont_ignore  in
                  let rec aux uu___8_3680 =
                    match uu___8_3680 with
                    | a::q ->
                        let uu____3689 = proc a  in
                        option_of_cont (fun uu____3693  -> aux q) uu____3689
                    | [] ->
                        let uu____3694 = lookup_default_id Cont_fail id  in
                        option_of_cont
                          (fun uu____3698  -> FStar_Pervasives_Native.None)
                          uu____3694
                     in
                  aux env1.scope_mods
  
let found_local_binding :
  'uuuuuu3708 'uuuuuu3709 .
    FStar_Range.range ->
      ('uuuuuu3708 * FStar_Syntax_Syntax.bv * 'uuuuuu3709) ->
        FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____3725  ->
      match uu____3725 with | (id',x,uu____3734) -> bv_to_name x r
  
let find_in_module :
  'uuuuuu3746 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'uuuuuu3746)
          -> 'uuuuuu3746 -> 'uuuuuu3746
  =
  fun env1  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3787 =
            FStar_Util.smap_try_find (sigmap env1) lid.FStar_Ident.str  in
          match uu____3787 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun id  ->
      let uu____3831 = unmangleOpName id  in
      match uu____3831 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3837 ->
          try_lookup_id'' env1 id Exported_id_term_type
            (fun r  ->
               let uu____3843 = found_local_binding id.FStar_Ident.idRange r
                  in
               Cont_ok uu____3843) (fun uu____3845  -> Cont_fail)
            (fun uu____3847  -> Cont_ignore)
            (fun i  ->
               find_in_module env1 i
                 (fun uu____3854  -> fun uu____3855  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3863  -> fun uu____3864  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____3938 ->
                let lid = qualify env1 id  in
                let uu____3940 =
                  FStar_Util.smap_try_find (sigmap env1) lid.FStar_Ident.str
                   in
                (match uu____3940 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3968 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3968
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v -> v
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____3992 = current_module env1  in qual uu____3992 id
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
        let nslen = FStar_List.length lid.FStar_Ident.ns  in
        let rec aux uu___9_4064 =
          match uu___9_4064 with
          | [] ->
              let uu____4069 = module_is_defined env1 lid  in
              if uu____4069
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____4081 =
                  let uu____4082 = FStar_Ident.path_of_lid ns  in
                  let uu____4086 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____4082 uu____4086  in
                let uu____4091 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____4081 uu____4091  in
              let uu____4092 = module_is_defined env1 new_lid  in
              if uu____4092
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____4101 when
              (nslen = Prims.int_zero) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____4107::q -> aux q  in
        aux env1.scope_mods
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      fun open_kind1  ->
        FStar_List.existsb
          (fun uu___10_4131  ->
             match uu___10_4131 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind1) && (FStar_Ident.lid_equals lid ns)
             | uu____4135 -> false) env1.scope_mods
  
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
                 let uu____4264 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____4264
                   (FStar_Util.map_option
                      (fun uu____4314  ->
                         match uu____4314 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids)))))
           in
        let do_shorten env2 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4384 = aux ns_rev_prefix ns_last_id  in
              (match uu____4384 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > Prims.int_zero)
        then
          let uu____4447 =
            let uu____4450 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env1 uu____4450 true  in
          match uu____4447 with
          | FStar_Pervasives_Native.Some m when module_is_open env1 m ->
              (ids, [])
          | uu____4465 -> do_shorten env1 ids
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
                  match lid.FStar_Ident.ns with
                  | uu____4586::uu____4587 ->
                      let uu____4590 =
                        let uu____4593 =
                          let uu____4594 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4595 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4594 uu____4595  in
                        resolve_module_name env1 uu____4593 true  in
                      (match uu____4590 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4600 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env1 modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4604  -> FStar_Pervasives_Native.None)
                             uu____4600)
                  | [] ->
                      try_lookup_id'' env1 lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___11_4628  ->
      match uu___11_4628 with
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
              let uu____4749 = k_global_def lid1 def  in
              cont_of_option k uu____4749  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env1 lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env1 i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env1 lid Exported_id_term_type
              (fun l  ->
                 let uu____4785 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4785)
              (fun r  ->
                 let uu____4791 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4791)
              (fun uu____4795  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4806,uu____4807,uu____4808,l,uu____4810,uu____4811) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___12_4824  ->
               match uu___12_4824 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4827,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4839 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4845,uu____4846,uu____4847)
        -> FStar_Pervasives_Native.None
    | uu____4848 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4864 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4872 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4872
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4864 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4895 =
         let uu____4896 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4896  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4895) &&
        (let uu____4900 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4900 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____4917 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___13_4924  ->
                     match uu___13_4924 with
                     | FStar_Syntax_Syntax.Projector uu____4926 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____4932 -> true
                     | uu____4934 -> false)))
           in
        if uu____4917
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____4939 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___14_4945  ->
                 match uu___14_4945 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____4948 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___15_4954  ->
                    match uu___15_4954 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____4957 -> false)))
             &&
             (let uu____4960 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___16_4966  ->
                        match uu___16_4966 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____4969 -> false))
                 in
              Prims.op_Negation uu____4960))
         in
      if uu____4939 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___19_5021 =
            match uu___19_5021 with
            | (uu____5029,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____5033) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____5038 ->
                     let uu____5055 =
                       let uu____5056 =
                         let uu____5063 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____5063, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____5056  in
                     FStar_Pervasives_Native.Some uu____5055
                 | FStar_Syntax_Syntax.Sig_datacon uu____5066 ->
                     let uu____5082 =
                       let uu____5083 =
                         let uu____5090 =
                           let uu____5091 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____5091
                            in
                         (uu____5090, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____5083  in
                     FStar_Pervasives_Native.Some uu____5082
                 | FStar_Syntax_Syntax.Sig_let ((uu____5096,lbs),uu____5098)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____5110 =
                       let uu____5111 =
                         let uu____5118 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____5118, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____5111  in
                     FStar_Pervasives_Native.Some uu____5110
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____5122,uu____5123) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____5127 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___17_5133  ->
                                  match uu___17_5133 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____5136 -> false)))
                        in
                     if uu____5127
                     then
                       let lid2 =
                         let uu____5142 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____5142  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____5144 =
                         FStar_Util.find_map quals
                           (fun uu___18_5149  ->
                              match uu___18_5149 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____5153 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____5144 with
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
                        | uu____5162 ->
                            let uu____5165 =
                              let uu____5166 =
                                let uu____5173 =
                                  let uu____5174 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____5174
                                   in
                                (uu____5173,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____5166  in
                            FStar_Pervasives_Native.Some uu____5165)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5182 =
                       let uu____5183 =
                         let uu____5188 =
                           let uu____5189 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____5189
                            in
                         (se, uu____5188)  in
                       Eff_name uu____5183  in
                     FStar_Pervasives_Native.Some uu____5182
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5190 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____5209 =
                       let uu____5210 =
                         let uu____5217 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                Prims.int_one) FStar_Pervasives_Native.None
                            in
                         (uu____5217, [])  in
                       Term_name uu____5210  in
                     FStar_Pervasives_Native.Some uu____5209
                 | uu____5221 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____5243 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____5243 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____5301 =
            match uu____5301 with
            | (id,l,dd,used_marker1) ->
                (FStar_ST.op_Colon_Equals used_marker1 true;
                 (let uu____5459 =
                    let uu____5460 =
                      let uu____5467 =
                        let uu____5468 =
                          let uu____5469 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range l uu____5469  in
                        FStar_Syntax_Syntax.fvar uu____5468 dd
                          FStar_Pervasives_Native.None
                         in
                      (uu____5467, [])  in
                    Term_name uu____5460  in
                  FStar_Pervasives_Native.Some uu____5459))
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____5477 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____5477 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____5485 -> FStar_Pervasives_Native.None)
            | uu____5488 -> FStar_Pervasives_Native.None  in
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
        let uu____5526 = try_lookup_name true exclude_interf env1 lid  in
        match uu____5526 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____5542 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____5562 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l  in
      match uu____5562 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5577 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____5603 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l  in
      match uu____5603 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5619;
             FStar_Syntax_Syntax.sigquals = uu____5620;
             FStar_Syntax_Syntax.sigmeta = uu____5621;
             FStar_Syntax_Syntax.sigattrs = uu____5622;
             FStar_Syntax_Syntax.sigopts = uu____5623;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5643,uu____5644,uu____5645,uu____5646,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5648;
             FStar_Syntax_Syntax.sigquals = uu____5649;
             FStar_Syntax_Syntax.sigmeta = uu____5650;
             FStar_Syntax_Syntax.sigattrs = uu____5651;
             FStar_Syntax_Syntax.sigopts = uu____5652;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5676 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____5702 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l  in
      match uu____5702 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5712;
             FStar_Syntax_Syntax.sigquals = uu____5713;
             FStar_Syntax_Syntax.sigmeta = uu____5714;
             FStar_Syntax_Syntax.sigattrs = uu____5715;
             FStar_Syntax_Syntax.sigopts = uu____5716;_},uu____5717)
          -> FStar_Pervasives_Native.Some ne
      | uu____5728 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____5747 = try_lookup_effect_name env1 lid  in
      match uu____5747 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5752 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____5767 =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l  in
      match uu____5767 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5777,uu____5778,uu____5779,uu____5780);
             FStar_Syntax_Syntax.sigrng = uu____5781;
             FStar_Syntax_Syntax.sigquals = uu____5782;
             FStar_Syntax_Syntax.sigmeta = uu____5783;
             FStar_Syntax_Syntax.sigattrs = uu____5784;
             FStar_Syntax_Syntax.sigopts = uu____5785;_},uu____5786)
          ->
          let rec aux new_name =
            let uu____5809 =
              FStar_Util.smap_try_find (sigmap env1) new_name.FStar_Ident.str
               in
            match uu____5809 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5830) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5841 =
                       let uu____5842 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5842
                        in
                     FStar_Pervasives_Native.Some uu____5841
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5843,uu____5844,uu____5845,cmp,uu____5847) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5853 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5854,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5860 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals_and_attrs :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.qualifier Prims.list *
        FStar_Syntax_Syntax.attribute Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let k_global_def lid1 uu___20_5911 =
        match uu___20_5911 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5927,uu____5928,uu____5929);
             FStar_Syntax_Syntax.sigrng = uu____5930;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5932;
             FStar_Syntax_Syntax.sigattrs = attrs;
             FStar_Syntax_Syntax.sigopts = uu____5934;_},uu____5935)
            -> FStar_Pervasives_Native.Some (quals, attrs)
        | uu____5956 -> FStar_Pervasives_Native.None  in
      let uu____5970 =
        resolve_in_open_namespaces' env1 lid
          (fun uu____5990  -> FStar_Pervasives_Native.None)
          (fun uu____6000  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5970 with
      | FStar_Pervasives_Native.Some qa -> qa
      | uu____6034 -> ([], [])
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun path  ->
      let uu____6062 =
        FStar_List.tryFind
          (fun uu____6077  ->
             match uu____6077 with
             | (mlid,modul) ->
                 let uu____6085 = FStar_Ident.path_of_lid mlid  in
                 uu____6085 = path) env1.modules
         in
      match uu____6062 with
      | FStar_Pervasives_Native.Some (uu____6088,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let k_global_def lid1 uu___21_6128 =
        match uu___21_6128 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____6136,lbs),uu____6138);
             FStar_Syntax_Syntax.sigrng = uu____6139;
             FStar_Syntax_Syntax.sigquals = uu____6140;
             FStar_Syntax_Syntax.sigmeta = uu____6141;
             FStar_Syntax_Syntax.sigattrs = uu____6142;
             FStar_Syntax_Syntax.sigopts = uu____6143;_},uu____6144)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____6164 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____6164
        | uu____6165 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6172  -> FStar_Pervasives_Native.None)
        (fun uu____6174  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let k_global_def lid1 uu___22_6207 =
        match uu___22_6207 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____6218);
             FStar_Syntax_Syntax.sigrng = uu____6219;
             FStar_Syntax_Syntax.sigquals = uu____6220;
             FStar_Syntax_Syntax.sigmeta = uu____6221;
             FStar_Syntax_Syntax.sigattrs = uu____6222;
             FStar_Syntax_Syntax.sigopts = uu____6223;_},uu____6224)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____6252 -> FStar_Pervasives_Native.None)
        | uu____6259 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6270  -> FStar_Pervasives_Native.None)
        (fun uu____6274  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____6334 = try_lookup_name any_val exclude_interface env1 lid
             in
          match uu____6334 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____6359 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____6397) ->
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
      let uu____6455 = try_lookup_lid_with_attributes env1 l  in
      FStar_All.pipe_right uu____6455 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____6487 = try_lookup_lid env1 l  in
      match uu____6487 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____6493 =
            let uu____6494 = FStar_Syntax_Subst.compress e  in
            uu____6494.FStar_Syntax_Syntax.n  in
          (match uu____6493 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____6500 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____6512 = shorten_module_path env1 lid.FStar_Ident.ns true  in
      match uu____6512 with
      | (uu____6522,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env1  ->
    fun lid  ->
      match env1.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env1 lid
      | uu____6543 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____6547 =
            resolve_to_fully_qualified_name env1 lid_without_ns  in
          (match uu____6547 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____6552 -> shorten_lid' env1 lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let env' =
        let uu___869_6583 = env1  in
        {
          curmodule = (uu___869_6583.curmodule);
          curmonad = (uu___869_6583.curmonad);
          modules = (uu___869_6583.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___869_6583.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___869_6583.sigaccum);
          sigmap = (uu___869_6583.sigmap);
          iface = (uu___869_6583.iface);
          admitted_iface = (uu___869_6583.admitted_iface);
          expect_typ = (uu___869_6583.expect_typ);
          remaining_iface_decls = (uu___869_6583.remaining_iface_decls);
          syntax_only = (uu___869_6583.syntax_only);
          ds_hooks = (uu___869_6583.ds_hooks);
          dep_graph = (uu___869_6583.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____6599 = try_lookup_lid_with_attributes_no_resolve env1 l  in
      FStar_All.pipe_right uu____6599 drop_attributes
  
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
               (uu____6656,uu____6657,uu____6658);
             FStar_Syntax_Syntax.sigrng = uu____6659;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6661;
             FStar_Syntax_Syntax.sigattrs = uu____6662;
             FStar_Syntax_Syntax.sigopts = uu____6663;_},uu____6664)
            ->
            let uu____6673 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___23_6679  ->
                      match uu___23_6679 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6682 -> false))
               in
            if uu____6673
            then
              let uu____6687 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6687
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6690;
             FStar_Syntax_Syntax.sigrng = uu____6691;
             FStar_Syntax_Syntax.sigquals = uu____6692;
             FStar_Syntax_Syntax.sigmeta = uu____6693;
             FStar_Syntax_Syntax.sigattrs = uu____6694;
             FStar_Syntax_Syntax.sigopts = uu____6695;_},uu____6696)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____6724 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____6724
        | uu____6725 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6732  -> FStar_Pervasives_Native.None)
        (fun uu____6734  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let k_global_def lid1 uu___24_6769 =
        match uu___24_6769 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6779,uu____6780,uu____6781,uu____6782,datas,uu____6784);
             FStar_Syntax_Syntax.sigrng = uu____6785;
             FStar_Syntax_Syntax.sigquals = uu____6786;
             FStar_Syntax_Syntax.sigmeta = uu____6787;
             FStar_Syntax_Syntax.sigattrs = uu____6788;
             FStar_Syntax_Syntax.sigopts = uu____6789;_},uu____6790)
            -> FStar_Pervasives_Native.Some datas
        | uu____6809 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env1 lid
        (fun uu____6820  -> FStar_Pervasives_Native.None)
        (fun uu____6824  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push uu____6903 =
    let uu____6904 =
      let uu____6909 =
        let uu____6912 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6912  in
      let uu____6946 = FStar_ST.op_Bang record_cache  in uu____6909 ::
        uu____6946
       in
    FStar_ST.op_Colon_Equals record_cache uu____6904  in
  let pop uu____7012 =
    let uu____7013 =
      let uu____7018 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____7018  in
    FStar_ST.op_Colon_Equals record_cache uu____7013  in
  let snapshot uu____7089 = FStar_Common.snapshot push record_cache ()  in
  let rollback depth = FStar_Common.rollback pop record_cache depth  in
  let peek uu____7113 =
    let uu____7114 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____7114  in
  let insert r =
    let uu____7154 =
      let uu____7159 = let uu____7162 = peek ()  in r :: uu____7162  in
      let uu____7165 =
        let uu____7170 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____7170  in
      uu____7159 :: uu____7165  in
    FStar_ST.op_Colon_Equals record_cache uu____7154  in
  let filter uu____7238 =
    let rc = peek ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____7247 =
      let uu____7252 =
        let uu____7257 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____7257  in
      filtered :: uu____7252  in
    FStar_ST.op_Colon_Equals record_cache uu____7247  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____8183) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___25_8202  ->
                   match uu___25_8202 with
                   | FStar_Syntax_Syntax.RecordType uu____8204 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____8214 -> true
                   | uu____8224 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___26_8250  ->
                      match uu___26_8250 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____8253,uu____8254,uu____8255,uu____8256,uu____8257);
                          FStar_Syntax_Syntax.sigrng = uu____8258;
                          FStar_Syntax_Syntax.sigquals = uu____8259;
                          FStar_Syntax_Syntax.sigmeta = uu____8260;
                          FStar_Syntax_Syntax.sigattrs = uu____8261;
                          FStar_Syntax_Syntax.sigopts = uu____8262;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____8275 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___27_8313  ->
                    match uu___27_8313 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____8317,uu____8318,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____8320;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____8322;
                        FStar_Syntax_Syntax.sigattrs = uu____8323;
                        FStar_Syntax_Syntax.sigopts = uu____8324;_} ->
                        let uu____8337 =
                          let uu____8338 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____8338  in
                        (match uu____8337 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____8344,t,uu____8346,uu____8347,uu____8348);
                             FStar_Syntax_Syntax.sigrng = uu____8349;
                             FStar_Syntax_Syntax.sigquals = uu____8350;
                             FStar_Syntax_Syntax.sigmeta = uu____8351;
                             FStar_Syntax_Syntax.sigattrs = uu____8352;
                             FStar_Syntax_Syntax.sigopts = uu____8353;_} ->
                             let uu____8366 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____8366 with
                              | (formals,uu____8374) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____8412  ->
                                            match uu____8412 with
                                            | (x,q) ->
                                                let uu____8425 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____8425
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____8480  ->
                                            match uu____8480 with
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
                                  ((let uu____8504 =
                                      let uu____8507 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____8507  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____8504);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____8566 =
                                            match uu____8566 with
                                            | (id,uu____8572) ->
                                                let modul =
                                                  let uu____8575 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____8575.FStar_Ident.str
                                                   in
                                                let uu____8576 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____8576 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____8599 =
                                                         let uu____8600 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____8600
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8599);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8645 =
                                                               let uu____8646
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id
                                                                  in
                                                               uu____8646.FStar_Ident.ident
                                                                in
                                                             uu____8645.FStar_Ident.idText
                                                              in
                                                           let uu____8648 =
                                                             let uu____8649 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8649
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8648))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8701 -> ())
                    | uu____8702 -> ()))
        | uu____8703 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env1  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8725 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8725 with
        | (ns,id) ->
            let uu____8742 = peek_record_cache ()  in
            FStar_Util.find_map uu____8742
              (fun record  ->
                 let uu____8748 =
                   find_in_record ns id record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8754  -> FStar_Pervasives_Native.None)
                   uu____8748)
         in
      resolve_in_open_namespaces'' env1 fieldname Exported_id_field
        (fun uu____8756  -> Cont_ignore) (fun uu____8758  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8764 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8764)
        (fun k  -> fun uu____8770  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env1  ->
    fun fieldname  ->
      let uu____8786 = try_lookup_record_or_dc_by_field_name env1 fieldname
         in
      match uu____8786 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____8792 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      fun record  ->
        let uu____8812 = try_lookup_record_by_field_name env1 lid  in
        match uu____8812 with
        | FStar_Pervasives_Native.Some record' when
            let uu____8817 =
              let uu____8819 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8819  in
            let uu____8820 =
              let uu____8822 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____8822  in
            uu____8817 = uu____8820 ->
            let uu____8824 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____8828  -> Cont_ok ())
               in
            (match uu____8824 with
             | Cont_ok uu____8830 -> true
             | uu____8832 -> false)
        | uu____8836 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fieldname  ->
      let uu____8858 = try_lookup_record_or_dc_by_field_name env1 fieldname
         in
      match uu____8858 with
      | FStar_Pervasives_Native.Some r ->
          let uu____8869 =
            let uu____8875 =
              let uu____8876 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____8877 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____8876 uu____8877  in
            (uu____8875, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____8869
      | uu____8884 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8902  ->
    let uu____8903 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____8903
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____8924  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___28_8937  ->
      match uu___28_8937 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env1  ->
        fun lid  ->
          let filter_scope_mods uu___29_8975 =
            match uu___29_8975 with
            | Rec_binding uu____8977 -> true
            | uu____8979 -> false  in
          let this_env =
            let uu___1099_8982 = env1  in
            let uu____8983 =
              FStar_List.filter filter_scope_mods env1.scope_mods  in
            {
              curmodule = (uu___1099_8982.curmodule);
              curmonad = (uu___1099_8982.curmonad);
              modules = (uu___1099_8982.modules);
              scope_mods = uu____8983;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1099_8982.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1099_8982.sigaccum);
              sigmap = (uu___1099_8982.sigmap);
              iface = (uu___1099_8982.iface);
              admitted_iface = (uu___1099_8982.admitted_iface);
              expect_typ = (uu___1099_8982.expect_typ);
              remaining_iface_decls = (uu___1099_8982.remaining_iface_decls);
              syntax_only = (uu___1099_8982.syntax_only);
              ds_hooks = (uu___1099_8982.ds_hooks);
              dep_graph = (uu___1099_8982.dep_graph)
            }  in
          let uu____8986 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____8986 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____9003 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env1  ->
    fun scope_mod1  ->
      let uu___1107_9028 = env1  in
      {
        curmodule = (uu___1107_9028.curmodule);
        curmonad = (uu___1107_9028.curmonad);
        modules = (uu___1107_9028.modules);
        scope_mods = (scope_mod1 :: (env1.scope_mods));
        exported_ids = (uu___1107_9028.exported_ids);
        trans_exported_ids = (uu___1107_9028.trans_exported_ids);
        includes = (uu___1107_9028.includes);
        sigaccum = (uu___1107_9028.sigaccum);
        sigmap = (uu___1107_9028.sigmap);
        iface = (uu___1107_9028.iface);
        admitted_iface = (uu___1107_9028.admitted_iface);
        expect_typ = (uu___1107_9028.expect_typ);
        remaining_iface_decls = (uu___1107_9028.remaining_iface_decls);
        syntax_only = (uu___1107_9028.syntax_only);
        ds_hooks = (uu___1107_9028.ds_hooks);
        dep_graph = (uu___1107_9028.dep_graph)
      }
  
let (push_bv' :
  env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv * used_marker)) =
  fun env1  ->
    fun x  ->
      let bv =
        FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
          (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange))
          FStar_Syntax_Syntax.tun
         in
      let used_marker1 = FStar_Util.mk_ref false  in
      ((push_scope_mod env1 (Local_binding (x, bv, used_marker1))), bv,
        used_marker1)
  
let (push_bv : env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv)) =
  fun env1  ->
    fun x  ->
      let uu____9068 = push_bv' env1 x  in
      match uu____9068 with | (env2,bv,uu____9081) -> (env2, bv)
  
let (push_top_level_rec_binding :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.delta_depth -> (env * Prims.bool FStar_ST.ref))
  =
  fun env0  ->
    fun x  ->
      fun dd  ->
        let l = qualify env0 x  in
        let uu____9113 =
          (unique false true env0 l) || (FStar_Options.interactive ())  in
        if uu____9113
        then
          let used_marker1 = FStar_Util.mk_ref false  in
          ((push_scope_mod env0 (Rec_binding (x, l, dd, used_marker1))),
            used_marker1)
        else
          (let uu____9136 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____9136)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env1  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env1) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____9187) ->
                let uu____9195 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____9195 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____9200 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____9200
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____9209 =
            let uu____9215 =
              let uu____9217 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____9217 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____9215)  in
          let uu____9221 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____9209 uu____9221  in
        let globals = FStar_Util.mk_ref env1.scope_mods  in
        let env2 =
          let uu____9230 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____9243 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____9254 -> (false, true)
            | uu____9267 -> (false, false)  in
          match uu____9230 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____9281 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____9287 =
                       let uu____9289 =
                         unique any_val exclude_interface env1 l  in
                       Prims.op_Negation uu____9289  in
                     if uu____9287
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____9281 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____9297 ->
                   (extract_record env1 globals s;
                    (let uu___1156_9301 = env1  in
                     {
                       curmodule = (uu___1156_9301.curmodule);
                       curmonad = (uu___1156_9301.curmonad);
                       modules = (uu___1156_9301.modules);
                       scope_mods = (uu___1156_9301.scope_mods);
                       exported_ids = (uu___1156_9301.exported_ids);
                       trans_exported_ids =
                         (uu___1156_9301.trans_exported_ids);
                       includes = (uu___1156_9301.includes);
                       sigaccum = (s :: (env1.sigaccum));
                       sigmap = (uu___1156_9301.sigmap);
                       iface = (uu___1156_9301.iface);
                       admitted_iface = (uu___1156_9301.admitted_iface);
                       expect_typ = (uu___1156_9301.expect_typ);
                       remaining_iface_decls =
                         (uu___1156_9301.remaining_iface_decls);
                       syntax_only = (uu___1156_9301.syntax_only);
                       ds_hooks = (uu___1156_9301.ds_hooks);
                       dep_graph = (uu___1156_9301.dep_graph)
                     })))
           in
        let env3 =
          let uu___1159_9303 = env2  in
          let uu____9304 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1159_9303.curmodule);
            curmonad = (uu___1159_9303.curmonad);
            modules = (uu___1159_9303.modules);
            scope_mods = uu____9304;
            exported_ids = (uu___1159_9303.exported_ids);
            trans_exported_ids = (uu___1159_9303.trans_exported_ids);
            includes = (uu___1159_9303.includes);
            sigaccum = (uu___1159_9303.sigaccum);
            sigmap = (uu___1159_9303.sigmap);
            iface = (uu___1159_9303.iface);
            admitted_iface = (uu___1159_9303.admitted_iface);
            expect_typ = (uu___1159_9303.expect_typ);
            remaining_iface_decls = (uu___1159_9303.remaining_iface_decls);
            syntax_only = (uu___1159_9303.syntax_only);
            ds_hooks = (uu___1159_9303.ds_hooks);
            dep_graph = (uu___1159_9303.dep_graph)
          }  in
        let uu____9330 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9356) ->
              let uu____9365 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env3, uu____9365)
          | uu____9392 -> (env3, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____9330 with
        | (env4,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____9451  ->
                     match uu____9451 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____9473 =
                                    let uu____9476 = FStar_ST.op_Bang globals
                                       in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____9476
                                     in
                                  FStar_ST.op_Colon_Equals globals uu____9473);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____9527 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____9527.FStar_Ident.str  in
                                      ((let uu____9529 =
                                          get_exported_id_set env4 modul  in
                                        match uu____9529 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____9551 =
                                              let uu____9552 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____9552
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____9551
                                        | FStar_Pervasives_Native.None  -> ());
                                       (match () with
                                        | () ->
                                            let is_iface =
                                              env4.iface &&
                                                (Prims.op_Negation
                                                   env4.admitted_iface)
                                               in
                                            FStar_Util.smap_add (sigmap env4)
                                              lid.FStar_Ident.str
                                              (se,
                                                (env4.iface &&
                                                   (Prims.op_Negation
                                                      env4.admitted_iface))))))))));
             (let env5 =
                let uu___1184_9609 = env4  in
                let uu____9610 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1184_9609.curmodule);
                  curmonad = (uu___1184_9609.curmonad);
                  modules = (uu___1184_9609.modules);
                  scope_mods = uu____9610;
                  exported_ids = (uu___1184_9609.exported_ids);
                  trans_exported_ids = (uu___1184_9609.trans_exported_ids);
                  includes = (uu___1184_9609.includes);
                  sigaccum = (uu___1184_9609.sigaccum);
                  sigmap = (uu___1184_9609.sigmap);
                  iface = (uu___1184_9609.iface);
                  admitted_iface = (uu___1184_9609.admitted_iface);
                  expect_typ = (uu___1184_9609.expect_typ);
                  remaining_iface_decls =
                    (uu___1184_9609.remaining_iface_decls);
                  syntax_only = (uu___1184_9609.syntax_only);
                  ds_hooks = (uu___1184_9609.ds_hooks);
                  dep_graph = (uu___1184_9609.dep_graph)
                }  in
              env5))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  -> fun se  -> push_sigelt' true env1 se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  -> fun se  -> push_sigelt' false env1 se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun ns  ->
      let uu____9671 =
        let uu____9676 = resolve_module_name env1 ns false  in
        match uu____9676 with
        | FStar_Pervasives_Native.None  ->
            let modules = env1.modules  in
            let uu____9691 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____9709  ->
                      match uu____9709 with
                      | (m,uu____9716) ->
                          let uu____9717 =
                            let uu____9719 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____9719 "."  in
                          let uu____9722 =
                            let uu____9724 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____9724 "."  in
                          FStar_Util.starts_with uu____9717 uu____9722))
               in
            if uu____9691
            then (ns, Open_namespace)
            else
              (let uu____9734 =
                 let uu____9740 =
                   let uu____9742 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____9742
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____9740)  in
               let uu____9746 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____9734 uu____9746)
        | FStar_Pervasives_Native.Some ns' -> (ns', Open_module)  in
      match uu____9671 with
      | (ns',kd) ->
          ((env1.ds_hooks).ds_push_open_hook env1 (ns', kd);
           push_scope_mod env1 (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____9767 = resolve_module_name env1 ns false  in
      match uu____9767 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env1.ds_hooks).ds_push_include_hook env1 ns1;
           (let env2 =
              push_scope_mod env1
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____9776 = current_module env2  in
              uu____9776.FStar_Ident.str  in
            (let uu____9778 = FStar_Util.smap_try_find env2.includes curmod
                in
             match uu____9778 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____9802 =
                   let uu____9805 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____9805
                    in
                 FStar_ST.op_Colon_Equals incl uu____9802);
            (match () with
             | () ->
                 let uu____9854 =
                   get_trans_exported_id_set env2 ns1.FStar_Ident.str  in
                 (match uu____9854 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____9874 =
                          let uu____9971 = get_exported_id_set env2 curmod
                             in
                          let uu____10018 =
                            get_trans_exported_id_set env2 curmod  in
                          (uu____9971, uu____10018)  in
                        match uu____9874 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10434 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10434  in
                              let ex = cur_exports k  in
                              (let uu____10535 =
                                 let uu____10539 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____10539 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____10535);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____10631 =
                                     let uu____10635 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____10635 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____10631)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____10684 -> ());
                       (match () with | () -> env2))
                  | FStar_Pervasives_Native.None  ->
                      let uu____10786 =
                        let uu____10792 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____10792)
                         in
                      let uu____10796 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____10786 uu____10796))))
      | uu____10797 ->
          let uu____10800 =
            let uu____10806 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____10806)  in
          let uu____10810 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____10800 uu____10810
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun x  ->
      fun l  ->
        let uu____10827 = module_is_defined env1 l  in
        if uu____10827
        then
          ((env1.ds_hooks).ds_push_module_abbrev_hook env1 x l;
           push_scope_mod env1 (Module_abbrev (x, l)))
        else
          (let uu____10833 =
             let uu____10839 =
               let uu____10841 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____10841  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____10839)  in
           let uu____10845 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____10833 uu____10845)
  
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
                      let uu____10888 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____10888 ->
                      let uu____10893 =
                        FStar_Util.smap_try_find (sigmap env1)
                          l.FStar_Ident.str
                         in
                      (match uu____10893 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____10908;
                              FStar_Syntax_Syntax.sigrng = uu____10909;
                              FStar_Syntax_Syntax.sigquals = uu____10910;
                              FStar_Syntax_Syntax.sigmeta = uu____10911;
                              FStar_Syntax_Syntax.sigattrs = uu____10912;
                              FStar_Syntax_Syntax.sigopts = uu____10913;_},uu____10914)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____10934;
                              FStar_Syntax_Syntax.sigrng = uu____10935;
                              FStar_Syntax_Syntax.sigquals = uu____10936;
                              FStar_Syntax_Syntax.sigmeta = uu____10937;
                              FStar_Syntax_Syntax.sigattrs = uu____10938;
                              FStar_Syntax_Syntax.sigopts = uu____10939;_},uu____10940)
                           -> lids
                       | uu____10970 ->
                           ((let uu____10979 =
                               let uu____10981 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____10981  in
                             if uu____10979
                             then
                               let uu____10984 = FStar_Ident.range_of_lid l
                                  in
                               let uu____10985 =
                                 let uu____10991 =
                                   let uu____10993 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____10993
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____10991)
                                  in
                               FStar_Errors.log_issue uu____10984 uu____10985
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env1)
                               l.FStar_Ident.str
                               ((let uu___1275_11010 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1275_11010.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1275_11010.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1275_11010.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1275_11010.FStar_Syntax_Syntax.sigattrs);
                                   FStar_Syntax_Syntax.sigopts =
                                     (uu___1275_11010.FStar_Syntax_Syntax.sigopts)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____11012 -> lids) [])
         in
      let uu___1280_11013 = m  in
      let uu____11014 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____11024,uu____11025) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1289_11028 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1289_11028.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1289_11028.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1289_11028.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1289_11028.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1289_11028.FStar_Syntax_Syntax.sigopts)
                    }
                | uu____11029 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1280_11013.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11014;
        FStar_Syntax_Syntax.exports =
          (uu___1280_11013.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1280_11013.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env1  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11053) ->
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
                                (lid,uu____11074,uu____11075,uu____11076,uu____11077,uu____11078)
                                ->
                                FStar_Util.smap_remove (sigmap env1)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____11094,uu____11095)
                                ->
                                (FStar_Util.smap_remove (sigmap env1)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11112 =
                                        let uu____11119 =
                                          let uu____11120 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____11121 =
                                            let uu____11128 =
                                              let uu____11129 =
                                                let uu____11144 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11144)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11129
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11128
                                             in
                                          uu____11121
                                            FStar_Pervasives_Native.None
                                            uu____11120
                                           in
                                        (lid, univ_names, uu____11119)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11112
                                       in
                                    let se2 =
                                      let uu___1321_11158 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1321_11158.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1321_11158.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1321_11158.FStar_Syntax_Syntax.sigattrs);
                                        FStar_Syntax_Syntax.sigopts =
                                          (uu___1321_11158.FStar_Syntax_Syntax.sigopts)
                                      }  in
                                    FStar_Util.smap_add (sigmap env1)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11168 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11172,uu____11173) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env1) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11182,lbs),uu____11184)
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
                             let uu____11202 =
                               let uu____11204 =
                                 let uu____11205 =
                                   let uu____11208 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11208.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11205.FStar_Syntax_Syntax.v  in
                               uu____11204.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env1) uu____11202))
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
                               let uu____11225 =
                                 let uu____11228 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11228.FStar_Syntax_Syntax.fv_name  in
                               uu____11225.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1344_11233 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1344_11233.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1344_11233.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1344_11233.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___1344_11233.FStar_Syntax_Syntax.sigopts)
                               }  in
                             FStar_Util.smap_add (sigmap env1)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11243 -> ()));
      (let curmod =
         let uu____11246 = current_module env1  in
         uu____11246.FStar_Ident.str  in
       (let uu____11248 =
          let uu____11345 = get_exported_id_set env1 curmod  in
          let uu____11392 = get_trans_exported_id_set env1 curmod  in
          (uu____11345, uu____11392)  in
        match uu____11248 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____11811 = cur_ex eikind  in
                FStar_ST.op_Bang uu____11811  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____11917 =
                let uu____11921 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____11921  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____11917  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____11970 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1362_12068 = env1  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1362_12068.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env1.modules));
                    scope_mods = [];
                    exported_ids = (uu___1362_12068.exported_ids);
                    trans_exported_ids = (uu___1362_12068.trans_exported_ids);
                    includes = (uu___1362_12068.includes);
                    sigaccum = [];
                    sigmap = (uu___1362_12068.sigmap);
                    iface = (uu___1362_12068.iface);
                    admitted_iface = (uu___1362_12068.admitted_iface);
                    expect_typ = (uu___1362_12068.expect_typ);
                    remaining_iface_decls =
                      (uu___1362_12068.remaining_iface_decls);
                    syntax_only = (uu___1362_12068.syntax_only);
                    ds_hooks = (uu___1362_12068.ds_hooks);
                    dep_graph = (uu___1362_12068.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env1  ->
    FStar_Util.atomically
      (fun uu____12094  ->
         push_record_cache ();
         (let uu____12097 =
            let uu____12100 = FStar_ST.op_Bang stack  in env1 :: uu____12100
             in
          FStar_ST.op_Colon_Equals stack uu____12097);
         (let uu___1368_12149 = env1  in
          let uu____12150 = FStar_Util.smap_copy env1.exported_ids  in
          let uu____12155 = FStar_Util.smap_copy env1.trans_exported_ids  in
          let uu____12160 = FStar_Util.smap_copy env1.includes  in
          let uu____12171 = FStar_Util.smap_copy env1.sigmap  in
          {
            curmodule = (uu___1368_12149.curmodule);
            curmonad = (uu___1368_12149.curmonad);
            modules = (uu___1368_12149.modules);
            scope_mods = (uu___1368_12149.scope_mods);
            exported_ids = uu____12150;
            trans_exported_ids = uu____12155;
            includes = uu____12160;
            sigaccum = (uu___1368_12149.sigaccum);
            sigmap = uu____12171;
            iface = (uu___1368_12149.iface);
            admitted_iface = (uu___1368_12149.admitted_iface);
            expect_typ = (uu___1368_12149.expect_typ);
            remaining_iface_decls = (uu___1368_12149.remaining_iface_decls);
            syntax_only = (uu___1368_12149.syntax_only);
            ds_hooks = (uu___1368_12149.ds_hooks);
            dep_graph = (uu___1368_12149.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____12189  ->
    FStar_Util.atomically
      (fun uu____12196  ->
         let uu____12197 = FStar_ST.op_Bang stack  in
         match uu____12197 with
         | env1::tl ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl; env1)
         | uu____12252 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env1  -> FStar_Common.snapshot push stack env1 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env1  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____12299 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____12303 -> false  in
      let sm = sigmap env1  in
      let env2 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env2  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____12345 = FStar_Util.smap_try_find sm' k  in
              match uu____12345 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1403_12376 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1403_12376.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1403_12376.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1403_12376.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1403_12376.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___1403_12376.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____12377 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____12385 -> ()));
      env2
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env1  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env1 modul
        else modul  in
      let uu____12412 = finish env1 modul1  in (uu____12412, modul1)
  
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
      let uu____12481 =
        let uu____12485 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____12485  in
      FStar_Util.set_elements uu____12481  in
    let fields =
      let uu____12548 =
        let uu____12552 = e Exported_id_field  in
        FStar_ST.op_Bang uu____12552  in
      FStar_Util.set_elements uu____12548  in
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
          let uu____12644 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____12644  in
        let fields =
          let uu____12658 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____12658  in
        (fun uu___30_12666  ->
           match uu___30_12666 with
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
  'uuuuuu12770 .
    'uuuuuu12770 Prims.list FStar_Pervasives_Native.option ->
      'uuuuuu12770 Prims.list FStar_ST.ref
  =
  fun uu___31_12783  ->
    match uu___31_12783 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env1  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____12826 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____12826 as_exported_ids  in
      let uu____12832 = as_ids_opt env1.exported_ids  in
      let uu____12835 = as_ids_opt env1.trans_exported_ids  in
      let uu____12838 =
        let uu____12843 = FStar_Util.smap_try_find env1.includes mname  in
        FStar_Util.map_opt uu____12843 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____12832;
        mii_trans_exported_ids = uu____12835;
        mii_includes = uu____12838
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
                let uu____12932 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____12932 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___32_12954 =
                  match uu___32_12954 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____12966  ->
                     match uu____12966 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if (FStar_List.length mname.FStar_Ident.ns) > Prims.int_zero
                then
                  let uu____12992 =
                    let uu____12997 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____12997, Open_namespace)  in
                  [uu____12992]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____13028 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env2.exported_ids mname.FStar_Ident.str
                 uu____13028);
              (match () with
               | () ->
                   ((let uu____13033 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env2.trans_exported_ids
                       mname.FStar_Ident.str uu____13033);
                    (match () with
                     | () ->
                         ((let uu____13038 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env2.includes
                             mname.FStar_Ident.str uu____13038);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1473_13048 = env2  in
                                 let uu____13049 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1473_13048.curmonad);
                                   modules = (uu___1473_13048.modules);
                                   scope_mods = uu____13049;
                                   exported_ids =
                                     (uu___1473_13048.exported_ids);
                                   trans_exported_ids =
                                     (uu___1473_13048.trans_exported_ids);
                                   includes = (uu___1473_13048.includes);
                                   sigaccum = (uu___1473_13048.sigaccum);
                                   sigmap = (env2.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1473_13048.expect_typ);
                                   remaining_iface_decls =
                                     (uu___1473_13048.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1473_13048.syntax_only);
                                   ds_hooks = (uu___1473_13048.ds_hooks);
                                   dep_graph = (uu___1473_13048.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env2.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____13061 =
              FStar_All.pipe_right env1.modules
                (FStar_Util.find_opt
                   (fun uu____13087  ->
                      match uu____13087 with
                      | (l,uu____13094) -> FStar_Ident.lid_equals l mname))
               in
            match uu____13061 with
            | FStar_Pervasives_Native.None  ->
                let uu____13104 = prep env1  in (uu____13104, false)
            | FStar_Pervasives_Native.Some (uu____13107,m) ->
                ((let uu____13114 =
                    (let uu____13118 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____13118) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____13114
                  then
                    let uu____13121 =
                      let uu____13127 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____13127)
                       in
                    let uu____13131 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____13121 uu____13131
                  else ());
                 (let uu____13134 =
                    let uu____13135 = push env1  in prep uu____13135  in
                  (uu____13134, true)))
  
let (enter_monad_scope : env -> FStar_Ident.ident -> env) =
  fun env1  ->
    fun mname  ->
      match env1.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MonadAlreadyDefined,
              (Prims.op_Hat "Trying to define monad "
                 (Prims.op_Hat mname.FStar_Ident.idText
                    (Prims.op_Hat ", but already in monad scope "
                       mname'.FStar_Ident.idText))))
            mname.FStar_Ident.idRange
      | FStar_Pervasives_Native.None  ->
          let uu___1494_13153 = env1  in
          {
            curmodule = (uu___1494_13153.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1494_13153.modules);
            scope_mods = (uu___1494_13153.scope_mods);
            exported_ids = (uu___1494_13153.exported_ids);
            trans_exported_ids = (uu___1494_13153.trans_exported_ids);
            includes = (uu___1494_13153.includes);
            sigaccum = (uu___1494_13153.sigaccum);
            sigmap = (uu___1494_13153.sigmap);
            iface = (uu___1494_13153.iface);
            admitted_iface = (uu___1494_13153.admitted_iface);
            expect_typ = (uu___1494_13153.expect_typ);
            remaining_iface_decls = (uu___1494_13153.remaining_iface_decls);
            syntax_only = (uu___1494_13153.syntax_only);
            ds_hooks = (uu___1494_13153.ds_hooks);
            dep_graph = (uu___1494_13153.dep_graph)
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
        let uu____13188 = lookup lid  in
        match uu____13188 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____13203  ->
                   match uu____13203 with
                   | (lid1,uu____13210) -> FStar_Ident.text_of_lid lid1)
                env1.modules
               in
            let msg =
              let uu____13213 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____13213  in
            let msg1 =
              if (FStar_List.length lid.FStar_Ident.ns) = Prims.int_zero
              then msg
              else
                (let modul =
                   let uu____13225 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____13226 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____13225 uu____13226  in
                 let uu____13227 = resolve_module_name env1 modul true  in
                 match uu____13227 with
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
            let uu____13248 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____13248
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup  ->
    fun id  ->
      let uu____13278 = lookup id  in
      match uu____13278 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id.FStar_Ident.idText "]")))
            id.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  