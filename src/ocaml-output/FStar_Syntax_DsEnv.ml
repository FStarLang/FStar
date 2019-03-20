open Prims
type local_binding = (FStar_Ident.ident * FStar_Syntax_Syntax.bv)
type rec_binding =
  (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth)
type module_abbrev = (FStar_Ident.ident * FStar_Ident.lident)
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____48993 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____49004 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____49224 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____49243 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____49262 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____49281 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____49300 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____49319 -> false
  
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
    | uu____49340 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____49351 -> false
  
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
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap ;
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
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmodule
  
let (__proj__Mkenv__item__curmonad :
  env -> FStar_Ident.ident FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmonad
  
let (__proj__Mkenv__item__modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> modules
  
let (__proj__Mkenv__item__scope_mods : env -> scope_mod Prims.list) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> scope_mods
  
let (__proj__Mkenv__item__exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> exported_ids
  
let (__proj__Mkenv__item__trans_exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> trans_exported_ids
  
let (__proj__Mkenv__item__includes :
  env -> FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> includes
  
let (__proj__Mkenv__item__sigaccum : env -> FStar_Syntax_Syntax.sigelts) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> sigaccum
  
let (__proj__Mkenv__item__sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> sigmap
  
let (__proj__Mkenv__item__iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> iface
  
let (__proj__Mkenv__item__admitted_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> admitted_iface
  
let (__proj__Mkenv__item__expect_typ : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> expect_typ
  
let (__proj__Mkenv__item__docs :
  env -> FStar_Parser_AST.fsdoc FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> docs
  
let (__proj__Mkenv__item__remaining_iface_decls :
  env -> (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> remaining_iface_decls
  
let (__proj__Mkenv__item__syntax_only : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> syntax_only
  
let (__proj__Mkenv__item__ds_hooks : env -> dsenv_hooks) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> ds_hooks
  
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
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
    ds_push_open_hook = (fun uu____50971  -> fun uu____50972  -> ());
    ds_push_include_hook = (fun uu____50975  -> fun uu____50976  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____50980  -> fun uu____50981  -> fun uu____50982  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____51019 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____51060 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___549_51094 = env  in
      {
        curmodule = (uu___549_51094.curmodule);
        curmonad = (uu___549_51094.curmonad);
        modules = (uu___549_51094.modules);
        scope_mods = (uu___549_51094.scope_mods);
        exported_ids = (uu___549_51094.exported_ids);
        trans_exported_ids = (uu___549_51094.trans_exported_ids);
        includes = (uu___549_51094.includes);
        sigaccum = (uu___549_51094.sigaccum);
        sigmap = (uu___549_51094.sigmap);
        iface = b;
        admitted_iface = (uu___549_51094.admitted_iface);
        expect_typ = (uu___549_51094.expect_typ);
        docs = (uu___549_51094.docs);
        remaining_iface_decls = (uu___549_51094.remaining_iface_decls);
        syntax_only = (uu___549_51094.syntax_only);
        ds_hooks = (uu___549_51094.ds_hooks);
        dep_graph = (uu___549_51094.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___554_51115 = e  in
      {
        curmodule = (uu___554_51115.curmodule);
        curmonad = (uu___554_51115.curmonad);
        modules = (uu___554_51115.modules);
        scope_mods = (uu___554_51115.scope_mods);
        exported_ids = (uu___554_51115.exported_ids);
        trans_exported_ids = (uu___554_51115.trans_exported_ids);
        includes = (uu___554_51115.includes);
        sigaccum = (uu___554_51115.sigaccum);
        sigmap = (uu___554_51115.sigmap);
        iface = (uu___554_51115.iface);
        admitted_iface = b;
        expect_typ = (uu___554_51115.expect_typ);
        docs = (uu___554_51115.docs);
        remaining_iface_decls = (uu___554_51115.remaining_iface_decls);
        syntax_only = (uu___554_51115.syntax_only);
        ds_hooks = (uu___554_51115.ds_hooks);
        dep_graph = (uu___554_51115.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___559_51136 = e  in
      {
        curmodule = (uu___559_51136.curmodule);
        curmonad = (uu___559_51136.curmonad);
        modules = (uu___559_51136.modules);
        scope_mods = (uu___559_51136.scope_mods);
        exported_ids = (uu___559_51136.exported_ids);
        trans_exported_ids = (uu___559_51136.trans_exported_ids);
        includes = (uu___559_51136.includes);
        sigaccum = (uu___559_51136.sigaccum);
        sigmap = (uu___559_51136.sigmap);
        iface = (uu___559_51136.iface);
        admitted_iface = (uu___559_51136.admitted_iface);
        expect_typ = b;
        docs = (uu___559_51136.docs);
        remaining_iface_decls = (uu___559_51136.remaining_iface_decls);
        syntax_only = (uu___559_51136.syntax_only);
        ds_hooks = (uu___559_51136.ds_hooks);
        dep_graph = (uu___559_51136.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____51163 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____51163 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____51176 =
            let uu____51180 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____51180  in
          FStar_All.pipe_right uu____51176 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___420_51268  ->
         match uu___420_51268 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____51273 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___578_51285 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___578_51285.curmonad);
        modules = (uu___578_51285.modules);
        scope_mods = (uu___578_51285.scope_mods);
        exported_ids = (uu___578_51285.exported_ids);
        trans_exported_ids = (uu___578_51285.trans_exported_ids);
        includes = (uu___578_51285.includes);
        sigaccum = (uu___578_51285.sigaccum);
        sigmap = (uu___578_51285.sigmap);
        iface = (uu___578_51285.iface);
        admitted_iface = (uu___578_51285.admitted_iface);
        expect_typ = (uu___578_51285.expect_typ);
        docs = (uu___578_51285.docs);
        remaining_iface_decls = (uu___578_51285.remaining_iface_decls);
        syntax_only = (uu___578_51285.syntax_only);
        ds_hooks = (uu___578_51285.ds_hooks);
        dep_graph = (uu___578_51285.dep_graph)
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
      let uu____51309 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____51343  ->
                match uu____51343 with
                | (m,uu____51352) -> FStar_Ident.lid_equals l m))
         in
      match uu____51309 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____51369,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____51403 =
          FStar_List.partition
            (fun uu____51433  ->
               match uu____51433 with
               | (m,uu____51442) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____51403 with
        | (uu____51447,rest) ->
            let uu___603_51481 = env  in
            {
              curmodule = (uu___603_51481.curmodule);
              curmonad = (uu___603_51481.curmonad);
              modules = (uu___603_51481.modules);
              scope_mods = (uu___603_51481.scope_mods);
              exported_ids = (uu___603_51481.exported_ids);
              trans_exported_ids = (uu___603_51481.trans_exported_ids);
              includes = (uu___603_51481.includes);
              sigaccum = (uu___603_51481.sigaccum);
              sigmap = (uu___603_51481.sigmap);
              iface = (uu___603_51481.iface);
              admitted_iface = (uu___603_51481.admitted_iface);
              expect_typ = (uu___603_51481.expect_typ);
              docs = (uu___603_51481.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___603_51481.syntax_only);
              ds_hooks = (uu___603_51481.ds_hooks);
              dep_graph = (uu___603_51481.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____51510 = current_module env  in qual uu____51510 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____51512 =
            let uu____51513 = current_module env  in qual uu____51513 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____51512
            id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___613_51534 = env  in
      {
        curmodule = (uu___613_51534.curmodule);
        curmonad = (uu___613_51534.curmonad);
        modules = (uu___613_51534.modules);
        scope_mods = (uu___613_51534.scope_mods);
        exported_ids = (uu___613_51534.exported_ids);
        trans_exported_ids = (uu___613_51534.trans_exported_ids);
        includes = (uu___613_51534.includes);
        sigaccum = (uu___613_51534.sigaccum);
        sigmap = (uu___613_51534.sigmap);
        iface = (uu___613_51534.iface);
        admitted_iface = (uu___613_51534.admitted_iface);
        expect_typ = (uu___613_51534.expect_typ);
        docs = (uu___613_51534.docs);
        remaining_iface_decls = (uu___613_51534.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___613_51534.ds_hooks);
        dep_graph = (uu___613_51534.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___618_51552 = env  in
      {
        curmodule = (uu___618_51552.curmodule);
        curmonad = (uu___618_51552.curmonad);
        modules = (uu___618_51552.modules);
        scope_mods = (uu___618_51552.scope_mods);
        exported_ids = (uu___618_51552.exported_ids);
        trans_exported_ids = (uu___618_51552.trans_exported_ids);
        includes = (uu___618_51552.includes);
        sigaccum = (uu___618_51552.sigaccum);
        sigmap = (uu___618_51552.sigmap);
        iface = (uu___618_51552.iface);
        admitted_iface = (uu___618_51552.admitted_iface);
        expect_typ = (uu___618_51552.expect_typ);
        docs = (uu___618_51552.docs);
        remaining_iface_decls = (uu___618_51552.remaining_iface_decls);
        syntax_only = (uu___618_51552.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___618_51552.dep_graph)
      }
  
let new_sigmap : 'Auu____51558 . unit -> 'Auu____51558 FStar_Util.smap =
  fun uu____51565  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____51573 = new_sigmap ()  in
    let uu____51578 = new_sigmap ()  in
    let uu____51583 = new_sigmap ()  in
    let uu____51594 = new_sigmap ()  in
    let uu____51607 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____51573;
      trans_exported_ids = uu____51578;
      includes = uu____51583;
      sigaccum = [];
      sigmap = uu____51594;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____51607;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___625_51641 = env  in
      {
        curmodule = (uu___625_51641.curmodule);
        curmonad = (uu___625_51641.curmonad);
        modules = (uu___625_51641.modules);
        scope_mods = (uu___625_51641.scope_mods);
        exported_ids = (uu___625_51641.exported_ids);
        trans_exported_ids = (uu___625_51641.trans_exported_ids);
        includes = (uu___625_51641.includes);
        sigaccum = (uu___625_51641.sigaccum);
        sigmap = (uu___625_51641.sigmap);
        iface = (uu___625_51641.iface);
        admitted_iface = (uu___625_51641.admitted_iface);
        expect_typ = (uu___625_51641.expect_typ);
        docs = (uu___625_51641.docs);
        remaining_iface_decls = (uu___625_51641.remaining_iface_decls);
        syntax_only = (uu___625_51641.syntax_only);
        ds_hooks = (uu___625_51641.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____51669  ->
         match uu____51669 with
         | (m,uu____51676) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___634_51689 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___634_51689.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___637_51690 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index =
          (uu___637_51690.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___637_51690.FStar_Syntax_Syntax.sort)
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
      (fun uu____51793  ->
         match uu____51793 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____51824 =
                 let uu____51825 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____51825 dd dq  in
               FStar_Pervasives_Native.Some uu____51824
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____51865 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____51902 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____51923 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___421_51953  ->
      match uu___421_51953 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____51972 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____51972 cont_t) -> 'Auu____51972 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____52009 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____52009
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____52025  ->
                   match uu____52025 with
                   | (f,uu____52033) ->
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
  fun uu___422_52107  ->
    match uu___422_52107 with
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
              let rec aux uu___423_52183 =
                match uu___423_52183 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____52196 = get_exported_id_set env mname  in
                      match uu____52196 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____52223 = mex eikind  in
                            FStar_ST.op_Bang uu____52223  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____52285 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____52285 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____52340 = qual modul id1  in
                        find_in_module uu____52340
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____52345 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___424_52354  ->
    match uu___424_52354 with
    | Exported_id_field  -> true
    | uu____52357 -> false
  
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
                  let check_local_binding_id uu___425_52481 =
                    match uu___425_52481 with
                    | (id',uu____52484) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___426_52492 =
                    match uu___426_52492 with
                    | (id',uu____52495,uu____52496) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____52501 = current_module env  in
                    FStar_Ident.ids_of_lid uu____52501  in
                  let proc uu___427_52509 =
                    match uu___427_52509 with
                    | Local_binding l when check_local_binding_id l ->
                        k_local_binding l
                    | Rec_binding r when check_rec_binding_id r ->
                        k_rec_binding r
                    | Open_module_or_namespace (ns,Open_module ) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env ns id1
                    | Top_level_def id' when
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText ->
                        lookup_default_id Cont_ignore id1
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____52518 = FStar_Ident.lid_of_ids curmod_ns
                           in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____52518 id1
                    | uu____52523 -> Cont_ignore  in
                  let rec aux uu___428_52533 =
                    match uu___428_52533 with
                    | a::q ->
                        let uu____52542 = proc a  in
                        option_of_cont (fun uu____52546  -> aux q)
                          uu____52542
                    | [] ->
                        let uu____52547 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____52551  -> FStar_Pervasives_Native.None)
                          uu____52547
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____52559 .
    FStar_Range.range ->
      ('Auu____52559 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____52573  -> match uu____52573 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____52591 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____52591)
          -> 'Auu____52591 -> 'Auu____52591
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____52632 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____52632 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____52676 = unmangleOpName id1  in
      match uu____52676 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____52682 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____52688 =
                 found_local_binding id1.FStar_Ident.idRange r  in
               Cont_ok uu____52688) (fun uu____52690  -> Cont_fail)
            (fun uu____52692  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____52699  -> fun uu____52700  -> Cont_fail)
                 Cont_ignore)
            (fun uu____52708  -> fun uu____52709  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____52783 ->
                let lid = qualify env id1  in
                let uu____52785 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____52785 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____52813 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____52813
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____52837 = current_module env  in qual uu____52837 id1
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
        let rec aux uu___429_52909 =
          match uu___429_52909 with
          | [] ->
              let uu____52914 = module_is_defined env lid  in
              if uu____52914
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____52926 =
                  let uu____52927 = FStar_Ident.path_of_lid ns  in
                  let uu____52931 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____52927 uu____52931  in
                let uu____52936 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____52926 uu____52936  in
              let uu____52937 = module_is_defined env new_lid  in
              if uu____52937
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____52946 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____52952::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____52972 =
          let uu____52974 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____52974  in
        if uu____52972
        then
          let uu____52976 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____52976
           then ()
           else
             (let uu____52981 =
                let uu____52987 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____52987)
                 in
              let uu____52991 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____52981 uu____52991))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____53005 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____53009 = resolve_module_name env modul_orig true  in
          (match uu____53009 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____53014 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___430_53037  ->
             match uu___430_53037 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____53041 -> false) env.scope_mods
  
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
                 let uu____53170 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____53170
                   (FStar_Util.map_option
                      (fun uu____53220  ->
                         match uu____53220 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____53290 = aux ns_rev_prefix ns_last_id  in
              (match uu____53290 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____53353 =
            let uu____53356 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____53356 true  in
          match uu____53353 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____53371 -> do_shorten env ids
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
                  | uu____53492::uu____53493 ->
                      let uu____53496 =
                        let uu____53499 =
                          let uu____53500 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____53501 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____53500 uu____53501
                           in
                        resolve_module_name env uu____53499 true  in
                      (match uu____53496 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____53506 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____53510  ->
                                FStar_Pervasives_Native.None) uu____53506)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___431_53534  ->
      match uu___431_53534 with
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
              let uu____53655 = k_global_def lid1 def  in
              cont_of_option k uu____53655  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____53691 = k_local_binding l  in
                 cont_of_option Cont_fail uu____53691)
              (fun r  ->
                 let uu____53697 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____53697)
              (fun uu____53701  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____53712,uu____53713,uu____53714,l,uu____53716,uu____53717) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___432_53730  ->
               match uu___432_53730 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____53733,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____53745 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____53751,uu____53752,uu____53753) -> FStar_Pervasives_Native.None
    | uu____53754 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____53770 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____53778 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____53778
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____53770 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____53801 =
         let uu____53802 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____53802  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____53801) &&
        (let uu____53806 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____53806 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____53823 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___433_53830  ->
                     match uu___433_53830 with
                     | FStar_Syntax_Syntax.Projector uu____53832 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____53838 -> true
                     | uu____53840 -> false)))
           in
        if uu____53823
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____53845 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___434_53851  ->
                 match uu___434_53851 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____53854 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___435_53860  ->
                    match uu___435_53860 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____53863 -> false)))
             &&
             (let uu____53866 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___436_53872  ->
                        match uu___436_53872 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____53875 -> false))
                 in
              Prims.op_Negation uu____53866))
         in
      if uu____53845 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___439_53927 =
            match uu___439_53927 with
            | (uu____53935,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____53939) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____53944 ->
                     let uu____53961 =
                       let uu____53962 =
                         let uu____53969 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____53969, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____53962  in
                     FStar_Pervasives_Native.Some uu____53961
                 | FStar_Syntax_Syntax.Sig_datacon uu____53972 ->
                     let uu____53988 =
                       let uu____53989 =
                         let uu____53996 =
                           let uu____53997 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____53997
                            in
                         (uu____53996, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____53989  in
                     FStar_Pervasives_Native.Some uu____53988
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____54002,lbs),uu____54004) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____54016 =
                       let uu____54017 =
                         let uu____54024 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____54024, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____54017  in
                     FStar_Pervasives_Native.Some uu____54016
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____54028,uu____54029) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____54033 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___437_54039  ->
                                  match uu___437_54039 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____54042 -> false)))
                        in
                     if uu____54033
                     then
                       let lid2 =
                         let uu____54048 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____54048  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____54050 =
                         FStar_Util.find_map quals
                           (fun uu___438_54055  ->
                              match uu___438_54055 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____54059 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____54050 with
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
                        | uu____54068 ->
                            let uu____54071 =
                              let uu____54072 =
                                let uu____54079 =
                                  let uu____54080 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____54080
                                   in
                                (uu____54079,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____54072  in
                            FStar_Pervasives_Native.Some uu____54071)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____54088 =
                       let uu____54089 =
                         let uu____54094 =
                           let uu____54095 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54095
                            in
                         (se, uu____54094)  in
                       Eff_name uu____54089  in
                     FStar_Pervasives_Native.Some uu____54088
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____54097 =
                       let uu____54098 =
                         let uu____54103 =
                           let uu____54104 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54104
                            in
                         (se, uu____54103)  in
                       Eff_name uu____54098  in
                     FStar_Pervasives_Native.Some uu____54097
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____54105 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____54124 =
                       let uu____54125 =
                         let uu____54132 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____54132, [])  in
                       Term_name uu____54125  in
                     FStar_Pervasives_Native.Some uu____54124
                 | uu____54136 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____54154 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____54154 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____54170 =
            match uu____54170 with
            | (id1,l,dd) ->
                let uu____54182 =
                  let uu____54183 =
                    let uu____54190 =
                      let uu____54191 =
                        let uu____54192 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____54192  in
                      FStar_Syntax_Syntax.fvar uu____54191 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____54190, [])  in
                  Term_name uu____54183  in
                FStar_Pervasives_Native.Some uu____54182
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____54200 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____54200 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____54208 -> FStar_Pervasives_Native.None)
            | uu____54211 -> FStar_Pervasives_Native.None  in
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
        let uu____54249 = try_lookup_name true exclude_interf env lid  in
        match uu____54249 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____54265 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54285 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54285 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____54300 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54326 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54326 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____54342;
             FStar_Syntax_Syntax.sigquals = uu____54343;
             FStar_Syntax_Syntax.sigmeta = uu____54344;
             FStar_Syntax_Syntax.sigattrs = uu____54345;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____54364;
             FStar_Syntax_Syntax.sigquals = uu____54365;
             FStar_Syntax_Syntax.sigmeta = uu____54366;
             FStar_Syntax_Syntax.sigattrs = uu____54367;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____54385,uu____54386,uu____54387,uu____54388,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____54390;
             FStar_Syntax_Syntax.sigquals = uu____54391;
             FStar_Syntax_Syntax.sigmeta = uu____54392;
             FStar_Syntax_Syntax.sigattrs = uu____54393;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____54415 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54441 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54441 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____54451;
             FStar_Syntax_Syntax.sigquals = uu____54452;
             FStar_Syntax_Syntax.sigmeta = uu____54453;
             FStar_Syntax_Syntax.sigattrs = uu____54454;_},uu____54455)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____54465;
             FStar_Syntax_Syntax.sigquals = uu____54466;
             FStar_Syntax_Syntax.sigmeta = uu____54467;
             FStar_Syntax_Syntax.sigattrs = uu____54468;_},uu____54469)
          -> FStar_Pervasives_Native.Some ne
      | uu____54478 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____54497 = try_lookup_effect_name env lid  in
      match uu____54497 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____54502 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54517 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54517 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____54527,uu____54528,uu____54529,uu____54530);
             FStar_Syntax_Syntax.sigrng = uu____54531;
             FStar_Syntax_Syntax.sigquals = uu____54532;
             FStar_Syntax_Syntax.sigmeta = uu____54533;
             FStar_Syntax_Syntax.sigattrs = uu____54534;_},uu____54535)
          ->
          let rec aux new_name =
            let uu____54556 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____54556 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____54577) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____54588 =
                       let uu____54589 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____54589
                        in
                     FStar_Pervasives_Native.Some uu____54588
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____54591 =
                       let uu____54592 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____54592
                        in
                     FStar_Pervasives_Native.Some uu____54591
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____54593,uu____54594,uu____54595,cmp,uu____54597) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____54603 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____54604,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____54610 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___440_54649 =
        match uu___440_54649 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____54659,uu____54660,uu____54661);
             FStar_Syntax_Syntax.sigrng = uu____54662;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____54664;
             FStar_Syntax_Syntax.sigattrs = uu____54665;_},uu____54666)
            -> FStar_Pervasives_Native.Some quals
        | uu____54675 -> FStar_Pervasives_Native.None  in
      let uu____54683 =
        resolve_in_open_namespaces' env lid
          (fun uu____54691  -> FStar_Pervasives_Native.None)
          (fun uu____54695  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____54683 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____54705 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____54723 =
        FStar_List.tryFind
          (fun uu____54738  ->
             match uu____54738 with
             | (mlid,modul) ->
                 let uu____54746 = FStar_Ident.path_of_lid mlid  in
                 uu____54746 = path) env.modules
         in
      match uu____54723 with
      | FStar_Pervasives_Native.Some (uu____54749,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___441_54789 =
        match uu___441_54789 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____54797,lbs),uu____54799);
             FStar_Syntax_Syntax.sigrng = uu____54800;
             FStar_Syntax_Syntax.sigquals = uu____54801;
             FStar_Syntax_Syntax.sigmeta = uu____54802;
             FStar_Syntax_Syntax.sigattrs = uu____54803;_},uu____54804)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____54822 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____54822
        | uu____54823 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____54830  -> FStar_Pervasives_Native.None)
        (fun uu____54832  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___442_54865 =
        match uu___442_54865 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____54876);
             FStar_Syntax_Syntax.sigrng = uu____54877;
             FStar_Syntax_Syntax.sigquals = uu____54878;
             FStar_Syntax_Syntax.sigmeta = uu____54879;
             FStar_Syntax_Syntax.sigattrs = uu____54880;_},uu____54881)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____54907 -> FStar_Pervasives_Native.None)
        | uu____54914 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____54925  -> FStar_Pervasives_Native.None)
        (fun uu____54929  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____54989 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____54989 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____55014 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____55052) ->
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
      let uu____55110 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____55110 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55142 = try_lookup_lid env l  in
      match uu____55142 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____55148 =
            let uu____55149 = FStar_Syntax_Subst.compress e  in
            uu____55149.FStar_Syntax_Syntax.n  in
          (match uu____55148 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____55155 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____55167 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____55167 with
      | (uu____55177,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____55198 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____55202 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____55202 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____55207 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___1304_55238 = env  in
        {
          curmodule = (uu___1304_55238.curmodule);
          curmonad = (uu___1304_55238.curmonad);
          modules = (uu___1304_55238.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___1304_55238.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___1304_55238.sigaccum);
          sigmap = (uu___1304_55238.sigmap);
          iface = (uu___1304_55238.iface);
          admitted_iface = (uu___1304_55238.admitted_iface);
          expect_typ = (uu___1304_55238.expect_typ);
          docs = (uu___1304_55238.docs);
          remaining_iface_decls = (uu___1304_55238.remaining_iface_decls);
          syntax_only = (uu___1304_55238.syntax_only);
          ds_hooks = (uu___1304_55238.ds_hooks);
          dep_graph = (uu___1304_55238.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55254 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____55254 drop_attributes
  
let (try_lookup_doc :
  env ->
    FStar_Ident.lid -> FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)
  = fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str 
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
               (uu____55324,uu____55325,uu____55326);
             FStar_Syntax_Syntax.sigrng = uu____55327;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____55329;
             FStar_Syntax_Syntax.sigattrs = uu____55330;_},uu____55331)
            ->
            let uu____55338 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___443_55344  ->
                      match uu___443_55344 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____55347 -> false))
               in
            if uu____55338
            then
              let uu____55352 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____55352
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____55355;
             FStar_Syntax_Syntax.sigrng = uu____55356;
             FStar_Syntax_Syntax.sigquals = uu____55357;
             FStar_Syntax_Syntax.sigmeta = uu____55358;
             FStar_Syntax_Syntax.sigattrs = uu____55359;_},uu____55360)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____55386 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____55386
        | uu____55387 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55394  -> FStar_Pervasives_Native.None)
        (fun uu____55396  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___444_55431 =
        match uu___444_55431 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____55441,uu____55442,uu____55443,uu____55444,datas,uu____55446);
             FStar_Syntax_Syntax.sigrng = uu____55447;
             FStar_Syntax_Syntax.sigquals = uu____55448;
             FStar_Syntax_Syntax.sigmeta = uu____55449;
             FStar_Syntax_Syntax.sigattrs = uu____55450;_},uu____55451)
            -> FStar_Pervasives_Native.Some datas
        | uu____55468 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55479  -> FStar_Pervasives_Native.None)
        (fun uu____55483  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____55562 =
    let uu____55563 =
      let uu____55568 =
        let uu____55571 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____55571  in
      let uu____55605 = FStar_ST.op_Bang record_cache  in uu____55568 ::
        uu____55605
       in
    FStar_ST.op_Colon_Equals record_cache uu____55563  in
  let pop1 uu____55671 =
    let uu____55672 =
      let uu____55677 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____55677  in
    FStar_ST.op_Colon_Equals record_cache uu____55672  in
  let snapshot1 uu____55748 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____55772 =
    let uu____55773 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____55773  in
  let insert r =
    let uu____55813 =
      let uu____55818 = let uu____55821 = peek1 ()  in r :: uu____55821  in
      let uu____55824 =
        let uu____55829 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____55829  in
      uu____55818 :: uu____55824  in
    FStar_ST.op_Colon_Equals record_cache uu____55813  in
  let filter1 uu____55897 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____55906 =
      let uu____55911 =
        let uu____55916 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____55916  in
      filtered :: uu____55911  in
    FStar_ST.op_Colon_Equals record_cache uu____55906  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____56842) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___445_56861  ->
                   match uu___445_56861 with
                   | FStar_Syntax_Syntax.RecordType uu____56863 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____56873 ->
                       true
                   | uu____56883 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___446_56908  ->
                      match uu___446_56908 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____56911,uu____56912,uu____56913,uu____56914,uu____56915);
                          FStar_Syntax_Syntax.sigrng = uu____56916;
                          FStar_Syntax_Syntax.sigquals = uu____56917;
                          FStar_Syntax_Syntax.sigmeta = uu____56918;
                          FStar_Syntax_Syntax.sigattrs = uu____56919;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____56930 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___447_56966  ->
                    match uu___447_56966 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____56970,uu____56971,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____56973;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____56975;
                        FStar_Syntax_Syntax.sigattrs = uu____56976;_} ->
                        let uu____56987 =
                          let uu____56988 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____56988  in
                        (match uu____56987 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____56994,t,uu____56996,uu____56997,uu____56998);
                             FStar_Syntax_Syntax.sigrng = uu____56999;
                             FStar_Syntax_Syntax.sigquals = uu____57000;
                             FStar_Syntax_Syntax.sigmeta = uu____57001;
                             FStar_Syntax_Syntax.sigattrs = uu____57002;_} ->
                             let uu____57013 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____57013 with
                              | (formals,uu____57029) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____57083  ->
                                            match uu____57083 with
                                            | (x,q) ->
                                                let uu____57096 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____57096
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____57151  ->
                                            match uu____57151 with
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
                                  ((let uu____57175 =
                                      let uu____57178 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____57178
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____57175);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____57237 =
                                            match uu____57237 with
                                            | (id1,uu____57243) ->
                                                let modul =
                                                  let uu____57246 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____57246.FStar_Ident.str
                                                   in
                                                let uu____57247 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____57247 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____57270 =
                                                         let uu____57271 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____57271
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____57270);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____57316
                                                               =
                                                               let uu____57317
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____57317.FStar_Ident.ident
                                                                in
                                                             uu____57316.FStar_Ident.idText
                                                              in
                                                           let uu____57319 =
                                                             let uu____57320
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____57320
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____57319))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____57372 -> ())
                    | uu____57373 -> ()))
        | uu____57374 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____57396 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____57396 with
        | (ns,id1) ->
            let uu____57413 = peek_record_cache ()  in
            FStar_Util.find_map uu____57413
              (fun record  ->
                 let uu____57419 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____57425  -> FStar_Pervasives_Native.None)
                   uu____57419)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____57427  -> Cont_ignore) (fun uu____57429  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____57435 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____57435)
        (fun k  -> fun uu____57441  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____57457 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____57457 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____57463 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____57483 = try_lookup_record_by_field_name env lid  in
        match uu____57483 with
        | FStar_Pervasives_Native.Some record' when
            let uu____57488 =
              let uu____57490 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____57490  in
            let uu____57491 =
              let uu____57493 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____57493  in
            uu____57488 = uu____57491 ->
            let uu____57495 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____57499  -> Cont_ok ())
               in
            (match uu____57495 with
             | Cont_ok uu____57501 -> true
             | uu____57503 -> false)
        | uu____57507 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____57529 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____57529 with
      | FStar_Pervasives_Native.Some r ->
          let uu____57540 =
            let uu____57546 =
              let uu____57547 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____57548 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____57547 uu____57548  in
            (uu____57546, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____57540
      | uu____57555 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____57573  ->
    let uu____57574 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____57574
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____57595  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___448_57608  ->
      match uu___448_57608 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___449_57646 =
            match uu___449_57646 with
            | Rec_binding uu____57648 -> true
            | uu____57650 -> false  in
          let this_env =
            let uu___1530_57653 = env  in
            let uu____57654 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1530_57653.curmodule);
              curmonad = (uu___1530_57653.curmonad);
              modules = (uu___1530_57653.modules);
              scope_mods = uu____57654;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1530_57653.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1530_57653.sigaccum);
              sigmap = (uu___1530_57653.sigmap);
              iface = (uu___1530_57653.iface);
              admitted_iface = (uu___1530_57653.admitted_iface);
              expect_typ = (uu___1530_57653.expect_typ);
              docs = (uu___1530_57653.docs);
              remaining_iface_decls = (uu___1530_57653.remaining_iface_decls);
              syntax_only = (uu___1530_57653.syntax_only);
              ds_hooks = (uu___1530_57653.ds_hooks);
              dep_graph = (uu___1530_57653.dep_graph)
            }  in
          let uu____57657 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____57657 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____57674 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1538_57699 = env  in
      {
        curmodule = (uu___1538_57699.curmodule);
        curmonad = (uu___1538_57699.curmonad);
        modules = (uu___1538_57699.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1538_57699.exported_ids);
        trans_exported_ids = (uu___1538_57699.trans_exported_ids);
        includes = (uu___1538_57699.includes);
        sigaccum = (uu___1538_57699.sigaccum);
        sigmap = (uu___1538_57699.sigmap);
        iface = (uu___1538_57699.iface);
        admitted_iface = (uu___1538_57699.admitted_iface);
        expect_typ = (uu___1538_57699.expect_typ);
        docs = (uu___1538_57699.docs);
        remaining_iface_decls = (uu___1538_57699.remaining_iface_decls);
        syntax_only = (uu___1538_57699.syntax_only);
        ds_hooks = (uu___1538_57699.ds_hooks);
        dep_graph = (uu___1538_57699.dep_graph)
      }
  
let (push_bv : env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv)) =
  fun env  ->
    fun x  ->
      let bv =
        FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
          (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange))
          FStar_Syntax_Syntax.tun
         in
      ((push_scope_mod env (Local_binding (x, bv))), bv)
  
let (push_top_level_rec_binding :
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env) =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x  in
        let uu____57733 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____57733
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____57740 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____57740)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____57784) ->
                let uu____57792 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____57792 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____57797 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____57797
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____57806 =
            let uu____57812 =
              let uu____57814 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____57814 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____57812)  in
          let uu____57818 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____57806 uu____57818  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____57827 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____57840 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____57851 -> (false, true)
            | uu____57864 -> (false, false)  in
          match uu____57827 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____57878 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____57884 =
                       let uu____57886 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____57886  in
                     if uu____57884
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____57878 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____57894 ->
                   (extract_record env globals s;
                    (let uu___1579_57898 = env  in
                     {
                       curmodule = (uu___1579_57898.curmodule);
                       curmonad = (uu___1579_57898.curmonad);
                       modules = (uu___1579_57898.modules);
                       scope_mods = (uu___1579_57898.scope_mods);
                       exported_ids = (uu___1579_57898.exported_ids);
                       trans_exported_ids =
                         (uu___1579_57898.trans_exported_ids);
                       includes = (uu___1579_57898.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1579_57898.sigmap);
                       iface = (uu___1579_57898.iface);
                       admitted_iface = (uu___1579_57898.admitted_iface);
                       expect_typ = (uu___1579_57898.expect_typ);
                       docs = (uu___1579_57898.docs);
                       remaining_iface_decls =
                         (uu___1579_57898.remaining_iface_decls);
                       syntax_only = (uu___1579_57898.syntax_only);
                       ds_hooks = (uu___1579_57898.ds_hooks);
                       dep_graph = (uu___1579_57898.dep_graph)
                     })))
           in
        let env2 =
          let uu___1582_57900 = env1  in
          let uu____57901 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1582_57900.curmodule);
            curmonad = (uu___1582_57900.curmonad);
            modules = (uu___1582_57900.modules);
            scope_mods = uu____57901;
            exported_ids = (uu___1582_57900.exported_ids);
            trans_exported_ids = (uu___1582_57900.trans_exported_ids);
            includes = (uu___1582_57900.includes);
            sigaccum = (uu___1582_57900.sigaccum);
            sigmap = (uu___1582_57900.sigmap);
            iface = (uu___1582_57900.iface);
            admitted_iface = (uu___1582_57900.admitted_iface);
            expect_typ = (uu___1582_57900.expect_typ);
            docs = (uu___1582_57900.docs);
            remaining_iface_decls = (uu___1582_57900.remaining_iface_decls);
            syntax_only = (uu___1582_57900.syntax_only);
            ds_hooks = (uu___1582_57900.ds_hooks);
            dep_graph = (uu___1582_57900.dep_graph)
          }  in
        let uu____57927 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____57953) ->
              let uu____57962 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____57962)
          | uu____57989 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____57927 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____58048  ->
                     match uu____58048 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____58070 =
                                    let uu____58073 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____58073
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____58070);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____58124 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____58124.FStar_Ident.str  in
                                      ((let uu____58126 =
                                          get_exported_id_set env3 modul  in
                                        match uu____58126 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____58148 =
                                              let uu____58149 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____58149
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____58148
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
                let uu___1607_58206 = env3  in
                let uu____58207 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1607_58206.curmodule);
                  curmonad = (uu___1607_58206.curmonad);
                  modules = (uu___1607_58206.modules);
                  scope_mods = uu____58207;
                  exported_ids = (uu___1607_58206.exported_ids);
                  trans_exported_ids = (uu___1607_58206.trans_exported_ids);
                  includes = (uu___1607_58206.includes);
                  sigaccum = (uu___1607_58206.sigaccum);
                  sigmap = (uu___1607_58206.sigmap);
                  iface = (uu___1607_58206.iface);
                  admitted_iface = (uu___1607_58206.admitted_iface);
                  expect_typ = (uu___1607_58206.expect_typ);
                  docs = (uu___1607_58206.docs);
                  remaining_iface_decls =
                    (uu___1607_58206.remaining_iface_decls);
                  syntax_only = (uu___1607_58206.syntax_only);
                  ds_hooks = (uu___1607_58206.ds_hooks);
                  dep_graph = (uu___1607_58206.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____58268 =
        let uu____58273 = resolve_module_name env ns false  in
        match uu____58273 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____58288 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____58306  ->
                      match uu____58306 with
                      | (m,uu____58313) ->
                          let uu____58314 =
                            let uu____58316 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____58316 "."  in
                          let uu____58319 =
                            let uu____58321 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____58321 "."  in
                          FStar_Util.starts_with uu____58314 uu____58319))
               in
            if uu____58288
            then (ns, Open_namespace)
            else
              (let uu____58331 =
                 let uu____58337 =
                   let uu____58339 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____58339
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____58337)  in
               let uu____58343 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____58331 uu____58343)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____58268 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____58365 = resolve_module_name env ns false  in
      match uu____58365 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____58375 = current_module env1  in
              uu____58375.FStar_Ident.str  in
            (let uu____58377 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____58377 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____58401 =
                   let uu____58404 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____58404
                    in
                 FStar_ST.op_Colon_Equals incl uu____58401);
            (match () with
             | () ->
                 let uu____58453 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____58453 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____58473 =
                          let uu____58570 = get_exported_id_set env1 curmod
                             in
                          let uu____58617 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____58570, uu____58617)  in
                        match uu____58473 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____59033 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____59033  in
                              let ex = cur_exports k  in
                              (let uu____59134 =
                                 let uu____59138 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____59138 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____59134);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____59230 =
                                     let uu____59234 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____59234 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____59230)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____59283 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____59385 =
                        let uu____59391 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____59391)
                         in
                      let uu____59395 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____59385 uu____59395))))
      | uu____59396 ->
          let uu____59399 =
            let uu____59405 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____59405)  in
          let uu____59409 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____59399 uu____59409
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____59426 = module_is_defined env l  in
        if uu____59426
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____59433 =
             let uu____59439 =
               let uu____59441 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____59441  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____59439)  in
           let uu____59445 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____59433 uu____59445)
  
let (push_doc :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option -> env)
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | FStar_Pervasives_Native.None  -> env
        | FStar_Pervasives_Native.Some doc1 ->
            ((let uu____59468 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____59468 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____59472 = FStar_Ident.range_of_lid l  in
                  let uu____59473 =
                    let uu____59479 =
                      let uu____59481 = FStar_Ident.string_of_lid l  in
                      let uu____59483 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____59485 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____59481 uu____59483 uu____59485
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____59479)  in
                  FStar_Errors.log_issue uu____59472 uu____59473);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
  
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
                      let uu____59531 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____59531 ->
                      let uu____59536 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____59536 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____59551;
                              FStar_Syntax_Syntax.sigrng = uu____59552;
                              FStar_Syntax_Syntax.sigquals = uu____59553;
                              FStar_Syntax_Syntax.sigmeta = uu____59554;
                              FStar_Syntax_Syntax.sigattrs = uu____59555;_},uu____59556)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____59574;
                              FStar_Syntax_Syntax.sigrng = uu____59575;
                              FStar_Syntax_Syntax.sigquals = uu____59576;
                              FStar_Syntax_Syntax.sigmeta = uu____59577;
                              FStar_Syntax_Syntax.sigattrs = uu____59578;_},uu____59579)
                           -> lids
                       | uu____59607 ->
                           ((let uu____59616 =
                               let uu____59618 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____59618  in
                             if uu____59616
                             then
                               let uu____59621 = FStar_Ident.range_of_lid l
                                  in
                               let uu____59622 =
                                 let uu____59628 =
                                   let uu____59630 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____59630
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____59628)
                                  in
                               FStar_Errors.log_issue uu____59621 uu____59622
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1710_59647 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1710_59647.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1710_59647.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1710_59647.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1710_59647.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____59649 -> lids) [])
         in
      let uu___1715_59650 = m  in
      let uu____59651 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____59661,uu____59662) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1724_59665 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1724_59665.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1724_59665.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1724_59665.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1724_59665.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____59666 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1715_59650.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____59651;
        FStar_Syntax_Syntax.exports =
          (uu___1715_59650.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1715_59650.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____59690) ->
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
                                (lid,uu____59711,uu____59712,uu____59713,uu____59714,uu____59715)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____59731,uu____59732)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____59749 =
                                        let uu____59756 =
                                          let uu____59757 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____59758 =
                                            let uu____59765 =
                                              let uu____59766 =
                                                let uu____59781 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____59781)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____59766
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____59765
                                             in
                                          uu____59758
                                            FStar_Pervasives_Native.None
                                            uu____59757
                                           in
                                        (lid, univ_names, uu____59756)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____59749
                                       in
                                    let se2 =
                                      let uu___1756_59795 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1756_59795.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1756_59795.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1756_59795.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____59805 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____59809,uu____59810) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____59819,lbs),uu____59821)
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
                             let uu____59839 =
                               let uu____59841 =
                                 let uu____59842 =
                                   let uu____59845 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____59845.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____59842.FStar_Syntax_Syntax.v  in
                               uu____59841.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____59839))
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
                               let uu____59862 =
                                 let uu____59865 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____59865.FStar_Syntax_Syntax.fv_name  in
                               uu____59862.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1779_59870 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1779_59870.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1779_59870.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1779_59870.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____59880 -> ()));
      (let curmod =
         let uu____59883 = current_module env  in uu____59883.FStar_Ident.str
          in
       (let uu____59885 =
          let uu____59982 = get_exported_id_set env curmod  in
          let uu____60029 = get_trans_exported_id_set env curmod  in
          (uu____59982, uu____60029)  in
        match uu____59885 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____60448 = cur_ex eikind  in
                FStar_ST.op_Bang uu____60448  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____60554 =
                let uu____60558 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____60558  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____60554  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____60607 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1797_60705 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1797_60705.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1797_60705.exported_ids);
                    trans_exported_ids = (uu___1797_60705.trans_exported_ids);
                    includes = (uu___1797_60705.includes);
                    sigaccum = [];
                    sigmap = (uu___1797_60705.sigmap);
                    iface = (uu___1797_60705.iface);
                    admitted_iface = (uu___1797_60705.admitted_iface);
                    expect_typ = (uu___1797_60705.expect_typ);
                    docs = (uu___1797_60705.docs);
                    remaining_iface_decls =
                      (uu___1797_60705.remaining_iface_decls);
                    syntax_only = (uu___1797_60705.syntax_only);
                    ds_hooks = (uu___1797_60705.ds_hooks);
                    dep_graph = (uu___1797_60705.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____60732  ->
         push_record_cache ();
         (let uu____60735 =
            let uu____60738 = FStar_ST.op_Bang stack  in env :: uu____60738
             in
          FStar_ST.op_Colon_Equals stack uu____60735);
         (let uu___1803_60787 = env  in
          let uu____60788 = FStar_Util.smap_copy env.exported_ids  in
          let uu____60793 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____60798 = FStar_Util.smap_copy env.includes  in
          let uu____60809 = FStar_Util.smap_copy env.sigmap  in
          let uu____60822 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1803_60787.curmodule);
            curmonad = (uu___1803_60787.curmonad);
            modules = (uu___1803_60787.modules);
            scope_mods = (uu___1803_60787.scope_mods);
            exported_ids = uu____60788;
            trans_exported_ids = uu____60793;
            includes = uu____60798;
            sigaccum = (uu___1803_60787.sigaccum);
            sigmap = uu____60809;
            iface = (uu___1803_60787.iface);
            admitted_iface = (uu___1803_60787.admitted_iface);
            expect_typ = (uu___1803_60787.expect_typ);
            docs = uu____60822;
            remaining_iface_decls = (uu___1803_60787.remaining_iface_decls);
            syntax_only = (uu___1803_60787.syntax_only);
            ds_hooks = (uu___1803_60787.ds_hooks);
            dep_graph = (uu___1803_60787.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____60830  ->
    FStar_Util.atomically
      (fun uu____60837  ->
         let uu____60838 = FStar_ST.op_Bang stack  in
         match uu____60838 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____60893 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____60940 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____60944 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____60986 = FStar_Util.smap_try_find sm' k  in
              match uu____60986 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1838_61017 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1838_61017.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1838_61017.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1838_61017.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1838_61017.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____61018 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____61026 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____61053 = finish env modul1  in (uu____61053, modul1)
  
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
      let uu____61122 =
        let uu____61126 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____61126  in
      FStar_Util.set_elements uu____61122  in
    let fields =
      let uu____61189 =
        let uu____61193 = e Exported_id_field  in
        FStar_ST.op_Bang uu____61193  in
      FStar_Util.set_elements uu____61189  in
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
          let uu____61285 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____61285  in
        let fields =
          let uu____61299 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____61299  in
        (fun uu___450_61307  ->
           match uu___450_61307 with
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
  'Auu____61411 .
    'Auu____61411 Prims.list FStar_Pervasives_Native.option ->
      'Auu____61411 Prims.list FStar_ST.ref
  =
  fun uu___451_61424  ->
    match uu___451_61424 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____61467 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____61467 as_exported_ids  in
      let uu____61473 = as_ids_opt env.exported_ids  in
      let uu____61476 = as_ids_opt env.trans_exported_ids  in
      let uu____61479 =
        let uu____61484 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____61484 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____61473;
        mii_trans_exported_ids = uu____61476;
        mii_includes = uu____61479
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
                let uu____61573 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____61573 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___452_61595 =
                  match uu___452_61595 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____61607  ->
                     match uu____61607 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____61633 =
                    let uu____61638 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____61638, Open_namespace)  in
                  [uu____61633]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____61669 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____61669);
              (match () with
               | () ->
                   ((let uu____61674 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____61674);
                    (match () with
                     | () ->
                         ((let uu____61679 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____61679);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1908_61689 = env1  in
                                 let uu____61690 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1908_61689.curmonad);
                                   modules = (uu___1908_61689.modules);
                                   scope_mods = uu____61690;
                                   exported_ids =
                                     (uu___1908_61689.exported_ids);
                                   trans_exported_ids =
                                     (uu___1908_61689.trans_exported_ids);
                                   includes = (uu___1908_61689.includes);
                                   sigaccum = (uu___1908_61689.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1908_61689.expect_typ);
                                   docs = (uu___1908_61689.docs);
                                   remaining_iface_decls =
                                     (uu___1908_61689.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1908_61689.syntax_only);
                                   ds_hooks = (uu___1908_61689.ds_hooks);
                                   dep_graph = (uu___1908_61689.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____61702 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____61728  ->
                      match uu____61728 with
                      | (l,uu____61735) -> FStar_Ident.lid_equals l mname))
               in
            match uu____61702 with
            | FStar_Pervasives_Native.None  ->
                let uu____61745 = prep env  in (uu____61745, false)
            | FStar_Pervasives_Native.Some (uu____61748,m) ->
                ((let uu____61755 =
                    (let uu____61759 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____61759) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____61755
                  then
                    let uu____61762 =
                      let uu____61768 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____61768)
                       in
                    let uu____61772 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____61762 uu____61772
                  else ());
                 (let uu____61775 =
                    let uu____61776 = push env  in prep uu____61776  in
                  (uu____61775, true)))
  
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
          let uu___1929_61794 = env  in
          {
            curmodule = (uu___1929_61794.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1929_61794.modules);
            scope_mods = (uu___1929_61794.scope_mods);
            exported_ids = (uu___1929_61794.exported_ids);
            trans_exported_ids = (uu___1929_61794.trans_exported_ids);
            includes = (uu___1929_61794.includes);
            sigaccum = (uu___1929_61794.sigaccum);
            sigmap = (uu___1929_61794.sigmap);
            iface = (uu___1929_61794.iface);
            admitted_iface = (uu___1929_61794.admitted_iface);
            expect_typ = (uu___1929_61794.expect_typ);
            docs = (uu___1929_61794.docs);
            remaining_iface_decls = (uu___1929_61794.remaining_iface_decls);
            syntax_only = (uu___1929_61794.syntax_only);
            ds_hooks = (uu___1929_61794.ds_hooks);
            dep_graph = (uu___1929_61794.dep_graph)
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
        let uu____61829 = lookup1 lid  in
        match uu____61829 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____61844  ->
                   match uu____61844 with
                   | (lid1,uu____61851) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____61854 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____61854  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____61866 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____61867 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____61866 uu____61867  in
                 let uu____61868 = resolve_module_name env modul true  in
                 match uu____61868 with
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
            let uu____61889 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____61889
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____61919 = lookup1 id1  in
      match uu____61919 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  