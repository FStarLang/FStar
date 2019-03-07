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
    match projectee with | Open_module  -> true | uu____48980 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____48991 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____49211 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____49230 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____49249 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____49268 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____49287 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____49306 -> false
  
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
    | uu____49327 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____49338 -> false
  
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
    ds_push_open_hook = (fun uu____50958  -> fun uu____50959  -> ());
    ds_push_include_hook = (fun uu____50962  -> fun uu____50963  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____50967  -> fun uu____50968  -> fun uu____50969  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____51006 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____51047 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___549_51081 = env  in
      {
        curmodule = (uu___549_51081.curmodule);
        curmonad = (uu___549_51081.curmonad);
        modules = (uu___549_51081.modules);
        scope_mods = (uu___549_51081.scope_mods);
        exported_ids = (uu___549_51081.exported_ids);
        trans_exported_ids = (uu___549_51081.trans_exported_ids);
        includes = (uu___549_51081.includes);
        sigaccum = (uu___549_51081.sigaccum);
        sigmap = (uu___549_51081.sigmap);
        iface = b;
        admitted_iface = (uu___549_51081.admitted_iface);
        expect_typ = (uu___549_51081.expect_typ);
        docs = (uu___549_51081.docs);
        remaining_iface_decls = (uu___549_51081.remaining_iface_decls);
        syntax_only = (uu___549_51081.syntax_only);
        ds_hooks = (uu___549_51081.ds_hooks);
        dep_graph = (uu___549_51081.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___554_51102 = e  in
      {
        curmodule = (uu___554_51102.curmodule);
        curmonad = (uu___554_51102.curmonad);
        modules = (uu___554_51102.modules);
        scope_mods = (uu___554_51102.scope_mods);
        exported_ids = (uu___554_51102.exported_ids);
        trans_exported_ids = (uu___554_51102.trans_exported_ids);
        includes = (uu___554_51102.includes);
        sigaccum = (uu___554_51102.sigaccum);
        sigmap = (uu___554_51102.sigmap);
        iface = (uu___554_51102.iface);
        admitted_iface = b;
        expect_typ = (uu___554_51102.expect_typ);
        docs = (uu___554_51102.docs);
        remaining_iface_decls = (uu___554_51102.remaining_iface_decls);
        syntax_only = (uu___554_51102.syntax_only);
        ds_hooks = (uu___554_51102.ds_hooks);
        dep_graph = (uu___554_51102.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___559_51123 = e  in
      {
        curmodule = (uu___559_51123.curmodule);
        curmonad = (uu___559_51123.curmonad);
        modules = (uu___559_51123.modules);
        scope_mods = (uu___559_51123.scope_mods);
        exported_ids = (uu___559_51123.exported_ids);
        trans_exported_ids = (uu___559_51123.trans_exported_ids);
        includes = (uu___559_51123.includes);
        sigaccum = (uu___559_51123.sigaccum);
        sigmap = (uu___559_51123.sigmap);
        iface = (uu___559_51123.iface);
        admitted_iface = (uu___559_51123.admitted_iface);
        expect_typ = b;
        docs = (uu___559_51123.docs);
        remaining_iface_decls = (uu___559_51123.remaining_iface_decls);
        syntax_only = (uu___559_51123.syntax_only);
        ds_hooks = (uu___559_51123.ds_hooks);
        dep_graph = (uu___559_51123.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____51150 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____51150 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____51163 =
            let uu____51167 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____51167  in
          FStar_All.pipe_right uu____51163 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___420_51255  ->
         match uu___420_51255 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____51260 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___578_51272 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___578_51272.curmonad);
        modules = (uu___578_51272.modules);
        scope_mods = (uu___578_51272.scope_mods);
        exported_ids = (uu___578_51272.exported_ids);
        trans_exported_ids = (uu___578_51272.trans_exported_ids);
        includes = (uu___578_51272.includes);
        sigaccum = (uu___578_51272.sigaccum);
        sigmap = (uu___578_51272.sigmap);
        iface = (uu___578_51272.iface);
        admitted_iface = (uu___578_51272.admitted_iface);
        expect_typ = (uu___578_51272.expect_typ);
        docs = (uu___578_51272.docs);
        remaining_iface_decls = (uu___578_51272.remaining_iface_decls);
        syntax_only = (uu___578_51272.syntax_only);
        ds_hooks = (uu___578_51272.ds_hooks);
        dep_graph = (uu___578_51272.dep_graph)
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
      let uu____51296 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____51330  ->
                match uu____51330 with
                | (m,uu____51339) -> FStar_Ident.lid_equals l m))
         in
      match uu____51296 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____51356,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____51390 =
          FStar_List.partition
            (fun uu____51420  ->
               match uu____51420 with
               | (m,uu____51429) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____51390 with
        | (uu____51434,rest) ->
            let uu___603_51468 = env  in
            {
              curmodule = (uu___603_51468.curmodule);
              curmonad = (uu___603_51468.curmonad);
              modules = (uu___603_51468.modules);
              scope_mods = (uu___603_51468.scope_mods);
              exported_ids = (uu___603_51468.exported_ids);
              trans_exported_ids = (uu___603_51468.trans_exported_ids);
              includes = (uu___603_51468.includes);
              sigaccum = (uu___603_51468.sigaccum);
              sigmap = (uu___603_51468.sigmap);
              iface = (uu___603_51468.iface);
              admitted_iface = (uu___603_51468.admitted_iface);
              expect_typ = (uu___603_51468.expect_typ);
              docs = (uu___603_51468.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___603_51468.syntax_only);
              ds_hooks = (uu___603_51468.ds_hooks);
              dep_graph = (uu___603_51468.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____51497 = current_module env  in qual uu____51497 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____51499 =
            let uu____51500 = current_module env  in qual uu____51500 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____51499
            id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___613_51521 = env  in
      {
        curmodule = (uu___613_51521.curmodule);
        curmonad = (uu___613_51521.curmonad);
        modules = (uu___613_51521.modules);
        scope_mods = (uu___613_51521.scope_mods);
        exported_ids = (uu___613_51521.exported_ids);
        trans_exported_ids = (uu___613_51521.trans_exported_ids);
        includes = (uu___613_51521.includes);
        sigaccum = (uu___613_51521.sigaccum);
        sigmap = (uu___613_51521.sigmap);
        iface = (uu___613_51521.iface);
        admitted_iface = (uu___613_51521.admitted_iface);
        expect_typ = (uu___613_51521.expect_typ);
        docs = (uu___613_51521.docs);
        remaining_iface_decls = (uu___613_51521.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___613_51521.ds_hooks);
        dep_graph = (uu___613_51521.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___618_51539 = env  in
      {
        curmodule = (uu___618_51539.curmodule);
        curmonad = (uu___618_51539.curmonad);
        modules = (uu___618_51539.modules);
        scope_mods = (uu___618_51539.scope_mods);
        exported_ids = (uu___618_51539.exported_ids);
        trans_exported_ids = (uu___618_51539.trans_exported_ids);
        includes = (uu___618_51539.includes);
        sigaccum = (uu___618_51539.sigaccum);
        sigmap = (uu___618_51539.sigmap);
        iface = (uu___618_51539.iface);
        admitted_iface = (uu___618_51539.admitted_iface);
        expect_typ = (uu___618_51539.expect_typ);
        docs = (uu___618_51539.docs);
        remaining_iface_decls = (uu___618_51539.remaining_iface_decls);
        syntax_only = (uu___618_51539.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___618_51539.dep_graph)
      }
  
let new_sigmap : 'Auu____51545 . unit -> 'Auu____51545 FStar_Util.smap =
  fun uu____51552  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____51560 = new_sigmap ()  in
    let uu____51565 = new_sigmap ()  in
    let uu____51570 = new_sigmap ()  in
    let uu____51581 = new_sigmap ()  in
    let uu____51594 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____51560;
      trans_exported_ids = uu____51565;
      includes = uu____51570;
      sigaccum = [];
      sigmap = uu____51581;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____51594;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___625_51628 = env  in
      {
        curmodule = (uu___625_51628.curmodule);
        curmonad = (uu___625_51628.curmonad);
        modules = (uu___625_51628.modules);
        scope_mods = (uu___625_51628.scope_mods);
        exported_ids = (uu___625_51628.exported_ids);
        trans_exported_ids = (uu___625_51628.trans_exported_ids);
        includes = (uu___625_51628.includes);
        sigaccum = (uu___625_51628.sigaccum);
        sigmap = (uu___625_51628.sigmap);
        iface = (uu___625_51628.iface);
        admitted_iface = (uu___625_51628.admitted_iface);
        expect_typ = (uu___625_51628.expect_typ);
        docs = (uu___625_51628.docs);
        remaining_iface_decls = (uu___625_51628.remaining_iface_decls);
        syntax_only = (uu___625_51628.syntax_only);
        ds_hooks = (uu___625_51628.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____51656  ->
         match uu____51656 with
         | (m,uu____51663) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___634_51676 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___634_51676.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___637_51677 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index =
          (uu___637_51677.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___637_51677.FStar_Syntax_Syntax.sort)
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
      (fun uu____51780  ->
         match uu____51780 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____51811 =
                 let uu____51812 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____51812 dd dq  in
               FStar_Pervasives_Native.Some uu____51811
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____51852 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____51889 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____51910 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___421_51940  ->
      match uu___421_51940 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____51959 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____51959 cont_t) -> 'Auu____51959 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____51996 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____51996
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____52012  ->
                   match uu____52012 with
                   | (f,uu____52020) ->
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
  fun uu___422_52094  ->
    match uu___422_52094 with
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
              let rec aux uu___423_52170 =
                match uu___423_52170 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____52183 = get_exported_id_set env mname  in
                      match uu____52183 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____52210 = mex eikind  in
                            FStar_ST.op_Bang uu____52210  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____52272 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____52272 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____52327 = qual modul id1  in
                        find_in_module uu____52327
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____52332 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___424_52341  ->
    match uu___424_52341 with
    | Exported_id_field  -> true
    | uu____52344 -> false
  
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
                  let check_local_binding_id uu___425_52468 =
                    match uu___425_52468 with
                    | (id',uu____52471) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___426_52479 =
                    match uu___426_52479 with
                    | (id',uu____52482,uu____52483) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____52488 = current_module env  in
                    FStar_Ident.ids_of_lid uu____52488  in
                  let proc uu___427_52496 =
                    match uu___427_52496 with
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
                        let uu____52505 = FStar_Ident.lid_of_ids curmod_ns
                           in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____52505 id1
                    | uu____52510 -> Cont_ignore  in
                  let rec aux uu___428_52520 =
                    match uu___428_52520 with
                    | a::q ->
                        let uu____52529 = proc a  in
                        option_of_cont (fun uu____52533  -> aux q)
                          uu____52529
                    | [] ->
                        let uu____52534 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____52538  -> FStar_Pervasives_Native.None)
                          uu____52534
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____52546 .
    FStar_Range.range ->
      ('Auu____52546 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____52560  -> match uu____52560 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____52578 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____52578)
          -> 'Auu____52578 -> 'Auu____52578
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____52619 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____52619 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____52663 = unmangleOpName id1  in
      match uu____52663 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____52669 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____52675 =
                 found_local_binding id1.FStar_Ident.idRange r  in
               Cont_ok uu____52675) (fun uu____52677  -> Cont_fail)
            (fun uu____52679  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____52686  -> fun uu____52687  -> Cont_fail)
                 Cont_ignore)
            (fun uu____52695  -> fun uu____52696  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____52770 ->
                let lid = qualify env id1  in
                let uu____52772 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____52772 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____52800 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____52800
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____52824 = current_module env  in qual uu____52824 id1
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
        let rec aux uu___429_52896 =
          match uu___429_52896 with
          | [] ->
              let uu____52901 = module_is_defined env lid  in
              if uu____52901
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____52913 =
                  let uu____52914 = FStar_Ident.path_of_lid ns  in
                  let uu____52918 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____52914 uu____52918  in
                let uu____52923 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____52913 uu____52923  in
              let uu____52924 = module_is_defined env new_lid  in
              if uu____52924
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____52933 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____52939::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____52959 =
          let uu____52961 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____52961  in
        if uu____52959
        then
          let uu____52963 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____52963
           then ()
           else
             (let uu____52968 =
                let uu____52974 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____52974)
                 in
              let uu____52978 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____52968 uu____52978))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____52992 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____52996 = resolve_module_name env modul_orig true  in
          (match uu____52996 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____53001 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___430_53024  ->
             match uu___430_53024 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____53028 -> false) env.scope_mods
  
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
                 let uu____53157 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____53157
                   (FStar_Util.map_option
                      (fun uu____53207  ->
                         match uu____53207 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____53277 = aux ns_rev_prefix ns_last_id  in
              (match uu____53277 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____53340 =
            let uu____53343 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____53343 true  in
          match uu____53340 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____53358 -> do_shorten env ids
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
                  | uu____53479::uu____53480 ->
                      let uu____53483 =
                        let uu____53486 =
                          let uu____53487 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____53488 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____53487 uu____53488
                           in
                        resolve_module_name env uu____53486 true  in
                      (match uu____53483 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____53493 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____53497  ->
                                FStar_Pervasives_Native.None) uu____53493)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___431_53521  ->
      match uu___431_53521 with
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
              let uu____53642 = k_global_def lid1 def  in
              cont_of_option k uu____53642  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____53678 = k_local_binding l  in
                 cont_of_option Cont_fail uu____53678)
              (fun r  ->
                 let uu____53684 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____53684)
              (fun uu____53688  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____53699,uu____53700,uu____53701,l,uu____53703,uu____53704) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___432_53717  ->
               match uu___432_53717 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____53720,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____53732 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____53738,uu____53739,uu____53740) -> FStar_Pervasives_Native.None
    | uu____53741 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____53757 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____53765 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____53765
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____53757 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____53788 =
         let uu____53789 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____53789  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____53788) &&
        (let uu____53793 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____53793 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____53810 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___433_53817  ->
                     match uu___433_53817 with
                     | FStar_Syntax_Syntax.Projector uu____53819 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____53825 -> true
                     | uu____53827 -> false)))
           in
        if uu____53810
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____53832 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___434_53838  ->
                 match uu___434_53838 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____53841 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___435_53847  ->
                    match uu___435_53847 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____53850 -> false)))
             &&
             (let uu____53853 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___436_53859  ->
                        match uu___436_53859 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____53862 -> false))
                 in
              Prims.op_Negation uu____53853))
         in
      if uu____53832 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___439_53914 =
            match uu___439_53914 with
            | (uu____53922,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____53926) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____53931 ->
                     let uu____53948 =
                       let uu____53949 =
                         let uu____53956 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____53956, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____53949  in
                     FStar_Pervasives_Native.Some uu____53948
                 | FStar_Syntax_Syntax.Sig_datacon uu____53959 ->
                     let uu____53975 =
                       let uu____53976 =
                         let uu____53983 =
                           let uu____53984 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____53984
                            in
                         (uu____53983, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____53976  in
                     FStar_Pervasives_Native.Some uu____53975
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____53989,lbs),uu____53991) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____54003 =
                       let uu____54004 =
                         let uu____54011 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____54011, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____54004  in
                     FStar_Pervasives_Native.Some uu____54003
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____54015,uu____54016) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____54020 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___437_54026  ->
                                  match uu___437_54026 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____54029 -> false)))
                        in
                     if uu____54020
                     then
                       let lid2 =
                         let uu____54035 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____54035  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____54037 =
                         FStar_Util.find_map quals
                           (fun uu___438_54042  ->
                              match uu___438_54042 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____54046 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____54037 with
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
                        | uu____54055 ->
                            let uu____54058 =
                              let uu____54059 =
                                let uu____54066 =
                                  let uu____54067 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____54067
                                   in
                                (uu____54066,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____54059  in
                            FStar_Pervasives_Native.Some uu____54058)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____54075 =
                       let uu____54076 =
                         let uu____54081 =
                           let uu____54082 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54082
                            in
                         (se, uu____54081)  in
                       Eff_name uu____54076  in
                     FStar_Pervasives_Native.Some uu____54075
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____54084 =
                       let uu____54085 =
                         let uu____54090 =
                           let uu____54091 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54091
                            in
                         (se, uu____54090)  in
                       Eff_name uu____54085  in
                     FStar_Pervasives_Native.Some uu____54084
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____54092 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____54111 =
                       let uu____54112 =
                         let uu____54119 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____54119, [])  in
                       Term_name uu____54112  in
                     FStar_Pervasives_Native.Some uu____54111
                 | uu____54123 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____54141 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____54141 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____54157 =
            match uu____54157 with
            | (id1,l,dd) ->
                let uu____54169 =
                  let uu____54170 =
                    let uu____54177 =
                      let uu____54178 =
                        let uu____54179 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____54179  in
                      FStar_Syntax_Syntax.fvar uu____54178 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____54177, [])  in
                  Term_name uu____54170  in
                FStar_Pervasives_Native.Some uu____54169
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____54187 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____54187 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____54195 -> FStar_Pervasives_Native.None)
            | uu____54198 -> FStar_Pervasives_Native.None  in
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
        let uu____54236 = try_lookup_name true exclude_interf env lid  in
        match uu____54236 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____54252 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54272 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54272 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____54287 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54313 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54313 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____54329;
             FStar_Syntax_Syntax.sigquals = uu____54330;
             FStar_Syntax_Syntax.sigmeta = uu____54331;
             FStar_Syntax_Syntax.sigattrs = uu____54332;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____54351;
             FStar_Syntax_Syntax.sigquals = uu____54352;
             FStar_Syntax_Syntax.sigmeta = uu____54353;
             FStar_Syntax_Syntax.sigattrs = uu____54354;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____54372,uu____54373,uu____54374,uu____54375,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____54377;
             FStar_Syntax_Syntax.sigquals = uu____54378;
             FStar_Syntax_Syntax.sigmeta = uu____54379;
             FStar_Syntax_Syntax.sigattrs = uu____54380;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____54402 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54428 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54428 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____54438;
             FStar_Syntax_Syntax.sigquals = uu____54439;
             FStar_Syntax_Syntax.sigmeta = uu____54440;
             FStar_Syntax_Syntax.sigattrs = uu____54441;_},uu____54442)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____54452;
             FStar_Syntax_Syntax.sigquals = uu____54453;
             FStar_Syntax_Syntax.sigmeta = uu____54454;
             FStar_Syntax_Syntax.sigattrs = uu____54455;_},uu____54456)
          -> FStar_Pervasives_Native.Some ne
      | uu____54465 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____54484 = try_lookup_effect_name env lid  in
      match uu____54484 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____54489 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54504 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54504 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____54514,uu____54515,uu____54516,uu____54517);
             FStar_Syntax_Syntax.sigrng = uu____54518;
             FStar_Syntax_Syntax.sigquals = uu____54519;
             FStar_Syntax_Syntax.sigmeta = uu____54520;
             FStar_Syntax_Syntax.sigattrs = uu____54521;_},uu____54522)
          ->
          let rec aux new_name =
            let uu____54543 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____54543 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____54564) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____54575 =
                       let uu____54576 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____54576
                        in
                     FStar_Pervasives_Native.Some uu____54575
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____54578 =
                       let uu____54579 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____54579
                        in
                     FStar_Pervasives_Native.Some uu____54578
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____54580,uu____54581,uu____54582,cmp,uu____54584) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____54590 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____54591,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____54597 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___440_54636 =
        match uu___440_54636 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____54646,uu____54647,uu____54648);
             FStar_Syntax_Syntax.sigrng = uu____54649;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____54651;
             FStar_Syntax_Syntax.sigattrs = uu____54652;_},uu____54653)
            -> FStar_Pervasives_Native.Some quals
        | uu____54662 -> FStar_Pervasives_Native.None  in
      let uu____54670 =
        resolve_in_open_namespaces' env lid
          (fun uu____54678  -> FStar_Pervasives_Native.None)
          (fun uu____54682  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____54670 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____54692 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____54710 =
        FStar_List.tryFind
          (fun uu____54725  ->
             match uu____54725 with
             | (mlid,modul) ->
                 let uu____54733 = FStar_Ident.path_of_lid mlid  in
                 uu____54733 = path) env.modules
         in
      match uu____54710 with
      | FStar_Pervasives_Native.Some (uu____54736,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___441_54776 =
        match uu___441_54776 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____54784,lbs),uu____54786);
             FStar_Syntax_Syntax.sigrng = uu____54787;
             FStar_Syntax_Syntax.sigquals = uu____54788;
             FStar_Syntax_Syntax.sigmeta = uu____54789;
             FStar_Syntax_Syntax.sigattrs = uu____54790;_},uu____54791)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____54809 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____54809
        | uu____54810 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____54817  -> FStar_Pervasives_Native.None)
        (fun uu____54819  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___442_54852 =
        match uu___442_54852 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____54863);
             FStar_Syntax_Syntax.sigrng = uu____54864;
             FStar_Syntax_Syntax.sigquals = uu____54865;
             FStar_Syntax_Syntax.sigmeta = uu____54866;
             FStar_Syntax_Syntax.sigattrs = uu____54867;_},uu____54868)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____54894 -> FStar_Pervasives_Native.None)
        | uu____54901 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____54912  -> FStar_Pervasives_Native.None)
        (fun uu____54916  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____54976 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____54976 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____55001 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____55039) ->
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
      let uu____55097 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____55097 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55129 = try_lookup_lid env l  in
      match uu____55129 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____55135 =
            let uu____55136 = FStar_Syntax_Subst.compress e  in
            uu____55136.FStar_Syntax_Syntax.n  in
          (match uu____55135 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____55142 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____55154 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____55154 with
      | (uu____55164,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____55185 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____55189 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____55189 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____55194 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___1304_55225 = env  in
        {
          curmodule = (uu___1304_55225.curmodule);
          curmonad = (uu___1304_55225.curmonad);
          modules = (uu___1304_55225.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___1304_55225.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___1304_55225.sigaccum);
          sigmap = (uu___1304_55225.sigmap);
          iface = (uu___1304_55225.iface);
          admitted_iface = (uu___1304_55225.admitted_iface);
          expect_typ = (uu___1304_55225.expect_typ);
          docs = (uu___1304_55225.docs);
          remaining_iface_decls = (uu___1304_55225.remaining_iface_decls);
          syntax_only = (uu___1304_55225.syntax_only);
          ds_hooks = (uu___1304_55225.ds_hooks);
          dep_graph = (uu___1304_55225.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55241 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____55241 drop_attributes
  
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
               (uu____55311,uu____55312,uu____55313);
             FStar_Syntax_Syntax.sigrng = uu____55314;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____55316;
             FStar_Syntax_Syntax.sigattrs = uu____55317;_},uu____55318)
            ->
            let uu____55325 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___443_55331  ->
                      match uu___443_55331 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____55334 -> false))
               in
            if uu____55325
            then
              let uu____55339 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____55339
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____55342;
             FStar_Syntax_Syntax.sigrng = uu____55343;
             FStar_Syntax_Syntax.sigquals = uu____55344;
             FStar_Syntax_Syntax.sigmeta = uu____55345;
             FStar_Syntax_Syntax.sigattrs = uu____55346;_},uu____55347)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____55373 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____55373
        | uu____55374 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55381  -> FStar_Pervasives_Native.None)
        (fun uu____55383  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___444_55418 =
        match uu___444_55418 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____55428,uu____55429,uu____55430,uu____55431,datas,uu____55433);
             FStar_Syntax_Syntax.sigrng = uu____55434;
             FStar_Syntax_Syntax.sigquals = uu____55435;
             FStar_Syntax_Syntax.sigmeta = uu____55436;
             FStar_Syntax_Syntax.sigattrs = uu____55437;_},uu____55438)
            -> FStar_Pervasives_Native.Some datas
        | uu____55455 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55466  -> FStar_Pervasives_Native.None)
        (fun uu____55470  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____55549 =
    let uu____55550 =
      let uu____55555 =
        let uu____55558 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____55558  in
      let uu____55592 = FStar_ST.op_Bang record_cache  in uu____55555 ::
        uu____55592
       in
    FStar_ST.op_Colon_Equals record_cache uu____55550  in
  let pop1 uu____55658 =
    let uu____55659 =
      let uu____55664 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____55664  in
    FStar_ST.op_Colon_Equals record_cache uu____55659  in
  let snapshot1 uu____55735 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____55759 =
    let uu____55760 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____55760  in
  let insert r =
    let uu____55800 =
      let uu____55805 = let uu____55808 = peek1 ()  in r :: uu____55808  in
      let uu____55811 =
        let uu____55816 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____55816  in
      uu____55805 :: uu____55811  in
    FStar_ST.op_Colon_Equals record_cache uu____55800  in
  let filter1 uu____55884 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____55893 =
      let uu____55898 =
        let uu____55903 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____55903  in
      filtered :: uu____55898  in
    FStar_ST.op_Colon_Equals record_cache uu____55893  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____56829) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___445_56848  ->
                   match uu___445_56848 with
                   | FStar_Syntax_Syntax.RecordType uu____56850 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____56860 ->
                       true
                   | uu____56870 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___446_56895  ->
                      match uu___446_56895 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____56898,uu____56899,uu____56900,uu____56901,uu____56902);
                          FStar_Syntax_Syntax.sigrng = uu____56903;
                          FStar_Syntax_Syntax.sigquals = uu____56904;
                          FStar_Syntax_Syntax.sigmeta = uu____56905;
                          FStar_Syntax_Syntax.sigattrs = uu____56906;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____56917 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___447_56953  ->
                    match uu___447_56953 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____56957,uu____56958,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____56960;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____56962;
                        FStar_Syntax_Syntax.sigattrs = uu____56963;_} ->
                        let uu____56974 =
                          let uu____56975 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____56975  in
                        (match uu____56974 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____56981,t,uu____56983,uu____56984,uu____56985);
                             FStar_Syntax_Syntax.sigrng = uu____56986;
                             FStar_Syntax_Syntax.sigquals = uu____56987;
                             FStar_Syntax_Syntax.sigmeta = uu____56988;
                             FStar_Syntax_Syntax.sigattrs = uu____56989;_} ->
                             let uu____57000 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____57000 with
                              | (formals,uu____57016) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____57070  ->
                                            match uu____57070 with
                                            | (x,q) ->
                                                let uu____57083 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____57083
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____57138  ->
                                            match uu____57138 with
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
                                  ((let uu____57162 =
                                      let uu____57165 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____57165
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____57162);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____57224 =
                                            match uu____57224 with
                                            | (id1,uu____57230) ->
                                                let modul =
                                                  let uu____57233 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____57233.FStar_Ident.str
                                                   in
                                                let uu____57234 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____57234 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____57257 =
                                                         let uu____57258 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____57258
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____57257);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____57303
                                                               =
                                                               let uu____57304
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____57304.FStar_Ident.ident
                                                                in
                                                             uu____57303.FStar_Ident.idText
                                                              in
                                                           let uu____57306 =
                                                             let uu____57307
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____57307
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____57306))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____57359 -> ())
                    | uu____57360 -> ()))
        | uu____57361 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____57383 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____57383 with
        | (ns,id1) ->
            let uu____57400 = peek_record_cache ()  in
            FStar_Util.find_map uu____57400
              (fun record  ->
                 let uu____57406 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____57412  -> FStar_Pervasives_Native.None)
                   uu____57406)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____57414  -> Cont_ignore) (fun uu____57416  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____57422 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____57422)
        (fun k  -> fun uu____57428  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____57444 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____57444 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____57450 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____57470 = try_lookup_record_by_field_name env lid  in
        match uu____57470 with
        | FStar_Pervasives_Native.Some record' when
            let uu____57475 =
              let uu____57477 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____57477  in
            let uu____57478 =
              let uu____57480 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____57480  in
            uu____57475 = uu____57478 ->
            let uu____57482 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____57486  -> Cont_ok ())
               in
            (match uu____57482 with
             | Cont_ok uu____57488 -> true
             | uu____57490 -> false)
        | uu____57494 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____57516 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____57516 with
      | FStar_Pervasives_Native.Some r ->
          let uu____57527 =
            let uu____57533 =
              let uu____57534 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____57535 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____57534 uu____57535  in
            (uu____57533, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____57527
      | uu____57542 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____57560  ->
    let uu____57561 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____57561
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____57582  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___448_57595  ->
      match uu___448_57595 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___449_57633 =
            match uu___449_57633 with
            | Rec_binding uu____57635 -> true
            | uu____57637 -> false  in
          let this_env =
            let uu___1530_57640 = env  in
            let uu____57641 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1530_57640.curmodule);
              curmonad = (uu___1530_57640.curmonad);
              modules = (uu___1530_57640.modules);
              scope_mods = uu____57641;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1530_57640.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1530_57640.sigaccum);
              sigmap = (uu___1530_57640.sigmap);
              iface = (uu___1530_57640.iface);
              admitted_iface = (uu___1530_57640.admitted_iface);
              expect_typ = (uu___1530_57640.expect_typ);
              docs = (uu___1530_57640.docs);
              remaining_iface_decls = (uu___1530_57640.remaining_iface_decls);
              syntax_only = (uu___1530_57640.syntax_only);
              ds_hooks = (uu___1530_57640.ds_hooks);
              dep_graph = (uu___1530_57640.dep_graph)
            }  in
          let uu____57644 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____57644 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____57661 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1538_57686 = env  in
      {
        curmodule = (uu___1538_57686.curmodule);
        curmonad = (uu___1538_57686.curmonad);
        modules = (uu___1538_57686.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1538_57686.exported_ids);
        trans_exported_ids = (uu___1538_57686.trans_exported_ids);
        includes = (uu___1538_57686.includes);
        sigaccum = (uu___1538_57686.sigaccum);
        sigmap = (uu___1538_57686.sigmap);
        iface = (uu___1538_57686.iface);
        admitted_iface = (uu___1538_57686.admitted_iface);
        expect_typ = (uu___1538_57686.expect_typ);
        docs = (uu___1538_57686.docs);
        remaining_iface_decls = (uu___1538_57686.remaining_iface_decls);
        syntax_only = (uu___1538_57686.syntax_only);
        ds_hooks = (uu___1538_57686.ds_hooks);
        dep_graph = (uu___1538_57686.dep_graph)
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
        let uu____57720 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____57720
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____57727 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____57727)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____57771) ->
                let uu____57779 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____57779 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____57784 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____57784
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____57793 =
            let uu____57799 =
              let uu____57801 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____57801 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____57799)  in
          let uu____57805 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____57793 uu____57805  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____57814 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____57827 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____57838 -> (false, true)
            | uu____57851 -> (false, false)  in
          match uu____57814 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____57865 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____57871 =
                       let uu____57873 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____57873  in
                     if uu____57871
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____57865 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____57881 ->
                   (extract_record env globals s;
                    (let uu___1579_57885 = env  in
                     {
                       curmodule = (uu___1579_57885.curmodule);
                       curmonad = (uu___1579_57885.curmonad);
                       modules = (uu___1579_57885.modules);
                       scope_mods = (uu___1579_57885.scope_mods);
                       exported_ids = (uu___1579_57885.exported_ids);
                       trans_exported_ids =
                         (uu___1579_57885.trans_exported_ids);
                       includes = (uu___1579_57885.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1579_57885.sigmap);
                       iface = (uu___1579_57885.iface);
                       admitted_iface = (uu___1579_57885.admitted_iface);
                       expect_typ = (uu___1579_57885.expect_typ);
                       docs = (uu___1579_57885.docs);
                       remaining_iface_decls =
                         (uu___1579_57885.remaining_iface_decls);
                       syntax_only = (uu___1579_57885.syntax_only);
                       ds_hooks = (uu___1579_57885.ds_hooks);
                       dep_graph = (uu___1579_57885.dep_graph)
                     })))
           in
        let env2 =
          let uu___1582_57887 = env1  in
          let uu____57888 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1582_57887.curmodule);
            curmonad = (uu___1582_57887.curmonad);
            modules = (uu___1582_57887.modules);
            scope_mods = uu____57888;
            exported_ids = (uu___1582_57887.exported_ids);
            trans_exported_ids = (uu___1582_57887.trans_exported_ids);
            includes = (uu___1582_57887.includes);
            sigaccum = (uu___1582_57887.sigaccum);
            sigmap = (uu___1582_57887.sigmap);
            iface = (uu___1582_57887.iface);
            admitted_iface = (uu___1582_57887.admitted_iface);
            expect_typ = (uu___1582_57887.expect_typ);
            docs = (uu___1582_57887.docs);
            remaining_iface_decls = (uu___1582_57887.remaining_iface_decls);
            syntax_only = (uu___1582_57887.syntax_only);
            ds_hooks = (uu___1582_57887.ds_hooks);
            dep_graph = (uu___1582_57887.dep_graph)
          }  in
        let uu____57914 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____57940) ->
              let uu____57949 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____57949)
          | uu____57976 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____57914 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____58035  ->
                     match uu____58035 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____58057 =
                                    let uu____58060 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____58060
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____58057);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____58111 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____58111.FStar_Ident.str  in
                                      ((let uu____58113 =
                                          get_exported_id_set env3 modul  in
                                        match uu____58113 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____58135 =
                                              let uu____58136 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____58136
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____58135
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
                let uu___1607_58193 = env3  in
                let uu____58194 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1607_58193.curmodule);
                  curmonad = (uu___1607_58193.curmonad);
                  modules = (uu___1607_58193.modules);
                  scope_mods = uu____58194;
                  exported_ids = (uu___1607_58193.exported_ids);
                  trans_exported_ids = (uu___1607_58193.trans_exported_ids);
                  includes = (uu___1607_58193.includes);
                  sigaccum = (uu___1607_58193.sigaccum);
                  sigmap = (uu___1607_58193.sigmap);
                  iface = (uu___1607_58193.iface);
                  admitted_iface = (uu___1607_58193.admitted_iface);
                  expect_typ = (uu___1607_58193.expect_typ);
                  docs = (uu___1607_58193.docs);
                  remaining_iface_decls =
                    (uu___1607_58193.remaining_iface_decls);
                  syntax_only = (uu___1607_58193.syntax_only);
                  ds_hooks = (uu___1607_58193.ds_hooks);
                  dep_graph = (uu___1607_58193.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____58255 =
        let uu____58260 = resolve_module_name env ns false  in
        match uu____58260 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____58275 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____58293  ->
                      match uu____58293 with
                      | (m,uu____58300) ->
                          let uu____58301 =
                            let uu____58303 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____58303 "."  in
                          let uu____58306 =
                            let uu____58308 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____58308 "."  in
                          FStar_Util.starts_with uu____58301 uu____58306))
               in
            if uu____58275
            then (ns, Open_namespace)
            else
              (let uu____58318 =
                 let uu____58324 =
                   let uu____58326 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____58326
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____58324)  in
               let uu____58330 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____58318 uu____58330)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____58255 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____58352 = resolve_module_name env ns false  in
      match uu____58352 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____58362 = current_module env1  in
              uu____58362.FStar_Ident.str  in
            (let uu____58364 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____58364 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____58388 =
                   let uu____58391 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____58391
                    in
                 FStar_ST.op_Colon_Equals incl uu____58388);
            (match () with
             | () ->
                 let uu____58440 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____58440 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____58460 =
                          let uu____58557 = get_exported_id_set env1 curmod
                             in
                          let uu____58604 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____58557, uu____58604)  in
                        match uu____58460 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____59020 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____59020  in
                              let ex = cur_exports k  in
                              (let uu____59121 =
                                 let uu____59125 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____59125 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____59121);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____59217 =
                                     let uu____59221 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____59221 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____59217)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____59270 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____59372 =
                        let uu____59378 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____59378)
                         in
                      let uu____59382 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____59372 uu____59382))))
      | uu____59383 ->
          let uu____59386 =
            let uu____59392 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____59392)  in
          let uu____59396 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____59386 uu____59396
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____59413 = module_is_defined env l  in
        if uu____59413
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____59420 =
             let uu____59426 =
               let uu____59428 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____59428  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____59426)  in
           let uu____59432 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____59420 uu____59432)
  
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
            ((let uu____59455 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____59455 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____59459 = FStar_Ident.range_of_lid l  in
                  let uu____59460 =
                    let uu____59466 =
                      let uu____59468 = FStar_Ident.string_of_lid l  in
                      let uu____59470 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____59472 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____59468 uu____59470 uu____59472
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____59466)  in
                  FStar_Errors.log_issue uu____59459 uu____59460);
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
                      let uu____59518 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____59518 ->
                      let uu____59523 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____59523 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____59538;
                              FStar_Syntax_Syntax.sigrng = uu____59539;
                              FStar_Syntax_Syntax.sigquals = uu____59540;
                              FStar_Syntax_Syntax.sigmeta = uu____59541;
                              FStar_Syntax_Syntax.sigattrs = uu____59542;_},uu____59543)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____59561;
                              FStar_Syntax_Syntax.sigrng = uu____59562;
                              FStar_Syntax_Syntax.sigquals = uu____59563;
                              FStar_Syntax_Syntax.sigmeta = uu____59564;
                              FStar_Syntax_Syntax.sigattrs = uu____59565;_},uu____59566)
                           -> lids
                       | uu____59594 ->
                           ((let uu____59603 =
                               let uu____59605 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____59605  in
                             if uu____59603
                             then
                               let uu____59608 = FStar_Ident.range_of_lid l
                                  in
                               let uu____59609 =
                                 let uu____59615 =
                                   let uu____59617 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____59617
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____59615)
                                  in
                               FStar_Errors.log_issue uu____59608 uu____59609
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1710_59634 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1710_59634.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1710_59634.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1710_59634.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1710_59634.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____59636 -> lids) [])
         in
      let uu___1715_59637 = m  in
      let uu____59638 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____59648,uu____59649) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1724_59652 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1724_59652.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1724_59652.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1724_59652.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1724_59652.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____59653 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1715_59637.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____59638;
        FStar_Syntax_Syntax.exports =
          (uu___1715_59637.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1715_59637.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____59677) ->
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
                                (lid,uu____59698,uu____59699,uu____59700,uu____59701,uu____59702)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____59718,uu____59719)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____59736 =
                                        let uu____59743 =
                                          let uu____59744 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____59745 =
                                            let uu____59752 =
                                              let uu____59753 =
                                                let uu____59768 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____59768)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____59753
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____59752
                                             in
                                          uu____59745
                                            FStar_Pervasives_Native.None
                                            uu____59744
                                           in
                                        (lid, univ_names, uu____59743)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____59736
                                       in
                                    let se2 =
                                      let uu___1756_59782 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1756_59782.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1756_59782.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1756_59782.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____59792 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____59796,uu____59797) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____59806,lbs),uu____59808)
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
                             let uu____59826 =
                               let uu____59828 =
                                 let uu____59829 =
                                   let uu____59832 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____59832.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____59829.FStar_Syntax_Syntax.v  in
                               uu____59828.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____59826))
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
                               let uu____59849 =
                                 let uu____59852 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____59852.FStar_Syntax_Syntax.fv_name  in
                               uu____59849.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1779_59857 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1779_59857.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1779_59857.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1779_59857.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____59867 -> ()));
      (let curmod =
         let uu____59870 = current_module env  in uu____59870.FStar_Ident.str
          in
       (let uu____59872 =
          let uu____59969 = get_exported_id_set env curmod  in
          let uu____60016 = get_trans_exported_id_set env curmod  in
          (uu____59969, uu____60016)  in
        match uu____59872 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____60435 = cur_ex eikind  in
                FStar_ST.op_Bang uu____60435  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____60541 =
                let uu____60545 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____60545  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____60541  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____60594 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1797_60692 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1797_60692.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1797_60692.exported_ids);
                    trans_exported_ids = (uu___1797_60692.trans_exported_ids);
                    includes = (uu___1797_60692.includes);
                    sigaccum = [];
                    sigmap = (uu___1797_60692.sigmap);
                    iface = (uu___1797_60692.iface);
                    admitted_iface = (uu___1797_60692.admitted_iface);
                    expect_typ = (uu___1797_60692.expect_typ);
                    docs = (uu___1797_60692.docs);
                    remaining_iface_decls =
                      (uu___1797_60692.remaining_iface_decls);
                    syntax_only = (uu___1797_60692.syntax_only);
                    ds_hooks = (uu___1797_60692.ds_hooks);
                    dep_graph = (uu___1797_60692.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____60719  ->
         push_record_cache ();
         (let uu____60722 =
            let uu____60725 = FStar_ST.op_Bang stack  in env :: uu____60725
             in
          FStar_ST.op_Colon_Equals stack uu____60722);
         (let uu___1803_60774 = env  in
          let uu____60775 = FStar_Util.smap_copy env.exported_ids  in
          let uu____60780 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____60785 = FStar_Util.smap_copy env.includes  in
          let uu____60796 = FStar_Util.smap_copy env.sigmap  in
          let uu____60809 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1803_60774.curmodule);
            curmonad = (uu___1803_60774.curmonad);
            modules = (uu___1803_60774.modules);
            scope_mods = (uu___1803_60774.scope_mods);
            exported_ids = uu____60775;
            trans_exported_ids = uu____60780;
            includes = uu____60785;
            sigaccum = (uu___1803_60774.sigaccum);
            sigmap = uu____60796;
            iface = (uu___1803_60774.iface);
            admitted_iface = (uu___1803_60774.admitted_iface);
            expect_typ = (uu___1803_60774.expect_typ);
            docs = uu____60809;
            remaining_iface_decls = (uu___1803_60774.remaining_iface_decls);
            syntax_only = (uu___1803_60774.syntax_only);
            ds_hooks = (uu___1803_60774.ds_hooks);
            dep_graph = (uu___1803_60774.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____60817  ->
    FStar_Util.atomically
      (fun uu____60824  ->
         let uu____60825 = FStar_ST.op_Bang stack  in
         match uu____60825 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____60880 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____60927 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____60931 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____60973 = FStar_Util.smap_try_find sm' k  in
              match uu____60973 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1838_61004 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1838_61004.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1838_61004.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1838_61004.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1838_61004.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____61005 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____61013 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____61040 = finish env modul1  in (uu____61040, modul1)
  
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
      let uu____61109 =
        let uu____61113 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____61113  in
      FStar_Util.set_elements uu____61109  in
    let fields =
      let uu____61176 =
        let uu____61180 = e Exported_id_field  in
        FStar_ST.op_Bang uu____61180  in
      FStar_Util.set_elements uu____61176  in
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
          let uu____61272 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____61272  in
        let fields =
          let uu____61286 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____61286  in
        (fun uu___450_61294  ->
           match uu___450_61294 with
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
  'Auu____61398 .
    'Auu____61398 Prims.list FStar_Pervasives_Native.option ->
      'Auu____61398 Prims.list FStar_ST.ref
  =
  fun uu___451_61411  ->
    match uu___451_61411 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____61454 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____61454 as_exported_ids  in
      let uu____61460 = as_ids_opt env.exported_ids  in
      let uu____61463 = as_ids_opt env.trans_exported_ids  in
      let uu____61466 =
        let uu____61471 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____61471 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____61460;
        mii_trans_exported_ids = uu____61463;
        mii_includes = uu____61466
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
                let uu____61560 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____61560 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___452_61582 =
                  match uu___452_61582 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____61594  ->
                     match uu____61594 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____61620 =
                    let uu____61625 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____61625, Open_namespace)  in
                  [uu____61620]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____61656 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____61656);
              (match () with
               | () ->
                   ((let uu____61661 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____61661);
                    (match () with
                     | () ->
                         ((let uu____61666 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____61666);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1908_61676 = env1  in
                                 let uu____61677 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1908_61676.curmonad);
                                   modules = (uu___1908_61676.modules);
                                   scope_mods = uu____61677;
                                   exported_ids =
                                     (uu___1908_61676.exported_ids);
                                   trans_exported_ids =
                                     (uu___1908_61676.trans_exported_ids);
                                   includes = (uu___1908_61676.includes);
                                   sigaccum = (uu___1908_61676.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1908_61676.expect_typ);
                                   docs = (uu___1908_61676.docs);
                                   remaining_iface_decls =
                                     (uu___1908_61676.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1908_61676.syntax_only);
                                   ds_hooks = (uu___1908_61676.ds_hooks);
                                   dep_graph = (uu___1908_61676.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____61689 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____61715  ->
                      match uu____61715 with
                      | (l,uu____61722) -> FStar_Ident.lid_equals l mname))
               in
            match uu____61689 with
            | FStar_Pervasives_Native.None  ->
                let uu____61732 = prep env  in (uu____61732, false)
            | FStar_Pervasives_Native.Some (uu____61735,m) ->
                ((let uu____61742 =
                    (let uu____61746 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____61746) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____61742
                  then
                    let uu____61749 =
                      let uu____61755 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____61755)
                       in
                    let uu____61759 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____61749 uu____61759
                  else ());
                 (let uu____61762 =
                    let uu____61763 = push env  in prep uu____61763  in
                  (uu____61762, true)))
  
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
          let uu___1929_61781 = env  in
          {
            curmodule = (uu___1929_61781.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1929_61781.modules);
            scope_mods = (uu___1929_61781.scope_mods);
            exported_ids = (uu___1929_61781.exported_ids);
            trans_exported_ids = (uu___1929_61781.trans_exported_ids);
            includes = (uu___1929_61781.includes);
            sigaccum = (uu___1929_61781.sigaccum);
            sigmap = (uu___1929_61781.sigmap);
            iface = (uu___1929_61781.iface);
            admitted_iface = (uu___1929_61781.admitted_iface);
            expect_typ = (uu___1929_61781.expect_typ);
            docs = (uu___1929_61781.docs);
            remaining_iface_decls = (uu___1929_61781.remaining_iface_decls);
            syntax_only = (uu___1929_61781.syntax_only);
            ds_hooks = (uu___1929_61781.ds_hooks);
            dep_graph = (uu___1929_61781.dep_graph)
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
        let uu____61816 = lookup1 lid  in
        match uu____61816 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____61831  ->
                   match uu____61831 with
                   | (lid1,uu____61838) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____61841 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____61841  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____61853 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____61854 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____61853 uu____61854  in
                 let uu____61855 = resolve_module_name env modul true  in
                 match uu____61855 with
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
            let uu____61876 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____61876
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____61906 = lookup1 id1  in
      match uu____61906 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  