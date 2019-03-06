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
    match projectee with | Open_module  -> true | uu____49703 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____49714 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____49934 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____49954 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____49974 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____49994 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____50014 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____50034 -> false
  
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
    | uu____50056 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____50067 -> false
  
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
    ds_push_open_hook = (fun uu____51687  -> fun uu____51688  -> ());
    ds_push_include_hook = (fun uu____51691  -> fun uu____51692  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____51696  -> fun uu____51697  -> fun uu____51698  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____51735 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____51777 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___549_51812 = env  in
      {
        curmodule = (uu___549_51812.curmodule);
        curmonad = (uu___549_51812.curmonad);
        modules = (uu___549_51812.modules);
        scope_mods = (uu___549_51812.scope_mods);
        exported_ids = (uu___549_51812.exported_ids);
        trans_exported_ids = (uu___549_51812.trans_exported_ids);
        includes = (uu___549_51812.includes);
        sigaccum = (uu___549_51812.sigaccum);
        sigmap = (uu___549_51812.sigmap);
        iface = b;
        admitted_iface = (uu___549_51812.admitted_iface);
        expect_typ = (uu___549_51812.expect_typ);
        docs = (uu___549_51812.docs);
        remaining_iface_decls = (uu___549_51812.remaining_iface_decls);
        syntax_only = (uu___549_51812.syntax_only);
        ds_hooks = (uu___549_51812.ds_hooks);
        dep_graph = (uu___549_51812.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___554_51833 = e  in
      {
        curmodule = (uu___554_51833.curmodule);
        curmonad = (uu___554_51833.curmonad);
        modules = (uu___554_51833.modules);
        scope_mods = (uu___554_51833.scope_mods);
        exported_ids = (uu___554_51833.exported_ids);
        trans_exported_ids = (uu___554_51833.trans_exported_ids);
        includes = (uu___554_51833.includes);
        sigaccum = (uu___554_51833.sigaccum);
        sigmap = (uu___554_51833.sigmap);
        iface = (uu___554_51833.iface);
        admitted_iface = b;
        expect_typ = (uu___554_51833.expect_typ);
        docs = (uu___554_51833.docs);
        remaining_iface_decls = (uu___554_51833.remaining_iface_decls);
        syntax_only = (uu___554_51833.syntax_only);
        ds_hooks = (uu___554_51833.ds_hooks);
        dep_graph = (uu___554_51833.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___559_51854 = e  in
      {
        curmodule = (uu___559_51854.curmodule);
        curmonad = (uu___559_51854.curmonad);
        modules = (uu___559_51854.modules);
        scope_mods = (uu___559_51854.scope_mods);
        exported_ids = (uu___559_51854.exported_ids);
        trans_exported_ids = (uu___559_51854.trans_exported_ids);
        includes = (uu___559_51854.includes);
        sigaccum = (uu___559_51854.sigaccum);
        sigmap = (uu___559_51854.sigmap);
        iface = (uu___559_51854.iface);
        admitted_iface = (uu___559_51854.admitted_iface);
        expect_typ = b;
        docs = (uu___559_51854.docs);
        remaining_iface_decls = (uu___559_51854.remaining_iface_decls);
        syntax_only = (uu___559_51854.syntax_only);
        ds_hooks = (uu___559_51854.ds_hooks);
        dep_graph = (uu___559_51854.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____51881 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____51881 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____51894 =
            let uu____51898 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____51898  in
          FStar_All.pipe_right uu____51894 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___420_51986  ->
         match uu___420_51986 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____51991 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___578_52003 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___578_52003.curmonad);
        modules = (uu___578_52003.modules);
        scope_mods = (uu___578_52003.scope_mods);
        exported_ids = (uu___578_52003.exported_ids);
        trans_exported_ids = (uu___578_52003.trans_exported_ids);
        includes = (uu___578_52003.includes);
        sigaccum = (uu___578_52003.sigaccum);
        sigmap = (uu___578_52003.sigmap);
        iface = (uu___578_52003.iface);
        admitted_iface = (uu___578_52003.admitted_iface);
        expect_typ = (uu___578_52003.expect_typ);
        docs = (uu___578_52003.docs);
        remaining_iface_decls = (uu___578_52003.remaining_iface_decls);
        syntax_only = (uu___578_52003.syntax_only);
        ds_hooks = (uu___578_52003.ds_hooks);
        dep_graph = (uu___578_52003.dep_graph)
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
      let uu____52027 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____52061  ->
                match uu____52061 with
                | (m,uu____52070) -> FStar_Ident.lid_equals l m))
         in
      match uu____52027 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____52087,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____52121 =
          FStar_List.partition
            (fun uu____52151  ->
               match uu____52151 with
               | (m,uu____52160) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____52121 with
        | (uu____52165,rest) ->
            let uu___603_52199 = env  in
            {
              curmodule = (uu___603_52199.curmodule);
              curmonad = (uu___603_52199.curmonad);
              modules = (uu___603_52199.modules);
              scope_mods = (uu___603_52199.scope_mods);
              exported_ids = (uu___603_52199.exported_ids);
              trans_exported_ids = (uu___603_52199.trans_exported_ids);
              includes = (uu___603_52199.includes);
              sigaccum = (uu___603_52199.sigaccum);
              sigmap = (uu___603_52199.sigmap);
              iface = (uu___603_52199.iface);
              admitted_iface = (uu___603_52199.admitted_iface);
              expect_typ = (uu___603_52199.expect_typ);
              docs = (uu___603_52199.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___603_52199.syntax_only);
              ds_hooks = (uu___603_52199.ds_hooks);
              dep_graph = (uu___603_52199.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____52228 = current_module env  in qual uu____52228 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____52230 =
            let uu____52231 = current_module env  in qual uu____52231 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____52230
            id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___613_52252 = env  in
      {
        curmodule = (uu___613_52252.curmodule);
        curmonad = (uu___613_52252.curmonad);
        modules = (uu___613_52252.modules);
        scope_mods = (uu___613_52252.scope_mods);
        exported_ids = (uu___613_52252.exported_ids);
        trans_exported_ids = (uu___613_52252.trans_exported_ids);
        includes = (uu___613_52252.includes);
        sigaccum = (uu___613_52252.sigaccum);
        sigmap = (uu___613_52252.sigmap);
        iface = (uu___613_52252.iface);
        admitted_iface = (uu___613_52252.admitted_iface);
        expect_typ = (uu___613_52252.expect_typ);
        docs = (uu___613_52252.docs);
        remaining_iface_decls = (uu___613_52252.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___613_52252.ds_hooks);
        dep_graph = (uu___613_52252.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___618_52270 = env  in
      {
        curmodule = (uu___618_52270.curmodule);
        curmonad = (uu___618_52270.curmonad);
        modules = (uu___618_52270.modules);
        scope_mods = (uu___618_52270.scope_mods);
        exported_ids = (uu___618_52270.exported_ids);
        trans_exported_ids = (uu___618_52270.trans_exported_ids);
        includes = (uu___618_52270.includes);
        sigaccum = (uu___618_52270.sigaccum);
        sigmap = (uu___618_52270.sigmap);
        iface = (uu___618_52270.iface);
        admitted_iface = (uu___618_52270.admitted_iface);
        expect_typ = (uu___618_52270.expect_typ);
        docs = (uu___618_52270.docs);
        remaining_iface_decls = (uu___618_52270.remaining_iface_decls);
        syntax_only = (uu___618_52270.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___618_52270.dep_graph)
      }
  
let new_sigmap : 'Auu____52276 . unit -> 'Auu____52276 FStar_Util.smap =
  fun uu____52283  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____52291 = new_sigmap ()  in
    let uu____52296 = new_sigmap ()  in
    let uu____52301 = new_sigmap ()  in
    let uu____52312 = new_sigmap ()  in
    let uu____52325 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____52291;
      trans_exported_ids = uu____52296;
      includes = uu____52301;
      sigaccum = [];
      sigmap = uu____52312;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____52325;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___625_52359 = env  in
      {
        curmodule = (uu___625_52359.curmodule);
        curmonad = (uu___625_52359.curmonad);
        modules = (uu___625_52359.modules);
        scope_mods = (uu___625_52359.scope_mods);
        exported_ids = (uu___625_52359.exported_ids);
        trans_exported_ids = (uu___625_52359.trans_exported_ids);
        includes = (uu___625_52359.includes);
        sigaccum = (uu___625_52359.sigaccum);
        sigmap = (uu___625_52359.sigmap);
        iface = (uu___625_52359.iface);
        admitted_iface = (uu___625_52359.admitted_iface);
        expect_typ = (uu___625_52359.expect_typ);
        docs = (uu___625_52359.docs);
        remaining_iface_decls = (uu___625_52359.remaining_iface_decls);
        syntax_only = (uu___625_52359.syntax_only);
        ds_hooks = (uu___625_52359.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____52387  ->
         match uu____52387 with
         | (m,uu____52394) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___634_52407 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___634_52407.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___637_52408 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index =
          (uu___637_52408.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___637_52408.FStar_Syntax_Syntax.sort)
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
      (fun uu____52511  ->
         match uu____52511 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____52542 =
                 let uu____52543 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____52543 dd dq  in
               FStar_Pervasives_Native.Some uu____52542
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____52583 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____52621 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____52642 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___421_52672  ->
      match uu___421_52672 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____52691 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____52691 cont_t) -> 'Auu____52691 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____52728 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____52728
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____52744  ->
                   match uu____52744 with
                   | (f,uu____52752) ->
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
  fun uu___422_52826  ->
    match uu___422_52826 with
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
              let rec aux uu___423_52902 =
                match uu___423_52902 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____52915 = get_exported_id_set env mname  in
                      match uu____52915 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____52942 = mex eikind  in
                            FStar_ST.op_Bang uu____52942  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____53004 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____53004 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____53059 = qual modul id1  in
                        find_in_module uu____53059
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____53064 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___424_53073  ->
    match uu___424_53073 with
    | Exported_id_field  -> true
    | uu____53076 -> false
  
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
                  let check_local_binding_id uu___425_53200 =
                    match uu___425_53200 with
                    | (id',uu____53203) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___426_53211 =
                    match uu___426_53211 with
                    | (id',uu____53214,uu____53215) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____53220 = current_module env  in
                    FStar_Ident.ids_of_lid uu____53220  in
                  let proc uu___427_53228 =
                    match uu___427_53228 with
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
                        let uu____53237 = FStar_Ident.lid_of_ids curmod_ns
                           in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____53237 id1
                    | uu____53242 -> Cont_ignore  in
                  let rec aux uu___428_53252 =
                    match uu___428_53252 with
                    | a::q ->
                        let uu____53261 = proc a  in
                        option_of_cont (fun uu____53265  -> aux q)
                          uu____53261
                    | [] ->
                        let uu____53266 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____53270  -> FStar_Pervasives_Native.None)
                          uu____53266
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____53278 .
    FStar_Range.range ->
      ('Auu____53278 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____53292  -> match uu____53292 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____53310 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____53310)
          -> 'Auu____53310 -> 'Auu____53310
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____53351 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____53351 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____53395 = unmangleOpName id1  in
      match uu____53395 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____53401 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____53407 =
                 found_local_binding id1.FStar_Ident.idRange r  in
               Cont_ok uu____53407) (fun uu____53409  -> Cont_fail)
            (fun uu____53411  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____53418  -> fun uu____53419  -> Cont_fail)
                 Cont_ignore)
            (fun uu____53427  -> fun uu____53428  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____53502 ->
                let lid = qualify env id1  in
                let uu____53504 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____53504 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____53532 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____53532
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____53556 = current_module env  in qual uu____53556 id1
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
        let rec aux uu___429_53628 =
          match uu___429_53628 with
          | [] ->
              let uu____53633 = module_is_defined env lid  in
              if uu____53633
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____53645 =
                  let uu____53646 = FStar_Ident.path_of_lid ns  in
                  let uu____53650 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____53646 uu____53650  in
                let uu____53655 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____53645 uu____53655  in
              let uu____53656 = module_is_defined env new_lid  in
              if uu____53656
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____53665 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____53671::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____53691 =
          let uu____53693 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____53693  in
        if uu____53691
        then
          let uu____53695 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____53695
           then ()
           else
             (let uu____53700 =
                let uu____53706 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____53706)
                 in
              let uu____53710 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____53700 uu____53710))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____53724 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____53728 = resolve_module_name env modul_orig true  in
          (match uu____53728 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____53733 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___430_53756  ->
             match uu___430_53756 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____53760 -> false) env.scope_mods
  
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
                 let uu____53889 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____53889
                   (FStar_Util.map_option
                      (fun uu____53939  ->
                         match uu____53939 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____54009 = aux ns_rev_prefix ns_last_id  in
              (match uu____54009 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____54072 =
            let uu____54075 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____54075 true  in
          match uu____54072 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____54090 -> do_shorten env ids
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
                  | uu____54211::uu____54212 ->
                      let uu____54215 =
                        let uu____54218 =
                          let uu____54219 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____54220 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____54219 uu____54220
                           in
                        resolve_module_name env uu____54218 true  in
                      (match uu____54215 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____54225 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____54229  ->
                                FStar_Pervasives_Native.None) uu____54225)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___431_54253  ->
      match uu___431_54253 with
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
              let uu____54374 = k_global_def lid1 def  in
              cont_of_option k uu____54374  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____54410 = k_local_binding l  in
                 cont_of_option Cont_fail uu____54410)
              (fun r  ->
                 let uu____54416 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____54416)
              (fun uu____54420  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____54431,uu____54432,uu____54433,l,uu____54435,uu____54436) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___432_54449  ->
               match uu___432_54449 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____54452,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____54464 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____54470,uu____54471,uu____54472) -> FStar_Pervasives_Native.None
    | uu____54473 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____54489 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____54497 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____54497
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____54489 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____54520 =
         let uu____54521 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____54521  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____54520) &&
        (let uu____54525 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____54525 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____54542 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___433_54549  ->
                     match uu___433_54549 with
                     | FStar_Syntax_Syntax.Projector uu____54551 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____54557 -> true
                     | uu____54559 -> false)))
           in
        if uu____54542
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____54564 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___434_54570  ->
                 match uu___434_54570 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____54573 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___435_54579  ->
                    match uu___435_54579 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____54582 -> false)))
             &&
             (let uu____54585 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___436_54591  ->
                        match uu___436_54591 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____54594 -> false))
                 in
              Prims.op_Negation uu____54585))
         in
      if uu____54564 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___439_54646 =
            match uu___439_54646 with
            | (uu____54654,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____54658) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____54663 ->
                     let uu____54680 =
                       let uu____54681 =
                         let uu____54688 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____54688, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____54681  in
                     FStar_Pervasives_Native.Some uu____54680
                 | FStar_Syntax_Syntax.Sig_datacon uu____54691 ->
                     let uu____54707 =
                       let uu____54708 =
                         let uu____54715 =
                           let uu____54716 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____54716
                            in
                         (uu____54715, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____54708  in
                     FStar_Pervasives_Native.Some uu____54707
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____54721,lbs),uu____54723) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____54735 =
                       let uu____54736 =
                         let uu____54743 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____54743, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____54736  in
                     FStar_Pervasives_Native.Some uu____54735
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____54747,uu____54748) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____54752 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___437_54758  ->
                                  match uu___437_54758 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____54761 -> false)))
                        in
                     if uu____54752
                     then
                       let lid2 =
                         let uu____54767 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____54767  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____54769 =
                         FStar_Util.find_map quals
                           (fun uu___438_54774  ->
                              match uu___438_54774 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____54778 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____54769 with
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
                        | uu____54787 ->
                            let uu____54790 =
                              let uu____54791 =
                                let uu____54798 =
                                  let uu____54799 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____54799
                                   in
                                (uu____54798,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____54791  in
                            FStar_Pervasives_Native.Some uu____54790)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____54807 =
                       let uu____54808 =
                         let uu____54813 =
                           let uu____54814 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54814
                            in
                         (se, uu____54813)  in
                       Eff_name uu____54808  in
                     FStar_Pervasives_Native.Some uu____54807
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____54816 =
                       let uu____54817 =
                         let uu____54822 =
                           let uu____54823 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54823
                            in
                         (se, uu____54822)  in
                       Eff_name uu____54817  in
                     FStar_Pervasives_Native.Some uu____54816
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____54824 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____54843 =
                       let uu____54844 =
                         let uu____54851 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____54851, [])  in
                       Term_name uu____54844  in
                     FStar_Pervasives_Native.Some uu____54843
                 | uu____54855 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____54873 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____54873 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____54889 =
            match uu____54889 with
            | (id1,l,dd) ->
                let uu____54901 =
                  let uu____54902 =
                    let uu____54909 =
                      let uu____54910 =
                        let uu____54911 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____54911  in
                      FStar_Syntax_Syntax.fvar uu____54910 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____54909, [])  in
                  Term_name uu____54902  in
                FStar_Pervasives_Native.Some uu____54901
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____54919 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____54919 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____54927 -> FStar_Pervasives_Native.None)
            | uu____54930 -> FStar_Pervasives_Native.None  in
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
        let uu____54968 = try_lookup_name true exclude_interf env lid  in
        match uu____54968 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____54984 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55004 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____55004 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____55019 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55045 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____55045 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____55061;
             FStar_Syntax_Syntax.sigquals = uu____55062;
             FStar_Syntax_Syntax.sigmeta = uu____55063;
             FStar_Syntax_Syntax.sigattrs = uu____55064;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____55083;
             FStar_Syntax_Syntax.sigquals = uu____55084;
             FStar_Syntax_Syntax.sigmeta = uu____55085;
             FStar_Syntax_Syntax.sigattrs = uu____55086;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____55104,uu____55105,uu____55106,uu____55107,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____55109;
             FStar_Syntax_Syntax.sigquals = uu____55110;
             FStar_Syntax_Syntax.sigmeta = uu____55111;
             FStar_Syntax_Syntax.sigattrs = uu____55112;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____55134 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55160 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____55160 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____55170;
             FStar_Syntax_Syntax.sigquals = uu____55171;
             FStar_Syntax_Syntax.sigmeta = uu____55172;
             FStar_Syntax_Syntax.sigattrs = uu____55173;_},uu____55174)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____55184;
             FStar_Syntax_Syntax.sigquals = uu____55185;
             FStar_Syntax_Syntax.sigmeta = uu____55186;
             FStar_Syntax_Syntax.sigattrs = uu____55187;_},uu____55188)
          -> FStar_Pervasives_Native.Some ne
      | uu____55197 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____55216 = try_lookup_effect_name env lid  in
      match uu____55216 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____55221 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55236 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____55236 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____55246,uu____55247,uu____55248,uu____55249);
             FStar_Syntax_Syntax.sigrng = uu____55250;
             FStar_Syntax_Syntax.sigquals = uu____55251;
             FStar_Syntax_Syntax.sigmeta = uu____55252;
             FStar_Syntax_Syntax.sigattrs = uu____55253;_},uu____55254)
          ->
          let rec aux new_name =
            let uu____55275 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____55275 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____55296) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____55307 =
                       let uu____55308 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____55308
                        in
                     FStar_Pervasives_Native.Some uu____55307
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____55310 =
                       let uu____55311 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____55311
                        in
                     FStar_Pervasives_Native.Some uu____55310
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____55312,uu____55313,uu____55314,cmp,uu____55316) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____55322 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____55323,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____55329 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___440_55368 =
        match uu___440_55368 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____55378,uu____55379,uu____55380);
             FStar_Syntax_Syntax.sigrng = uu____55381;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____55383;
             FStar_Syntax_Syntax.sigattrs = uu____55384;_},uu____55385)
            -> FStar_Pervasives_Native.Some quals
        | uu____55394 -> FStar_Pervasives_Native.None  in
      let uu____55402 =
        resolve_in_open_namespaces' env lid
          (fun uu____55410  -> FStar_Pervasives_Native.None)
          (fun uu____55414  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____55402 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____55424 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____55442 =
        FStar_List.tryFind
          (fun uu____55457  ->
             match uu____55457 with
             | (mlid,modul) ->
                 let uu____55465 = FStar_Ident.path_of_lid mlid  in
                 uu____55465 = path) env.modules
         in
      match uu____55442 with
      | FStar_Pervasives_Native.Some (uu____55468,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___441_55508 =
        match uu___441_55508 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____55516,lbs),uu____55518);
             FStar_Syntax_Syntax.sigrng = uu____55519;
             FStar_Syntax_Syntax.sigquals = uu____55520;
             FStar_Syntax_Syntax.sigmeta = uu____55521;
             FStar_Syntax_Syntax.sigattrs = uu____55522;_},uu____55523)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____55541 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____55541
        | uu____55542 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55549  -> FStar_Pervasives_Native.None)
        (fun uu____55551  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___442_55584 =
        match uu___442_55584 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____55595);
             FStar_Syntax_Syntax.sigrng = uu____55596;
             FStar_Syntax_Syntax.sigquals = uu____55597;
             FStar_Syntax_Syntax.sigmeta = uu____55598;
             FStar_Syntax_Syntax.sigattrs = uu____55599;_},uu____55600)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____55626 -> FStar_Pervasives_Native.None)
        | uu____55633 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55644  -> FStar_Pervasives_Native.None)
        (fun uu____55648  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____55708 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____55708 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____55733 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____55771) ->
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
      let uu____55829 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____55829 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55861 = try_lookup_lid env l  in
      match uu____55861 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____55867 =
            let uu____55868 = FStar_Syntax_Subst.compress e  in
            uu____55868.FStar_Syntax_Syntax.n  in
          (match uu____55867 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____55874 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____55886 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____55886 with
      | (uu____55896,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____55917 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____55921 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____55921 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____55926 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___1304_55957 = env  in
        {
          curmodule = (uu___1304_55957.curmodule);
          curmonad = (uu___1304_55957.curmonad);
          modules = (uu___1304_55957.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___1304_55957.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___1304_55957.sigaccum);
          sigmap = (uu___1304_55957.sigmap);
          iface = (uu___1304_55957.iface);
          admitted_iface = (uu___1304_55957.admitted_iface);
          expect_typ = (uu___1304_55957.expect_typ);
          docs = (uu___1304_55957.docs);
          remaining_iface_decls = (uu___1304_55957.remaining_iface_decls);
          syntax_only = (uu___1304_55957.syntax_only);
          ds_hooks = (uu___1304_55957.ds_hooks);
          dep_graph = (uu___1304_55957.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55973 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____55973 drop_attributes
  
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
               (uu____56043,uu____56044,uu____56045);
             FStar_Syntax_Syntax.sigrng = uu____56046;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____56048;
             FStar_Syntax_Syntax.sigattrs = uu____56049;_},uu____56050)
            ->
            let uu____56057 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___443_56063  ->
                      match uu___443_56063 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____56066 -> false))
               in
            if uu____56057
            then
              let uu____56071 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____56071
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____56074;
             FStar_Syntax_Syntax.sigrng = uu____56075;
             FStar_Syntax_Syntax.sigquals = uu____56076;
             FStar_Syntax_Syntax.sigmeta = uu____56077;
             FStar_Syntax_Syntax.sigattrs = uu____56078;_},uu____56079)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____56105 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____56105
        | uu____56106 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____56113  -> FStar_Pervasives_Native.None)
        (fun uu____56115  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___444_56150 =
        match uu___444_56150 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____56160,uu____56161,uu____56162,uu____56163,datas,uu____56165);
             FStar_Syntax_Syntax.sigrng = uu____56166;
             FStar_Syntax_Syntax.sigquals = uu____56167;
             FStar_Syntax_Syntax.sigmeta = uu____56168;
             FStar_Syntax_Syntax.sigattrs = uu____56169;_},uu____56170)
            -> FStar_Pervasives_Native.Some datas
        | uu____56187 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____56198  -> FStar_Pervasives_Native.None)
        (fun uu____56202  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____56281 =
    let uu____56282 =
      let uu____56287 =
        let uu____56290 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____56290  in
      let uu____56324 = FStar_ST.op_Bang record_cache  in uu____56287 ::
        uu____56324
       in
    FStar_ST.op_Colon_Equals record_cache uu____56282  in
  let pop1 uu____56390 =
    let uu____56391 =
      let uu____56396 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____56396  in
    FStar_ST.op_Colon_Equals record_cache uu____56391  in
  let snapshot1 uu____56467 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____56491 =
    let uu____56492 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____56492  in
  let insert r =
    let uu____56532 =
      let uu____56537 = let uu____56540 = peek1 ()  in r :: uu____56540  in
      let uu____56543 =
        let uu____56548 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____56548  in
      uu____56537 :: uu____56543  in
    FStar_ST.op_Colon_Equals record_cache uu____56532  in
  let filter1 uu____56616 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____56625 =
      let uu____56630 =
        let uu____56635 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____56635  in
      filtered :: uu____56630  in
    FStar_ST.op_Colon_Equals record_cache uu____56625  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____57561) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___445_57580  ->
                   match uu___445_57580 with
                   | FStar_Syntax_Syntax.RecordType uu____57582 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____57592 ->
                       true
                   | uu____57602 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___446_57627  ->
                      match uu___446_57627 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____57630,uu____57631,uu____57632,uu____57633,uu____57634);
                          FStar_Syntax_Syntax.sigrng = uu____57635;
                          FStar_Syntax_Syntax.sigquals = uu____57636;
                          FStar_Syntax_Syntax.sigmeta = uu____57637;
                          FStar_Syntax_Syntax.sigattrs = uu____57638;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____57649 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___447_57685  ->
                    match uu___447_57685 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____57689,uu____57690,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____57692;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____57694;
                        FStar_Syntax_Syntax.sigattrs = uu____57695;_} ->
                        let uu____57706 =
                          let uu____57707 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____57707  in
                        (match uu____57706 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____57713,t,uu____57715,uu____57716,uu____57717);
                             FStar_Syntax_Syntax.sigrng = uu____57718;
                             FStar_Syntax_Syntax.sigquals = uu____57719;
                             FStar_Syntax_Syntax.sigmeta = uu____57720;
                             FStar_Syntax_Syntax.sigattrs = uu____57721;_} ->
                             let uu____57732 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____57732 with
                              | (formals,uu____57748) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____57802  ->
                                            match uu____57802 with
                                            | (x,q) ->
                                                let uu____57815 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____57815
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____57870  ->
                                            match uu____57870 with
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
                                  ((let uu____57894 =
                                      let uu____57897 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____57897
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____57894);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____57956 =
                                            match uu____57956 with
                                            | (id1,uu____57962) ->
                                                let modul =
                                                  let uu____57965 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____57965.FStar_Ident.str
                                                   in
                                                let uu____57966 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____57966 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____57989 =
                                                         let uu____57990 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____57990
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____57989);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____58035
                                                               =
                                                               let uu____58036
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____58036.FStar_Ident.ident
                                                                in
                                                             uu____58035.FStar_Ident.idText
                                                              in
                                                           let uu____58038 =
                                                             let uu____58039
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____58039
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____58038))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____58091 -> ())
                    | uu____58092 -> ()))
        | uu____58093 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____58115 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____58115 with
        | (ns,id1) ->
            let uu____58132 = peek_record_cache ()  in
            FStar_Util.find_map uu____58132
              (fun record  ->
                 let uu____58138 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____58144  -> FStar_Pervasives_Native.None)
                   uu____58138)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____58146  -> Cont_ignore) (fun uu____58148  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____58154 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____58154)
        (fun k  -> fun uu____58160  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____58176 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____58176 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____58182 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____58202 = try_lookup_record_by_field_name env lid  in
        match uu____58202 with
        | FStar_Pervasives_Native.Some record' when
            let uu____58207 =
              let uu____58209 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____58209  in
            let uu____58210 =
              let uu____58212 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____58212  in
            uu____58207 = uu____58210 ->
            let uu____58214 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____58218  -> Cont_ok ())
               in
            (match uu____58214 with
             | Cont_ok uu____58220 -> true
             | uu____58222 -> false)
        | uu____58226 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____58248 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____58248 with
      | FStar_Pervasives_Native.Some r ->
          let uu____58259 =
            let uu____58265 =
              let uu____58266 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____58267 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____58266 uu____58267  in
            (uu____58265, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____58259
      | uu____58274 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____58292  ->
    let uu____58293 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____58293
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____58314  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___448_58327  ->
      match uu___448_58327 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___449_58365 =
            match uu___449_58365 with
            | Rec_binding uu____58367 -> true
            | uu____58369 -> false  in
          let this_env =
            let uu___1530_58372 = env  in
            let uu____58373 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1530_58372.curmodule);
              curmonad = (uu___1530_58372.curmonad);
              modules = (uu___1530_58372.modules);
              scope_mods = uu____58373;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1530_58372.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1530_58372.sigaccum);
              sigmap = (uu___1530_58372.sigmap);
              iface = (uu___1530_58372.iface);
              admitted_iface = (uu___1530_58372.admitted_iface);
              expect_typ = (uu___1530_58372.expect_typ);
              docs = (uu___1530_58372.docs);
              remaining_iface_decls = (uu___1530_58372.remaining_iface_decls);
              syntax_only = (uu___1530_58372.syntax_only);
              ds_hooks = (uu___1530_58372.ds_hooks);
              dep_graph = (uu___1530_58372.dep_graph)
            }  in
          let uu____58376 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____58376 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____58393 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1538_58418 = env  in
      {
        curmodule = (uu___1538_58418.curmodule);
        curmonad = (uu___1538_58418.curmonad);
        modules = (uu___1538_58418.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1538_58418.exported_ids);
        trans_exported_ids = (uu___1538_58418.trans_exported_ids);
        includes = (uu___1538_58418.includes);
        sigaccum = (uu___1538_58418.sigaccum);
        sigmap = (uu___1538_58418.sigmap);
        iface = (uu___1538_58418.iface);
        admitted_iface = (uu___1538_58418.admitted_iface);
        expect_typ = (uu___1538_58418.expect_typ);
        docs = (uu___1538_58418.docs);
        remaining_iface_decls = (uu___1538_58418.remaining_iface_decls);
        syntax_only = (uu___1538_58418.syntax_only);
        ds_hooks = (uu___1538_58418.ds_hooks);
        dep_graph = (uu___1538_58418.dep_graph)
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
        let uu____58452 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____58452
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____58459 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____58459)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____58503) ->
                let uu____58511 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____58511 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____58516 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____58516
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____58525 =
            let uu____58531 =
              let uu____58533 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____58533 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____58531)  in
          let uu____58537 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____58525 uu____58537  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____58546 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____58559 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____58570 -> (false, true)
            | uu____58583 -> (false, false)  in
          match uu____58546 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____58597 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____58603 =
                       let uu____58605 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____58605  in
                     if uu____58603
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____58597 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____58613 ->
                   (extract_record env globals s;
                    (let uu___1579_58617 = env  in
                     {
                       curmodule = (uu___1579_58617.curmodule);
                       curmonad = (uu___1579_58617.curmonad);
                       modules = (uu___1579_58617.modules);
                       scope_mods = (uu___1579_58617.scope_mods);
                       exported_ids = (uu___1579_58617.exported_ids);
                       trans_exported_ids =
                         (uu___1579_58617.trans_exported_ids);
                       includes = (uu___1579_58617.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1579_58617.sigmap);
                       iface = (uu___1579_58617.iface);
                       admitted_iface = (uu___1579_58617.admitted_iface);
                       expect_typ = (uu___1579_58617.expect_typ);
                       docs = (uu___1579_58617.docs);
                       remaining_iface_decls =
                         (uu___1579_58617.remaining_iface_decls);
                       syntax_only = (uu___1579_58617.syntax_only);
                       ds_hooks = (uu___1579_58617.ds_hooks);
                       dep_graph = (uu___1579_58617.dep_graph)
                     })))
           in
        let env2 =
          let uu___1582_58619 = env1  in
          let uu____58620 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1582_58619.curmodule);
            curmonad = (uu___1582_58619.curmonad);
            modules = (uu___1582_58619.modules);
            scope_mods = uu____58620;
            exported_ids = (uu___1582_58619.exported_ids);
            trans_exported_ids = (uu___1582_58619.trans_exported_ids);
            includes = (uu___1582_58619.includes);
            sigaccum = (uu___1582_58619.sigaccum);
            sigmap = (uu___1582_58619.sigmap);
            iface = (uu___1582_58619.iface);
            admitted_iface = (uu___1582_58619.admitted_iface);
            expect_typ = (uu___1582_58619.expect_typ);
            docs = (uu___1582_58619.docs);
            remaining_iface_decls = (uu___1582_58619.remaining_iface_decls);
            syntax_only = (uu___1582_58619.syntax_only);
            ds_hooks = (uu___1582_58619.ds_hooks);
            dep_graph = (uu___1582_58619.dep_graph)
          }  in
        let uu____58646 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____58672) ->
              let uu____58681 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____58681)
          | uu____58708 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____58646 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____58767  ->
                     match uu____58767 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____58789 =
                                    let uu____58792 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____58792
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____58789);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____58843 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____58843.FStar_Ident.str  in
                                      ((let uu____58845 =
                                          get_exported_id_set env3 modul  in
                                        match uu____58845 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____58867 =
                                              let uu____58868 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____58868
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____58867
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
                let uu___1607_58925 = env3  in
                let uu____58926 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1607_58925.curmodule);
                  curmonad = (uu___1607_58925.curmonad);
                  modules = (uu___1607_58925.modules);
                  scope_mods = uu____58926;
                  exported_ids = (uu___1607_58925.exported_ids);
                  trans_exported_ids = (uu___1607_58925.trans_exported_ids);
                  includes = (uu___1607_58925.includes);
                  sigaccum = (uu___1607_58925.sigaccum);
                  sigmap = (uu___1607_58925.sigmap);
                  iface = (uu___1607_58925.iface);
                  admitted_iface = (uu___1607_58925.admitted_iface);
                  expect_typ = (uu___1607_58925.expect_typ);
                  docs = (uu___1607_58925.docs);
                  remaining_iface_decls =
                    (uu___1607_58925.remaining_iface_decls);
                  syntax_only = (uu___1607_58925.syntax_only);
                  ds_hooks = (uu___1607_58925.ds_hooks);
                  dep_graph = (uu___1607_58925.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____58987 =
        let uu____58992 = resolve_module_name env ns false  in
        match uu____58992 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____59007 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____59025  ->
                      match uu____59025 with
                      | (m,uu____59032) ->
                          let uu____59033 =
                            let uu____59035 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____59035 "."  in
                          let uu____59038 =
                            let uu____59040 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____59040 "."  in
                          FStar_Util.starts_with uu____59033 uu____59038))
               in
            if uu____59007
            then (ns, Open_namespace)
            else
              (let uu____59050 =
                 let uu____59056 =
                   let uu____59058 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____59058
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____59056)  in
               let uu____59062 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____59050 uu____59062)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____58987 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____59084 = resolve_module_name env ns false  in
      match uu____59084 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____59094 = current_module env1  in
              uu____59094.FStar_Ident.str  in
            (let uu____59096 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____59096 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____59120 =
                   let uu____59123 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____59123
                    in
                 FStar_ST.op_Colon_Equals incl uu____59120);
            (match () with
             | () ->
                 let uu____59172 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____59172 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____59192 =
                          let uu____59289 = get_exported_id_set env1 curmod
                             in
                          let uu____59336 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____59289, uu____59336)  in
                        match uu____59192 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____59752 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____59752  in
                              let ex = cur_exports k  in
                              (let uu____59853 =
                                 let uu____59857 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____59857 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____59853);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____59949 =
                                     let uu____59953 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____59953 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____59949)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____60002 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____60104 =
                        let uu____60110 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____60110)
                         in
                      let uu____60114 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____60104 uu____60114))))
      | uu____60115 ->
          let uu____60118 =
            let uu____60124 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____60124)  in
          let uu____60128 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____60118 uu____60128
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____60145 = module_is_defined env l  in
        if uu____60145
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____60152 =
             let uu____60158 =
               let uu____60160 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____60160  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____60158)  in
           let uu____60164 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____60152 uu____60164)
  
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
            ((let uu____60187 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____60187 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____60191 = FStar_Ident.range_of_lid l  in
                  let uu____60192 =
                    let uu____60198 =
                      let uu____60200 = FStar_Ident.string_of_lid l  in
                      let uu____60202 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____60204 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____60200 uu____60202 uu____60204
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____60198)  in
                  FStar_Errors.log_issue uu____60191 uu____60192);
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
                      let uu____60250 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____60250 ->
                      let uu____60255 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____60255 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____60270;
                              FStar_Syntax_Syntax.sigrng = uu____60271;
                              FStar_Syntax_Syntax.sigquals = uu____60272;
                              FStar_Syntax_Syntax.sigmeta = uu____60273;
                              FStar_Syntax_Syntax.sigattrs = uu____60274;_},uu____60275)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____60293;
                              FStar_Syntax_Syntax.sigrng = uu____60294;
                              FStar_Syntax_Syntax.sigquals = uu____60295;
                              FStar_Syntax_Syntax.sigmeta = uu____60296;
                              FStar_Syntax_Syntax.sigattrs = uu____60297;_},uu____60298)
                           -> lids
                       | uu____60326 ->
                           ((let uu____60335 =
                               let uu____60337 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____60337  in
                             if uu____60335
                             then
                               let uu____60340 = FStar_Ident.range_of_lid l
                                  in
                               let uu____60341 =
                                 let uu____60347 =
                                   let uu____60349 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____60349
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____60347)
                                  in
                               FStar_Errors.log_issue uu____60340 uu____60341
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1710_60366 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1710_60366.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1710_60366.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1710_60366.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1710_60366.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____60368 -> lids) [])
         in
      let uu___1715_60369 = m  in
      let uu____60370 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____60380,uu____60381) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1724_60384 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1724_60384.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1724_60384.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1724_60384.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1724_60384.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____60385 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1715_60369.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____60370;
        FStar_Syntax_Syntax.exports =
          (uu___1715_60369.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1715_60369.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____60409) ->
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
                                (lid,uu____60430,uu____60431,uu____60432,uu____60433,uu____60434)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____60450,uu____60451)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____60468 =
                                        let uu____60475 =
                                          let uu____60476 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____60477 =
                                            let uu____60484 =
                                              let uu____60485 =
                                                let uu____60500 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____60500)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____60485
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____60484
                                             in
                                          uu____60477
                                            FStar_Pervasives_Native.None
                                            uu____60476
                                           in
                                        (lid, univ_names, uu____60475)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____60468
                                       in
                                    let se2 =
                                      let uu___1756_60514 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1756_60514.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1756_60514.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1756_60514.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____60524 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____60528,uu____60529) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____60538,lbs),uu____60540)
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
                             let uu____60558 =
                               let uu____60560 =
                                 let uu____60561 =
                                   let uu____60564 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____60564.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____60561.FStar_Syntax_Syntax.v  in
                               uu____60560.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____60558))
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
                               let uu____60581 =
                                 let uu____60584 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____60584.FStar_Syntax_Syntax.fv_name  in
                               uu____60581.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1779_60589 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1779_60589.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1779_60589.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1779_60589.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____60599 -> ()));
      (let curmod =
         let uu____60602 = current_module env  in uu____60602.FStar_Ident.str
          in
       (let uu____60604 =
          let uu____60701 = get_exported_id_set env curmod  in
          let uu____60748 = get_trans_exported_id_set env curmod  in
          (uu____60701, uu____60748)  in
        match uu____60604 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____61167 = cur_ex eikind  in
                FStar_ST.op_Bang uu____61167  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____61273 =
                let uu____61277 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____61277  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____61273  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____61326 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1797_61424 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1797_61424.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1797_61424.exported_ids);
                    trans_exported_ids = (uu___1797_61424.trans_exported_ids);
                    includes = (uu___1797_61424.includes);
                    sigaccum = [];
                    sigmap = (uu___1797_61424.sigmap);
                    iface = (uu___1797_61424.iface);
                    admitted_iface = (uu___1797_61424.admitted_iface);
                    expect_typ = (uu___1797_61424.expect_typ);
                    docs = (uu___1797_61424.docs);
                    remaining_iface_decls =
                      (uu___1797_61424.remaining_iface_decls);
                    syntax_only = (uu___1797_61424.syntax_only);
                    ds_hooks = (uu___1797_61424.ds_hooks);
                    dep_graph = (uu___1797_61424.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____61451  ->
         push_record_cache ();
         (let uu____61454 =
            let uu____61457 = FStar_ST.op_Bang stack  in env :: uu____61457
             in
          FStar_ST.op_Colon_Equals stack uu____61454);
         (let uu___1803_61506 = env  in
          let uu____61507 = FStar_Util.smap_copy env.exported_ids  in
          let uu____61512 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____61517 = FStar_Util.smap_copy env.includes  in
          let uu____61528 = FStar_Util.smap_copy env.sigmap  in
          let uu____61541 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1803_61506.curmodule);
            curmonad = (uu___1803_61506.curmonad);
            modules = (uu___1803_61506.modules);
            scope_mods = (uu___1803_61506.scope_mods);
            exported_ids = uu____61507;
            trans_exported_ids = uu____61512;
            includes = uu____61517;
            sigaccum = (uu___1803_61506.sigaccum);
            sigmap = uu____61528;
            iface = (uu___1803_61506.iface);
            admitted_iface = (uu___1803_61506.admitted_iface);
            expect_typ = (uu___1803_61506.expect_typ);
            docs = uu____61541;
            remaining_iface_decls = (uu___1803_61506.remaining_iface_decls);
            syntax_only = (uu___1803_61506.syntax_only);
            ds_hooks = (uu___1803_61506.ds_hooks);
            dep_graph = (uu___1803_61506.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____61549  ->
    FStar_Util.atomically
      (fun uu____61556  ->
         let uu____61557 = FStar_ST.op_Bang stack  in
         match uu____61557 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____61612 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____61659 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____61663 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____61705 = FStar_Util.smap_try_find sm' k  in
              match uu____61705 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1838_61736 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1838_61736.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1838_61736.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1838_61736.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1838_61736.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____61737 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____61745 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____61772 = finish env modul1  in (uu____61772, modul1)
  
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
      let uu____61841 =
        let uu____61845 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____61845  in
      FStar_Util.set_elements uu____61841  in
    let fields =
      let uu____61908 =
        let uu____61912 = e Exported_id_field  in
        FStar_ST.op_Bang uu____61912  in
      FStar_Util.set_elements uu____61908  in
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
          let uu____62004 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____62004  in
        let fields =
          let uu____62018 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____62018  in
        (fun uu___450_62026  ->
           match uu___450_62026 with
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
  'Auu____62130 .
    'Auu____62130 Prims.list FStar_Pervasives_Native.option ->
      'Auu____62130 Prims.list FStar_ST.ref
  =
  fun uu___451_62143  ->
    match uu___451_62143 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____62186 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____62186 as_exported_ids  in
      let uu____62192 = as_ids_opt env.exported_ids  in
      let uu____62195 = as_ids_opt env.trans_exported_ids  in
      let uu____62198 =
        let uu____62203 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____62203 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____62192;
        mii_trans_exported_ids = uu____62195;
        mii_includes = uu____62198
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
                let uu____62292 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____62292 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___452_62314 =
                  match uu___452_62314 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____62326  ->
                     match uu____62326 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____62352 =
                    let uu____62357 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____62357, Open_namespace)  in
                  [uu____62352]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____62388 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____62388);
              (match () with
               | () ->
                   ((let uu____62393 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____62393);
                    (match () with
                     | () ->
                         ((let uu____62398 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____62398);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1908_62408 = env1  in
                                 let uu____62409 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1908_62408.curmonad);
                                   modules = (uu___1908_62408.modules);
                                   scope_mods = uu____62409;
                                   exported_ids =
                                     (uu___1908_62408.exported_ids);
                                   trans_exported_ids =
                                     (uu___1908_62408.trans_exported_ids);
                                   includes = (uu___1908_62408.includes);
                                   sigaccum = (uu___1908_62408.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1908_62408.expect_typ);
                                   docs = (uu___1908_62408.docs);
                                   remaining_iface_decls =
                                     (uu___1908_62408.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1908_62408.syntax_only);
                                   ds_hooks = (uu___1908_62408.ds_hooks);
                                   dep_graph = (uu___1908_62408.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____62421 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____62447  ->
                      match uu____62447 with
                      | (l,uu____62454) -> FStar_Ident.lid_equals l mname))
               in
            match uu____62421 with
            | FStar_Pervasives_Native.None  ->
                let uu____62464 = prep env  in (uu____62464, false)
            | FStar_Pervasives_Native.Some (uu____62467,m) ->
                ((let uu____62474 =
                    (let uu____62478 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____62478) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____62474
                  then
                    let uu____62481 =
                      let uu____62487 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____62487)
                       in
                    let uu____62491 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____62481 uu____62491
                  else ());
                 (let uu____62494 =
                    let uu____62495 = push env  in prep uu____62495  in
                  (uu____62494, true)))
  
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
          let uu___1929_62513 = env  in
          {
            curmodule = (uu___1929_62513.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1929_62513.modules);
            scope_mods = (uu___1929_62513.scope_mods);
            exported_ids = (uu___1929_62513.exported_ids);
            trans_exported_ids = (uu___1929_62513.trans_exported_ids);
            includes = (uu___1929_62513.includes);
            sigaccum = (uu___1929_62513.sigaccum);
            sigmap = (uu___1929_62513.sigmap);
            iface = (uu___1929_62513.iface);
            admitted_iface = (uu___1929_62513.admitted_iface);
            expect_typ = (uu___1929_62513.expect_typ);
            docs = (uu___1929_62513.docs);
            remaining_iface_decls = (uu___1929_62513.remaining_iface_decls);
            syntax_only = (uu___1929_62513.syntax_only);
            ds_hooks = (uu___1929_62513.ds_hooks);
            dep_graph = (uu___1929_62513.dep_graph)
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
        let uu____62548 = lookup1 lid  in
        match uu____62548 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____62563  ->
                   match uu____62563 with
                   | (lid1,uu____62570) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____62573 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____62573  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____62585 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____62586 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____62585 uu____62586  in
                 let uu____62587 = resolve_module_name env modul true  in
                 match uu____62587 with
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
            let uu____62608 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____62608
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____62638 = lookup1 id1  in
      match uu____62638 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  