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
    match projectee with | Open_module  -> true | uu____48979 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____48990 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____49210 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____49229 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____49248 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____49267 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____49286 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____49305 -> false
  
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
    | uu____49326 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____49337 -> false
  
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
    ds_push_open_hook = (fun uu____50957  -> fun uu____50958  -> ());
    ds_push_include_hook = (fun uu____50961  -> fun uu____50962  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____50966  -> fun uu____50967  -> fun uu____50968  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____51005 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____51046 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___549_51080 = env  in
      {
        curmodule = (uu___549_51080.curmodule);
        curmonad = (uu___549_51080.curmonad);
        modules = (uu___549_51080.modules);
        scope_mods = (uu___549_51080.scope_mods);
        exported_ids = (uu___549_51080.exported_ids);
        trans_exported_ids = (uu___549_51080.trans_exported_ids);
        includes = (uu___549_51080.includes);
        sigaccum = (uu___549_51080.sigaccum);
        sigmap = (uu___549_51080.sigmap);
        iface = b;
        admitted_iface = (uu___549_51080.admitted_iface);
        expect_typ = (uu___549_51080.expect_typ);
        docs = (uu___549_51080.docs);
        remaining_iface_decls = (uu___549_51080.remaining_iface_decls);
        syntax_only = (uu___549_51080.syntax_only);
        ds_hooks = (uu___549_51080.ds_hooks);
        dep_graph = (uu___549_51080.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___554_51101 = e  in
      {
        curmodule = (uu___554_51101.curmodule);
        curmonad = (uu___554_51101.curmonad);
        modules = (uu___554_51101.modules);
        scope_mods = (uu___554_51101.scope_mods);
        exported_ids = (uu___554_51101.exported_ids);
        trans_exported_ids = (uu___554_51101.trans_exported_ids);
        includes = (uu___554_51101.includes);
        sigaccum = (uu___554_51101.sigaccum);
        sigmap = (uu___554_51101.sigmap);
        iface = (uu___554_51101.iface);
        admitted_iface = b;
        expect_typ = (uu___554_51101.expect_typ);
        docs = (uu___554_51101.docs);
        remaining_iface_decls = (uu___554_51101.remaining_iface_decls);
        syntax_only = (uu___554_51101.syntax_only);
        ds_hooks = (uu___554_51101.ds_hooks);
        dep_graph = (uu___554_51101.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___559_51122 = e  in
      {
        curmodule = (uu___559_51122.curmodule);
        curmonad = (uu___559_51122.curmonad);
        modules = (uu___559_51122.modules);
        scope_mods = (uu___559_51122.scope_mods);
        exported_ids = (uu___559_51122.exported_ids);
        trans_exported_ids = (uu___559_51122.trans_exported_ids);
        includes = (uu___559_51122.includes);
        sigaccum = (uu___559_51122.sigaccum);
        sigmap = (uu___559_51122.sigmap);
        iface = (uu___559_51122.iface);
        admitted_iface = (uu___559_51122.admitted_iface);
        expect_typ = b;
        docs = (uu___559_51122.docs);
        remaining_iface_decls = (uu___559_51122.remaining_iface_decls);
        syntax_only = (uu___559_51122.syntax_only);
        ds_hooks = (uu___559_51122.ds_hooks);
        dep_graph = (uu___559_51122.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____51149 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____51149 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____51162 =
            let uu____51166 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____51166  in
          FStar_All.pipe_right uu____51162 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___420_51254  ->
         match uu___420_51254 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____51259 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___578_51271 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___578_51271.curmonad);
        modules = (uu___578_51271.modules);
        scope_mods = (uu___578_51271.scope_mods);
        exported_ids = (uu___578_51271.exported_ids);
        trans_exported_ids = (uu___578_51271.trans_exported_ids);
        includes = (uu___578_51271.includes);
        sigaccum = (uu___578_51271.sigaccum);
        sigmap = (uu___578_51271.sigmap);
        iface = (uu___578_51271.iface);
        admitted_iface = (uu___578_51271.admitted_iface);
        expect_typ = (uu___578_51271.expect_typ);
        docs = (uu___578_51271.docs);
        remaining_iface_decls = (uu___578_51271.remaining_iface_decls);
        syntax_only = (uu___578_51271.syntax_only);
        ds_hooks = (uu___578_51271.ds_hooks);
        dep_graph = (uu___578_51271.dep_graph)
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
      let uu____51295 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____51329  ->
                match uu____51329 with
                | (m,uu____51338) -> FStar_Ident.lid_equals l m))
         in
      match uu____51295 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____51355,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____51389 =
          FStar_List.partition
            (fun uu____51419  ->
               match uu____51419 with
               | (m,uu____51428) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____51389 with
        | (uu____51433,rest) ->
            let uu___603_51467 = env  in
            {
              curmodule = (uu___603_51467.curmodule);
              curmonad = (uu___603_51467.curmonad);
              modules = (uu___603_51467.modules);
              scope_mods = (uu___603_51467.scope_mods);
              exported_ids = (uu___603_51467.exported_ids);
              trans_exported_ids = (uu___603_51467.trans_exported_ids);
              includes = (uu___603_51467.includes);
              sigaccum = (uu___603_51467.sigaccum);
              sigmap = (uu___603_51467.sigmap);
              iface = (uu___603_51467.iface);
              admitted_iface = (uu___603_51467.admitted_iface);
              expect_typ = (uu___603_51467.expect_typ);
              docs = (uu___603_51467.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___603_51467.syntax_only);
              ds_hooks = (uu___603_51467.ds_hooks);
              dep_graph = (uu___603_51467.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____51496 = current_module env  in qual uu____51496 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____51498 =
            let uu____51499 = current_module env  in qual uu____51499 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____51498
            id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___613_51520 = env  in
      {
        curmodule = (uu___613_51520.curmodule);
        curmonad = (uu___613_51520.curmonad);
        modules = (uu___613_51520.modules);
        scope_mods = (uu___613_51520.scope_mods);
        exported_ids = (uu___613_51520.exported_ids);
        trans_exported_ids = (uu___613_51520.trans_exported_ids);
        includes = (uu___613_51520.includes);
        sigaccum = (uu___613_51520.sigaccum);
        sigmap = (uu___613_51520.sigmap);
        iface = (uu___613_51520.iface);
        admitted_iface = (uu___613_51520.admitted_iface);
        expect_typ = (uu___613_51520.expect_typ);
        docs = (uu___613_51520.docs);
        remaining_iface_decls = (uu___613_51520.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___613_51520.ds_hooks);
        dep_graph = (uu___613_51520.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___618_51538 = env  in
      {
        curmodule = (uu___618_51538.curmodule);
        curmonad = (uu___618_51538.curmonad);
        modules = (uu___618_51538.modules);
        scope_mods = (uu___618_51538.scope_mods);
        exported_ids = (uu___618_51538.exported_ids);
        trans_exported_ids = (uu___618_51538.trans_exported_ids);
        includes = (uu___618_51538.includes);
        sigaccum = (uu___618_51538.sigaccum);
        sigmap = (uu___618_51538.sigmap);
        iface = (uu___618_51538.iface);
        admitted_iface = (uu___618_51538.admitted_iface);
        expect_typ = (uu___618_51538.expect_typ);
        docs = (uu___618_51538.docs);
        remaining_iface_decls = (uu___618_51538.remaining_iface_decls);
        syntax_only = (uu___618_51538.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___618_51538.dep_graph)
      }
  
let new_sigmap : 'Auu____51544 . unit -> 'Auu____51544 FStar_Util.smap =
  fun uu____51551  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____51559 = new_sigmap ()  in
    let uu____51564 = new_sigmap ()  in
    let uu____51569 = new_sigmap ()  in
    let uu____51580 = new_sigmap ()  in
    let uu____51593 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____51559;
      trans_exported_ids = uu____51564;
      includes = uu____51569;
      sigaccum = [];
      sigmap = uu____51580;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____51593;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___625_51627 = env  in
      {
        curmodule = (uu___625_51627.curmodule);
        curmonad = (uu___625_51627.curmonad);
        modules = (uu___625_51627.modules);
        scope_mods = (uu___625_51627.scope_mods);
        exported_ids = (uu___625_51627.exported_ids);
        trans_exported_ids = (uu___625_51627.trans_exported_ids);
        includes = (uu___625_51627.includes);
        sigaccum = (uu___625_51627.sigaccum);
        sigmap = (uu___625_51627.sigmap);
        iface = (uu___625_51627.iface);
        admitted_iface = (uu___625_51627.admitted_iface);
        expect_typ = (uu___625_51627.expect_typ);
        docs = (uu___625_51627.docs);
        remaining_iface_decls = (uu___625_51627.remaining_iface_decls);
        syntax_only = (uu___625_51627.syntax_only);
        ds_hooks = (uu___625_51627.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____51655  ->
         match uu____51655 with
         | (m,uu____51662) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___634_51675 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___634_51675.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___637_51676 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index =
          (uu___637_51676.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___637_51676.FStar_Syntax_Syntax.sort)
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
      (fun uu____51779  ->
         match uu____51779 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____51810 =
                 let uu____51811 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____51811 dd dq  in
               FStar_Pervasives_Native.Some uu____51810
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____51851 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____51888 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____51909 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___421_51939  ->
      match uu___421_51939 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____51958 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____51958 cont_t) -> 'Auu____51958 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____51995 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____51995
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____52011  ->
                   match uu____52011 with
                   | (f,uu____52019) ->
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
  fun uu___422_52093  ->
    match uu___422_52093 with
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
              let rec aux uu___423_52169 =
                match uu___423_52169 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____52182 = get_exported_id_set env mname  in
                      match uu____52182 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____52209 = mex eikind  in
                            FStar_ST.op_Bang uu____52209  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____52271 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____52271 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____52326 = qual modul id1  in
                        find_in_module uu____52326
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____52331 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___424_52340  ->
    match uu___424_52340 with
    | Exported_id_field  -> true
    | uu____52343 -> false
  
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
                  let check_local_binding_id uu___425_52467 =
                    match uu___425_52467 with
                    | (id',uu____52470) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___426_52478 =
                    match uu___426_52478 with
                    | (id',uu____52481,uu____52482) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____52487 = current_module env  in
                    FStar_Ident.ids_of_lid uu____52487  in
                  let proc uu___427_52495 =
                    match uu___427_52495 with
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
                        let uu____52504 = FStar_Ident.lid_of_ids curmod_ns
                           in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____52504 id1
                    | uu____52509 -> Cont_ignore  in
                  let rec aux uu___428_52519 =
                    match uu___428_52519 with
                    | a::q ->
                        let uu____52528 = proc a  in
                        option_of_cont (fun uu____52532  -> aux q)
                          uu____52528
                    | [] ->
                        let uu____52533 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____52537  -> FStar_Pervasives_Native.None)
                          uu____52533
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____52545 .
    FStar_Range.range ->
      ('Auu____52545 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____52559  -> match uu____52559 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____52577 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____52577)
          -> 'Auu____52577 -> 'Auu____52577
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____52618 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____52618 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____52662 = unmangleOpName id1  in
      match uu____52662 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____52668 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____52674 =
                 found_local_binding id1.FStar_Ident.idRange r  in
               Cont_ok uu____52674) (fun uu____52676  -> Cont_fail)
            (fun uu____52678  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____52685  -> fun uu____52686  -> Cont_fail)
                 Cont_ignore)
            (fun uu____52694  -> fun uu____52695  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____52769 ->
                let lid = qualify env id1  in
                let uu____52771 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____52771 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____52799 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____52799
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____52823 = current_module env  in qual uu____52823 id1
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
        let rec aux uu___429_52895 =
          match uu___429_52895 with
          | [] ->
              let uu____52900 = module_is_defined env lid  in
              if uu____52900
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____52912 =
                  let uu____52913 = FStar_Ident.path_of_lid ns  in
                  let uu____52917 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____52913 uu____52917  in
                let uu____52922 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____52912 uu____52922  in
              let uu____52923 = module_is_defined env new_lid  in
              if uu____52923
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____52932 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____52938::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____52958 =
          let uu____52960 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____52960  in
        if uu____52958
        then
          let uu____52962 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____52962
           then ()
           else
             (let uu____52967 =
                let uu____52973 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____52973)
                 in
              let uu____52977 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____52967 uu____52977))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____52991 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____52995 = resolve_module_name env modul_orig true  in
          (match uu____52995 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____53000 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___430_53023  ->
             match uu___430_53023 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____53027 -> false) env.scope_mods
  
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
                 let uu____53156 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____53156
                   (FStar_Util.map_option
                      (fun uu____53206  ->
                         match uu____53206 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____53276 = aux ns_rev_prefix ns_last_id  in
              (match uu____53276 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____53339 =
            let uu____53342 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____53342 true  in
          match uu____53339 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____53357 -> do_shorten env ids
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
                  | uu____53478::uu____53479 ->
                      let uu____53482 =
                        let uu____53485 =
                          let uu____53486 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____53487 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____53486 uu____53487
                           in
                        resolve_module_name env uu____53485 true  in
                      (match uu____53482 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____53492 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____53496  ->
                                FStar_Pervasives_Native.None) uu____53492)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___431_53520  ->
      match uu___431_53520 with
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
              let uu____53641 = k_global_def lid1 def  in
              cont_of_option k uu____53641  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____53677 = k_local_binding l  in
                 cont_of_option Cont_fail uu____53677)
              (fun r  ->
                 let uu____53683 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____53683)
              (fun uu____53687  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____53698,uu____53699,uu____53700,l,uu____53702,uu____53703) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___432_53716  ->
               match uu___432_53716 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____53719,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____53731 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____53737,uu____53738,uu____53739) -> FStar_Pervasives_Native.None
    | uu____53740 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____53756 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____53764 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____53764
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____53756 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____53787 =
         let uu____53788 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____53788  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____53787) &&
        (let uu____53792 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____53792 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____53809 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___433_53816  ->
                     match uu___433_53816 with
                     | FStar_Syntax_Syntax.Projector uu____53818 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____53824 -> true
                     | uu____53826 -> false)))
           in
        if uu____53809
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____53831 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___434_53837  ->
                 match uu___434_53837 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____53840 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___435_53846  ->
                    match uu___435_53846 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____53849 -> false)))
             &&
             (let uu____53852 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___436_53858  ->
                        match uu___436_53858 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____53861 -> false))
                 in
              Prims.op_Negation uu____53852))
         in
      if uu____53831 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___439_53913 =
            match uu___439_53913 with
            | (uu____53921,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____53925) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____53930 ->
                     let uu____53947 =
                       let uu____53948 =
                         let uu____53955 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____53955, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____53948  in
                     FStar_Pervasives_Native.Some uu____53947
                 | FStar_Syntax_Syntax.Sig_datacon uu____53958 ->
                     let uu____53974 =
                       let uu____53975 =
                         let uu____53982 =
                           let uu____53983 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____53983
                            in
                         (uu____53982, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____53975  in
                     FStar_Pervasives_Native.Some uu____53974
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____53988,lbs),uu____53990) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____54002 =
                       let uu____54003 =
                         let uu____54010 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____54010, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____54003  in
                     FStar_Pervasives_Native.Some uu____54002
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____54014,uu____54015) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____54019 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___437_54025  ->
                                  match uu___437_54025 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____54028 -> false)))
                        in
                     if uu____54019
                     then
                       let lid2 =
                         let uu____54034 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____54034  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____54036 =
                         FStar_Util.find_map quals
                           (fun uu___438_54041  ->
                              match uu___438_54041 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____54045 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____54036 with
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
                        | uu____54054 ->
                            let uu____54057 =
                              let uu____54058 =
                                let uu____54065 =
                                  let uu____54066 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____54066
                                   in
                                (uu____54065,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____54058  in
                            FStar_Pervasives_Native.Some uu____54057)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____54074 =
                       let uu____54075 =
                         let uu____54080 =
                           let uu____54081 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54081
                            in
                         (se, uu____54080)  in
                       Eff_name uu____54075  in
                     FStar_Pervasives_Native.Some uu____54074
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____54083 =
                       let uu____54084 =
                         let uu____54089 =
                           let uu____54090 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54090
                            in
                         (se, uu____54089)  in
                       Eff_name uu____54084  in
                     FStar_Pervasives_Native.Some uu____54083
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____54091 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____54110 =
                       let uu____54111 =
                         let uu____54118 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____54118, [])  in
                       Term_name uu____54111  in
                     FStar_Pervasives_Native.Some uu____54110
                 | uu____54122 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____54140 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____54140 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____54156 =
            match uu____54156 with
            | (id1,l,dd) ->
                let uu____54168 =
                  let uu____54169 =
                    let uu____54176 =
                      let uu____54177 =
                        let uu____54178 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____54178  in
                      FStar_Syntax_Syntax.fvar uu____54177 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____54176, [])  in
                  Term_name uu____54169  in
                FStar_Pervasives_Native.Some uu____54168
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____54186 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____54186 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____54194 -> FStar_Pervasives_Native.None)
            | uu____54197 -> FStar_Pervasives_Native.None  in
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
        let uu____54235 = try_lookup_name true exclude_interf env lid  in
        match uu____54235 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____54251 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54271 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54271 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____54286 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54312 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54312 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____54328;
             FStar_Syntax_Syntax.sigquals = uu____54329;
             FStar_Syntax_Syntax.sigmeta = uu____54330;
             FStar_Syntax_Syntax.sigattrs = uu____54331;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____54350;
             FStar_Syntax_Syntax.sigquals = uu____54351;
             FStar_Syntax_Syntax.sigmeta = uu____54352;
             FStar_Syntax_Syntax.sigattrs = uu____54353;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____54371,uu____54372,uu____54373,uu____54374,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____54376;
             FStar_Syntax_Syntax.sigquals = uu____54377;
             FStar_Syntax_Syntax.sigmeta = uu____54378;
             FStar_Syntax_Syntax.sigattrs = uu____54379;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____54401 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54427 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54427 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____54437;
             FStar_Syntax_Syntax.sigquals = uu____54438;
             FStar_Syntax_Syntax.sigmeta = uu____54439;
             FStar_Syntax_Syntax.sigattrs = uu____54440;_},uu____54441)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____54451;
             FStar_Syntax_Syntax.sigquals = uu____54452;
             FStar_Syntax_Syntax.sigmeta = uu____54453;
             FStar_Syntax_Syntax.sigattrs = uu____54454;_},uu____54455)
          -> FStar_Pervasives_Native.Some ne
      | uu____54464 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____54483 = try_lookup_effect_name env lid  in
      match uu____54483 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____54488 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54503 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54503 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____54513,uu____54514,uu____54515,uu____54516);
             FStar_Syntax_Syntax.sigrng = uu____54517;
             FStar_Syntax_Syntax.sigquals = uu____54518;
             FStar_Syntax_Syntax.sigmeta = uu____54519;
             FStar_Syntax_Syntax.sigattrs = uu____54520;_},uu____54521)
          ->
          let rec aux new_name =
            let uu____54542 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____54542 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____54563) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____54574 =
                       let uu____54575 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____54575
                        in
                     FStar_Pervasives_Native.Some uu____54574
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____54577 =
                       let uu____54578 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____54578
                        in
                     FStar_Pervasives_Native.Some uu____54577
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____54579,uu____54580,uu____54581,cmp,uu____54583) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____54589 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____54590,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____54596 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___440_54635 =
        match uu___440_54635 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____54645,uu____54646,uu____54647);
             FStar_Syntax_Syntax.sigrng = uu____54648;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____54650;
             FStar_Syntax_Syntax.sigattrs = uu____54651;_},uu____54652)
            -> FStar_Pervasives_Native.Some quals
        | uu____54661 -> FStar_Pervasives_Native.None  in
      let uu____54669 =
        resolve_in_open_namespaces' env lid
          (fun uu____54677  -> FStar_Pervasives_Native.None)
          (fun uu____54681  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____54669 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____54691 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____54709 =
        FStar_List.tryFind
          (fun uu____54724  ->
             match uu____54724 with
             | (mlid,modul) ->
                 let uu____54732 = FStar_Ident.path_of_lid mlid  in
                 uu____54732 = path) env.modules
         in
      match uu____54709 with
      | FStar_Pervasives_Native.Some (uu____54735,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___441_54775 =
        match uu___441_54775 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____54783,lbs),uu____54785);
             FStar_Syntax_Syntax.sigrng = uu____54786;
             FStar_Syntax_Syntax.sigquals = uu____54787;
             FStar_Syntax_Syntax.sigmeta = uu____54788;
             FStar_Syntax_Syntax.sigattrs = uu____54789;_},uu____54790)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____54808 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____54808
        | uu____54809 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____54816  -> FStar_Pervasives_Native.None)
        (fun uu____54818  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___442_54851 =
        match uu___442_54851 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____54862);
             FStar_Syntax_Syntax.sigrng = uu____54863;
             FStar_Syntax_Syntax.sigquals = uu____54864;
             FStar_Syntax_Syntax.sigmeta = uu____54865;
             FStar_Syntax_Syntax.sigattrs = uu____54866;_},uu____54867)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____54893 -> FStar_Pervasives_Native.None)
        | uu____54900 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____54911  -> FStar_Pervasives_Native.None)
        (fun uu____54915  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____54975 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____54975 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____55000 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____55038) ->
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
      let uu____55096 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____55096 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55128 = try_lookup_lid env l  in
      match uu____55128 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____55134 =
            let uu____55135 = FStar_Syntax_Subst.compress e  in
            uu____55135.FStar_Syntax_Syntax.n  in
          (match uu____55134 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____55141 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____55153 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____55153 with
      | (uu____55163,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____55184 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____55188 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____55188 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____55193 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___1304_55224 = env  in
        {
          curmodule = (uu___1304_55224.curmodule);
          curmonad = (uu___1304_55224.curmonad);
          modules = (uu___1304_55224.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___1304_55224.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___1304_55224.sigaccum);
          sigmap = (uu___1304_55224.sigmap);
          iface = (uu___1304_55224.iface);
          admitted_iface = (uu___1304_55224.admitted_iface);
          expect_typ = (uu___1304_55224.expect_typ);
          docs = (uu___1304_55224.docs);
          remaining_iface_decls = (uu___1304_55224.remaining_iface_decls);
          syntax_only = (uu___1304_55224.syntax_only);
          ds_hooks = (uu___1304_55224.ds_hooks);
          dep_graph = (uu___1304_55224.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55240 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____55240 drop_attributes
  
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
               (uu____55310,uu____55311,uu____55312);
             FStar_Syntax_Syntax.sigrng = uu____55313;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____55315;
             FStar_Syntax_Syntax.sigattrs = uu____55316;_},uu____55317)
            ->
            let uu____55324 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___443_55330  ->
                      match uu___443_55330 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____55333 -> false))
               in
            if uu____55324
            then
              let uu____55338 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____55338
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____55341;
             FStar_Syntax_Syntax.sigrng = uu____55342;
             FStar_Syntax_Syntax.sigquals = uu____55343;
             FStar_Syntax_Syntax.sigmeta = uu____55344;
             FStar_Syntax_Syntax.sigattrs = uu____55345;_},uu____55346)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____55372 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____55372
        | uu____55373 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55380  -> FStar_Pervasives_Native.None)
        (fun uu____55382  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___444_55417 =
        match uu___444_55417 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____55427,uu____55428,uu____55429,uu____55430,datas,uu____55432);
             FStar_Syntax_Syntax.sigrng = uu____55433;
             FStar_Syntax_Syntax.sigquals = uu____55434;
             FStar_Syntax_Syntax.sigmeta = uu____55435;
             FStar_Syntax_Syntax.sigattrs = uu____55436;_},uu____55437)
            -> FStar_Pervasives_Native.Some datas
        | uu____55454 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55465  -> FStar_Pervasives_Native.None)
        (fun uu____55469  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____55548 =
    let uu____55549 =
      let uu____55554 =
        let uu____55557 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____55557  in
      let uu____55591 = FStar_ST.op_Bang record_cache  in uu____55554 ::
        uu____55591
       in
    FStar_ST.op_Colon_Equals record_cache uu____55549  in
  let pop1 uu____55657 =
    let uu____55658 =
      let uu____55663 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____55663  in
    FStar_ST.op_Colon_Equals record_cache uu____55658  in
  let snapshot1 uu____55734 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____55758 =
    let uu____55759 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____55759  in
  let insert r =
    let uu____55799 =
      let uu____55804 = let uu____55807 = peek1 ()  in r :: uu____55807  in
      let uu____55810 =
        let uu____55815 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____55815  in
      uu____55804 :: uu____55810  in
    FStar_ST.op_Colon_Equals record_cache uu____55799  in
  let filter1 uu____55883 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____55892 =
      let uu____55897 =
        let uu____55902 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____55902  in
      filtered :: uu____55897  in
    FStar_ST.op_Colon_Equals record_cache uu____55892  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____56828) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___445_56847  ->
                   match uu___445_56847 with
                   | FStar_Syntax_Syntax.RecordType uu____56849 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____56859 ->
                       true
                   | uu____56869 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___446_56894  ->
                      match uu___446_56894 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____56897,uu____56898,uu____56899,uu____56900,uu____56901);
                          FStar_Syntax_Syntax.sigrng = uu____56902;
                          FStar_Syntax_Syntax.sigquals = uu____56903;
                          FStar_Syntax_Syntax.sigmeta = uu____56904;
                          FStar_Syntax_Syntax.sigattrs = uu____56905;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____56916 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___447_56952  ->
                    match uu___447_56952 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____56956,uu____56957,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____56959;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____56961;
                        FStar_Syntax_Syntax.sigattrs = uu____56962;_} ->
                        let uu____56973 =
                          let uu____56974 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____56974  in
                        (match uu____56973 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____56980,t,uu____56982,uu____56983,uu____56984);
                             FStar_Syntax_Syntax.sigrng = uu____56985;
                             FStar_Syntax_Syntax.sigquals = uu____56986;
                             FStar_Syntax_Syntax.sigmeta = uu____56987;
                             FStar_Syntax_Syntax.sigattrs = uu____56988;_} ->
                             let uu____56999 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____56999 with
                              | (formals,uu____57015) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____57069  ->
                                            match uu____57069 with
                                            | (x,q) ->
                                                let uu____57082 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____57082
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____57137  ->
                                            match uu____57137 with
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
                                  ((let uu____57161 =
                                      let uu____57164 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____57164
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____57161);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____57223 =
                                            match uu____57223 with
                                            | (id1,uu____57229) ->
                                                let modul =
                                                  let uu____57232 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____57232.FStar_Ident.str
                                                   in
                                                let uu____57233 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____57233 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____57256 =
                                                         let uu____57257 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____57257
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____57256);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____57302
                                                               =
                                                               let uu____57303
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____57303.FStar_Ident.ident
                                                                in
                                                             uu____57302.FStar_Ident.idText
                                                              in
                                                           let uu____57305 =
                                                             let uu____57306
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____57306
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____57305))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____57358 -> ())
                    | uu____57359 -> ()))
        | uu____57360 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____57382 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____57382 with
        | (ns,id1) ->
            let uu____57399 = peek_record_cache ()  in
            FStar_Util.find_map uu____57399
              (fun record  ->
                 let uu____57405 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____57411  -> FStar_Pervasives_Native.None)
                   uu____57405)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____57413  -> Cont_ignore) (fun uu____57415  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____57421 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____57421)
        (fun k  -> fun uu____57427  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____57443 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____57443 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____57449 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____57469 = try_lookup_record_by_field_name env lid  in
        match uu____57469 with
        | FStar_Pervasives_Native.Some record' when
            let uu____57474 =
              let uu____57476 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____57476  in
            let uu____57477 =
              let uu____57479 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____57479  in
            uu____57474 = uu____57477 ->
            let uu____57481 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____57485  -> Cont_ok ())
               in
            (match uu____57481 with
             | Cont_ok uu____57487 -> true
             | uu____57489 -> false)
        | uu____57493 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____57515 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____57515 with
      | FStar_Pervasives_Native.Some r ->
          let uu____57526 =
            let uu____57532 =
              let uu____57533 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____57534 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____57533 uu____57534  in
            (uu____57532, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____57526
      | uu____57541 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____57559  ->
    let uu____57560 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____57560
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____57581  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___448_57594  ->
      match uu___448_57594 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___449_57632 =
            match uu___449_57632 with
            | Rec_binding uu____57634 -> true
            | uu____57636 -> false  in
          let this_env =
            let uu___1530_57639 = env  in
            let uu____57640 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1530_57639.curmodule);
              curmonad = (uu___1530_57639.curmonad);
              modules = (uu___1530_57639.modules);
              scope_mods = uu____57640;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1530_57639.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1530_57639.sigaccum);
              sigmap = (uu___1530_57639.sigmap);
              iface = (uu___1530_57639.iface);
              admitted_iface = (uu___1530_57639.admitted_iface);
              expect_typ = (uu___1530_57639.expect_typ);
              docs = (uu___1530_57639.docs);
              remaining_iface_decls = (uu___1530_57639.remaining_iface_decls);
              syntax_only = (uu___1530_57639.syntax_only);
              ds_hooks = (uu___1530_57639.ds_hooks);
              dep_graph = (uu___1530_57639.dep_graph)
            }  in
          let uu____57643 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____57643 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____57660 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1538_57685 = env  in
      {
        curmodule = (uu___1538_57685.curmodule);
        curmonad = (uu___1538_57685.curmonad);
        modules = (uu___1538_57685.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1538_57685.exported_ids);
        trans_exported_ids = (uu___1538_57685.trans_exported_ids);
        includes = (uu___1538_57685.includes);
        sigaccum = (uu___1538_57685.sigaccum);
        sigmap = (uu___1538_57685.sigmap);
        iface = (uu___1538_57685.iface);
        admitted_iface = (uu___1538_57685.admitted_iface);
        expect_typ = (uu___1538_57685.expect_typ);
        docs = (uu___1538_57685.docs);
        remaining_iface_decls = (uu___1538_57685.remaining_iface_decls);
        syntax_only = (uu___1538_57685.syntax_only);
        ds_hooks = (uu___1538_57685.ds_hooks);
        dep_graph = (uu___1538_57685.dep_graph)
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
        let uu____57719 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____57719
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____57726 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____57726)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____57770) ->
                let uu____57778 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____57778 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____57783 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____57783
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____57792 =
            let uu____57798 =
              let uu____57800 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____57800 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____57798)  in
          let uu____57804 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____57792 uu____57804  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____57813 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____57826 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____57837 -> (false, true)
            | uu____57850 -> (false, false)  in
          match uu____57813 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____57864 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____57870 =
                       let uu____57872 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____57872  in
                     if uu____57870
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____57864 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____57880 ->
                   (extract_record env globals s;
                    (let uu___1579_57884 = env  in
                     {
                       curmodule = (uu___1579_57884.curmodule);
                       curmonad = (uu___1579_57884.curmonad);
                       modules = (uu___1579_57884.modules);
                       scope_mods = (uu___1579_57884.scope_mods);
                       exported_ids = (uu___1579_57884.exported_ids);
                       trans_exported_ids =
                         (uu___1579_57884.trans_exported_ids);
                       includes = (uu___1579_57884.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1579_57884.sigmap);
                       iface = (uu___1579_57884.iface);
                       admitted_iface = (uu___1579_57884.admitted_iface);
                       expect_typ = (uu___1579_57884.expect_typ);
                       docs = (uu___1579_57884.docs);
                       remaining_iface_decls =
                         (uu___1579_57884.remaining_iface_decls);
                       syntax_only = (uu___1579_57884.syntax_only);
                       ds_hooks = (uu___1579_57884.ds_hooks);
                       dep_graph = (uu___1579_57884.dep_graph)
                     })))
           in
        let env2 =
          let uu___1582_57886 = env1  in
          let uu____57887 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1582_57886.curmodule);
            curmonad = (uu___1582_57886.curmonad);
            modules = (uu___1582_57886.modules);
            scope_mods = uu____57887;
            exported_ids = (uu___1582_57886.exported_ids);
            trans_exported_ids = (uu___1582_57886.trans_exported_ids);
            includes = (uu___1582_57886.includes);
            sigaccum = (uu___1582_57886.sigaccum);
            sigmap = (uu___1582_57886.sigmap);
            iface = (uu___1582_57886.iface);
            admitted_iface = (uu___1582_57886.admitted_iface);
            expect_typ = (uu___1582_57886.expect_typ);
            docs = (uu___1582_57886.docs);
            remaining_iface_decls = (uu___1582_57886.remaining_iface_decls);
            syntax_only = (uu___1582_57886.syntax_only);
            ds_hooks = (uu___1582_57886.ds_hooks);
            dep_graph = (uu___1582_57886.dep_graph)
          }  in
        let uu____57913 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____57939) ->
              let uu____57948 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____57948)
          | uu____57975 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____57913 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____58034  ->
                     match uu____58034 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____58056 =
                                    let uu____58059 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____58059
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____58056);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____58110 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____58110.FStar_Ident.str  in
                                      ((let uu____58112 =
                                          get_exported_id_set env3 modul  in
                                        match uu____58112 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____58134 =
                                              let uu____58135 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____58135
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____58134
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
                let uu___1607_58192 = env3  in
                let uu____58193 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1607_58192.curmodule);
                  curmonad = (uu___1607_58192.curmonad);
                  modules = (uu___1607_58192.modules);
                  scope_mods = uu____58193;
                  exported_ids = (uu___1607_58192.exported_ids);
                  trans_exported_ids = (uu___1607_58192.trans_exported_ids);
                  includes = (uu___1607_58192.includes);
                  sigaccum = (uu___1607_58192.sigaccum);
                  sigmap = (uu___1607_58192.sigmap);
                  iface = (uu___1607_58192.iface);
                  admitted_iface = (uu___1607_58192.admitted_iface);
                  expect_typ = (uu___1607_58192.expect_typ);
                  docs = (uu___1607_58192.docs);
                  remaining_iface_decls =
                    (uu___1607_58192.remaining_iface_decls);
                  syntax_only = (uu___1607_58192.syntax_only);
                  ds_hooks = (uu___1607_58192.ds_hooks);
                  dep_graph = (uu___1607_58192.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____58254 =
        let uu____58259 = resolve_module_name env ns false  in
        match uu____58259 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____58274 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____58292  ->
                      match uu____58292 with
                      | (m,uu____58299) ->
                          let uu____58300 =
                            let uu____58302 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____58302 "."  in
                          let uu____58305 =
                            let uu____58307 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____58307 "."  in
                          FStar_Util.starts_with uu____58300 uu____58305))
               in
            if uu____58274
            then (ns, Open_namespace)
            else
              (let uu____58317 =
                 let uu____58323 =
                   let uu____58325 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____58325
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____58323)  in
               let uu____58329 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____58317 uu____58329)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____58254 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____58351 = resolve_module_name env ns false  in
      match uu____58351 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____58361 = current_module env1  in
              uu____58361.FStar_Ident.str  in
            (let uu____58363 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____58363 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____58387 =
                   let uu____58390 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____58390
                    in
                 FStar_ST.op_Colon_Equals incl uu____58387);
            (match () with
             | () ->
                 let uu____58439 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____58439 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____58459 =
                          let uu____58556 = get_exported_id_set env1 curmod
                             in
                          let uu____58603 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____58556, uu____58603)  in
                        match uu____58459 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____59019 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____59019  in
                              let ex = cur_exports k  in
                              (let uu____59120 =
                                 let uu____59124 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____59124 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____59120);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____59216 =
                                     let uu____59220 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____59220 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____59216)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____59269 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____59371 =
                        let uu____59377 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____59377)
                         in
                      let uu____59381 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____59371 uu____59381))))
      | uu____59382 ->
          let uu____59385 =
            let uu____59391 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____59391)  in
          let uu____59395 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____59385 uu____59395
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____59412 = module_is_defined env l  in
        if uu____59412
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____59419 =
             let uu____59425 =
               let uu____59427 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____59427  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____59425)  in
           let uu____59431 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____59419 uu____59431)
  
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
            ((let uu____59454 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____59454 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____59458 = FStar_Ident.range_of_lid l  in
                  let uu____59459 =
                    let uu____59465 =
                      let uu____59467 = FStar_Ident.string_of_lid l  in
                      let uu____59469 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____59471 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____59467 uu____59469 uu____59471
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____59465)  in
                  FStar_Errors.log_issue uu____59458 uu____59459);
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
                      let uu____59517 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____59517 ->
                      let uu____59522 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____59522 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____59537;
                              FStar_Syntax_Syntax.sigrng = uu____59538;
                              FStar_Syntax_Syntax.sigquals = uu____59539;
                              FStar_Syntax_Syntax.sigmeta = uu____59540;
                              FStar_Syntax_Syntax.sigattrs = uu____59541;_},uu____59542)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____59560;
                              FStar_Syntax_Syntax.sigrng = uu____59561;
                              FStar_Syntax_Syntax.sigquals = uu____59562;
                              FStar_Syntax_Syntax.sigmeta = uu____59563;
                              FStar_Syntax_Syntax.sigattrs = uu____59564;_},uu____59565)
                           -> lids
                       | uu____59593 ->
                           ((let uu____59602 =
                               let uu____59604 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____59604  in
                             if uu____59602
                             then
                               let uu____59607 = FStar_Ident.range_of_lid l
                                  in
                               let uu____59608 =
                                 let uu____59614 =
                                   let uu____59616 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____59616
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____59614)
                                  in
                               FStar_Errors.log_issue uu____59607 uu____59608
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1710_59633 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1710_59633.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1710_59633.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1710_59633.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1710_59633.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____59635 -> lids) [])
         in
      let uu___1715_59636 = m  in
      let uu____59637 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____59647,uu____59648) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1724_59651 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1724_59651.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1724_59651.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1724_59651.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1724_59651.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____59652 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1715_59636.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____59637;
        FStar_Syntax_Syntax.exports =
          (uu___1715_59636.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1715_59636.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____59676) ->
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
                                (lid,uu____59697,uu____59698,uu____59699,uu____59700,uu____59701)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____59717,uu____59718)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____59735 =
                                        let uu____59742 =
                                          let uu____59743 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____59744 =
                                            let uu____59751 =
                                              let uu____59752 =
                                                let uu____59767 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____59767)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____59752
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____59751
                                             in
                                          uu____59744
                                            FStar_Pervasives_Native.None
                                            uu____59743
                                           in
                                        (lid, univ_names, uu____59742)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____59735
                                       in
                                    let se2 =
                                      let uu___1756_59781 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1756_59781.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1756_59781.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1756_59781.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____59791 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____59795,uu____59796) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____59805,lbs),uu____59807)
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
                             let uu____59825 =
                               let uu____59827 =
                                 let uu____59828 =
                                   let uu____59831 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____59831.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____59828.FStar_Syntax_Syntax.v  in
                               uu____59827.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____59825))
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
                               let uu____59848 =
                                 let uu____59851 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____59851.FStar_Syntax_Syntax.fv_name  in
                               uu____59848.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1779_59856 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1779_59856.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1779_59856.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1779_59856.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____59866 -> ()));
      (let curmod =
         let uu____59869 = current_module env  in uu____59869.FStar_Ident.str
          in
       (let uu____59871 =
          let uu____59968 = get_exported_id_set env curmod  in
          let uu____60015 = get_trans_exported_id_set env curmod  in
          (uu____59968, uu____60015)  in
        match uu____59871 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____60434 = cur_ex eikind  in
                FStar_ST.op_Bang uu____60434  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____60540 =
                let uu____60544 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____60544  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____60540  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____60593 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1797_60691 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1797_60691.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1797_60691.exported_ids);
                    trans_exported_ids = (uu___1797_60691.trans_exported_ids);
                    includes = (uu___1797_60691.includes);
                    sigaccum = [];
                    sigmap = (uu___1797_60691.sigmap);
                    iface = (uu___1797_60691.iface);
                    admitted_iface = (uu___1797_60691.admitted_iface);
                    expect_typ = (uu___1797_60691.expect_typ);
                    docs = (uu___1797_60691.docs);
                    remaining_iface_decls =
                      (uu___1797_60691.remaining_iface_decls);
                    syntax_only = (uu___1797_60691.syntax_only);
                    ds_hooks = (uu___1797_60691.ds_hooks);
                    dep_graph = (uu___1797_60691.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____60718  ->
         push_record_cache ();
         (let uu____60721 =
            let uu____60724 = FStar_ST.op_Bang stack  in env :: uu____60724
             in
          FStar_ST.op_Colon_Equals stack uu____60721);
         (let uu___1803_60773 = env  in
          let uu____60774 = FStar_Util.smap_copy env.exported_ids  in
          let uu____60779 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____60784 = FStar_Util.smap_copy env.includes  in
          let uu____60795 = FStar_Util.smap_copy env.sigmap  in
          let uu____60808 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1803_60773.curmodule);
            curmonad = (uu___1803_60773.curmonad);
            modules = (uu___1803_60773.modules);
            scope_mods = (uu___1803_60773.scope_mods);
            exported_ids = uu____60774;
            trans_exported_ids = uu____60779;
            includes = uu____60784;
            sigaccum = (uu___1803_60773.sigaccum);
            sigmap = uu____60795;
            iface = (uu___1803_60773.iface);
            admitted_iface = (uu___1803_60773.admitted_iface);
            expect_typ = (uu___1803_60773.expect_typ);
            docs = uu____60808;
            remaining_iface_decls = (uu___1803_60773.remaining_iface_decls);
            syntax_only = (uu___1803_60773.syntax_only);
            ds_hooks = (uu___1803_60773.ds_hooks);
            dep_graph = (uu___1803_60773.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____60816  ->
    FStar_Util.atomically
      (fun uu____60823  ->
         let uu____60824 = FStar_ST.op_Bang stack  in
         match uu____60824 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____60879 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____60926 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____60930 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____60972 = FStar_Util.smap_try_find sm' k  in
              match uu____60972 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1838_61003 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1838_61003.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1838_61003.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1838_61003.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1838_61003.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____61004 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____61012 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____61039 = finish env modul1  in (uu____61039, modul1)
  
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
      let uu____61108 =
        let uu____61112 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____61112  in
      FStar_Util.set_elements uu____61108  in
    let fields =
      let uu____61175 =
        let uu____61179 = e Exported_id_field  in
        FStar_ST.op_Bang uu____61179  in
      FStar_Util.set_elements uu____61175  in
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
          let uu____61271 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____61271  in
        let fields =
          let uu____61285 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____61285  in
        (fun uu___450_61293  ->
           match uu___450_61293 with
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
  'Auu____61397 .
    'Auu____61397 Prims.list FStar_Pervasives_Native.option ->
      'Auu____61397 Prims.list FStar_ST.ref
  =
  fun uu___451_61410  ->
    match uu___451_61410 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____61453 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____61453 as_exported_ids  in
      let uu____61459 = as_ids_opt env.exported_ids  in
      let uu____61462 = as_ids_opt env.trans_exported_ids  in
      let uu____61465 =
        let uu____61470 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____61470 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____61459;
        mii_trans_exported_ids = uu____61462;
        mii_includes = uu____61465
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
                let uu____61559 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____61559 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___452_61581 =
                  match uu___452_61581 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____61593  ->
                     match uu____61593 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____61619 =
                    let uu____61624 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____61624, Open_namespace)  in
                  [uu____61619]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____61655 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____61655);
              (match () with
               | () ->
                   ((let uu____61660 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____61660);
                    (match () with
                     | () ->
                         ((let uu____61665 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____61665);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1908_61675 = env1  in
                                 let uu____61676 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1908_61675.curmonad);
                                   modules = (uu___1908_61675.modules);
                                   scope_mods = uu____61676;
                                   exported_ids =
                                     (uu___1908_61675.exported_ids);
                                   trans_exported_ids =
                                     (uu___1908_61675.trans_exported_ids);
                                   includes = (uu___1908_61675.includes);
                                   sigaccum = (uu___1908_61675.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1908_61675.expect_typ);
                                   docs = (uu___1908_61675.docs);
                                   remaining_iface_decls =
                                     (uu___1908_61675.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1908_61675.syntax_only);
                                   ds_hooks = (uu___1908_61675.ds_hooks);
                                   dep_graph = (uu___1908_61675.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____61688 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____61714  ->
                      match uu____61714 with
                      | (l,uu____61721) -> FStar_Ident.lid_equals l mname))
               in
            match uu____61688 with
            | FStar_Pervasives_Native.None  ->
                let uu____61731 = prep env  in (uu____61731, false)
            | FStar_Pervasives_Native.Some (uu____61734,m) ->
                ((let uu____61741 =
                    (let uu____61745 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____61745) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____61741
                  then
                    let uu____61748 =
                      let uu____61754 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____61754)
                       in
                    let uu____61758 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____61748 uu____61758
                  else ());
                 (let uu____61761 =
                    let uu____61762 = push env  in prep uu____61762  in
                  (uu____61761, true)))
  
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
          let uu___1929_61780 = env  in
          {
            curmodule = (uu___1929_61780.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1929_61780.modules);
            scope_mods = (uu___1929_61780.scope_mods);
            exported_ids = (uu___1929_61780.exported_ids);
            trans_exported_ids = (uu___1929_61780.trans_exported_ids);
            includes = (uu___1929_61780.includes);
            sigaccum = (uu___1929_61780.sigaccum);
            sigmap = (uu___1929_61780.sigmap);
            iface = (uu___1929_61780.iface);
            admitted_iface = (uu___1929_61780.admitted_iface);
            expect_typ = (uu___1929_61780.expect_typ);
            docs = (uu___1929_61780.docs);
            remaining_iface_decls = (uu___1929_61780.remaining_iface_decls);
            syntax_only = (uu___1929_61780.syntax_only);
            ds_hooks = (uu___1929_61780.ds_hooks);
            dep_graph = (uu___1929_61780.dep_graph)
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
        let uu____61815 = lookup1 lid  in
        match uu____61815 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____61830  ->
                   match uu____61830 with
                   | (lid1,uu____61837) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____61840 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____61840  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____61852 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____61853 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____61852 uu____61853  in
                 let uu____61854 = resolve_module_name env modul true  in
                 match uu____61854 with
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
            let uu____61875 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____61875
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____61905 = lookup1 id1  in
      match uu____61905 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  