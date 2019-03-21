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
    match projectee with | Open_module  -> true | uu____49013 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____49024 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____49244 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____49263 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____49282 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____49301 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____49320 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____49339 -> false
  
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
    | uu____49360 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____49371 -> false
  
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
    ds_push_open_hook = (fun uu____50991  -> fun uu____50992  -> ());
    ds_push_include_hook = (fun uu____50995  -> fun uu____50996  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____51000  -> fun uu____51001  -> fun uu____51002  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____51039 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____51080 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___549_51114 = env  in
      {
        curmodule = (uu___549_51114.curmodule);
        curmonad = (uu___549_51114.curmonad);
        modules = (uu___549_51114.modules);
        scope_mods = (uu___549_51114.scope_mods);
        exported_ids = (uu___549_51114.exported_ids);
        trans_exported_ids = (uu___549_51114.trans_exported_ids);
        includes = (uu___549_51114.includes);
        sigaccum = (uu___549_51114.sigaccum);
        sigmap = (uu___549_51114.sigmap);
        iface = b;
        admitted_iface = (uu___549_51114.admitted_iface);
        expect_typ = (uu___549_51114.expect_typ);
        docs = (uu___549_51114.docs);
        remaining_iface_decls = (uu___549_51114.remaining_iface_decls);
        syntax_only = (uu___549_51114.syntax_only);
        ds_hooks = (uu___549_51114.ds_hooks);
        dep_graph = (uu___549_51114.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___554_51135 = e  in
      {
        curmodule = (uu___554_51135.curmodule);
        curmonad = (uu___554_51135.curmonad);
        modules = (uu___554_51135.modules);
        scope_mods = (uu___554_51135.scope_mods);
        exported_ids = (uu___554_51135.exported_ids);
        trans_exported_ids = (uu___554_51135.trans_exported_ids);
        includes = (uu___554_51135.includes);
        sigaccum = (uu___554_51135.sigaccum);
        sigmap = (uu___554_51135.sigmap);
        iface = (uu___554_51135.iface);
        admitted_iface = b;
        expect_typ = (uu___554_51135.expect_typ);
        docs = (uu___554_51135.docs);
        remaining_iface_decls = (uu___554_51135.remaining_iface_decls);
        syntax_only = (uu___554_51135.syntax_only);
        ds_hooks = (uu___554_51135.ds_hooks);
        dep_graph = (uu___554_51135.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___559_51156 = e  in
      {
        curmodule = (uu___559_51156.curmodule);
        curmonad = (uu___559_51156.curmonad);
        modules = (uu___559_51156.modules);
        scope_mods = (uu___559_51156.scope_mods);
        exported_ids = (uu___559_51156.exported_ids);
        trans_exported_ids = (uu___559_51156.trans_exported_ids);
        includes = (uu___559_51156.includes);
        sigaccum = (uu___559_51156.sigaccum);
        sigmap = (uu___559_51156.sigmap);
        iface = (uu___559_51156.iface);
        admitted_iface = (uu___559_51156.admitted_iface);
        expect_typ = b;
        docs = (uu___559_51156.docs);
        remaining_iface_decls = (uu___559_51156.remaining_iface_decls);
        syntax_only = (uu___559_51156.syntax_only);
        ds_hooks = (uu___559_51156.ds_hooks);
        dep_graph = (uu___559_51156.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____51183 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____51183 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____51196 =
            let uu____51200 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____51200  in
          FStar_All.pipe_right uu____51196 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___420_51288  ->
         match uu___420_51288 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____51293 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___578_51305 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___578_51305.curmonad);
        modules = (uu___578_51305.modules);
        scope_mods = (uu___578_51305.scope_mods);
        exported_ids = (uu___578_51305.exported_ids);
        trans_exported_ids = (uu___578_51305.trans_exported_ids);
        includes = (uu___578_51305.includes);
        sigaccum = (uu___578_51305.sigaccum);
        sigmap = (uu___578_51305.sigmap);
        iface = (uu___578_51305.iface);
        admitted_iface = (uu___578_51305.admitted_iface);
        expect_typ = (uu___578_51305.expect_typ);
        docs = (uu___578_51305.docs);
        remaining_iface_decls = (uu___578_51305.remaining_iface_decls);
        syntax_only = (uu___578_51305.syntax_only);
        ds_hooks = (uu___578_51305.ds_hooks);
        dep_graph = (uu___578_51305.dep_graph)
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
      let uu____51329 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____51363  ->
                match uu____51363 with
                | (m,uu____51372) -> FStar_Ident.lid_equals l m))
         in
      match uu____51329 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____51389,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____51423 =
          FStar_List.partition
            (fun uu____51453  ->
               match uu____51453 with
               | (m,uu____51462) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____51423 with
        | (uu____51467,rest) ->
            let uu___603_51501 = env  in
            {
              curmodule = (uu___603_51501.curmodule);
              curmonad = (uu___603_51501.curmonad);
              modules = (uu___603_51501.modules);
              scope_mods = (uu___603_51501.scope_mods);
              exported_ids = (uu___603_51501.exported_ids);
              trans_exported_ids = (uu___603_51501.trans_exported_ids);
              includes = (uu___603_51501.includes);
              sigaccum = (uu___603_51501.sigaccum);
              sigmap = (uu___603_51501.sigmap);
              iface = (uu___603_51501.iface);
              admitted_iface = (uu___603_51501.admitted_iface);
              expect_typ = (uu___603_51501.expect_typ);
              docs = (uu___603_51501.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___603_51501.syntax_only);
              ds_hooks = (uu___603_51501.ds_hooks);
              dep_graph = (uu___603_51501.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____51530 = current_module env  in qual uu____51530 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____51532 =
            let uu____51533 = current_module env  in qual uu____51533 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____51532
            id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___613_51554 = env  in
      {
        curmodule = (uu___613_51554.curmodule);
        curmonad = (uu___613_51554.curmonad);
        modules = (uu___613_51554.modules);
        scope_mods = (uu___613_51554.scope_mods);
        exported_ids = (uu___613_51554.exported_ids);
        trans_exported_ids = (uu___613_51554.trans_exported_ids);
        includes = (uu___613_51554.includes);
        sigaccum = (uu___613_51554.sigaccum);
        sigmap = (uu___613_51554.sigmap);
        iface = (uu___613_51554.iface);
        admitted_iface = (uu___613_51554.admitted_iface);
        expect_typ = (uu___613_51554.expect_typ);
        docs = (uu___613_51554.docs);
        remaining_iface_decls = (uu___613_51554.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___613_51554.ds_hooks);
        dep_graph = (uu___613_51554.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___618_51572 = env  in
      {
        curmodule = (uu___618_51572.curmodule);
        curmonad = (uu___618_51572.curmonad);
        modules = (uu___618_51572.modules);
        scope_mods = (uu___618_51572.scope_mods);
        exported_ids = (uu___618_51572.exported_ids);
        trans_exported_ids = (uu___618_51572.trans_exported_ids);
        includes = (uu___618_51572.includes);
        sigaccum = (uu___618_51572.sigaccum);
        sigmap = (uu___618_51572.sigmap);
        iface = (uu___618_51572.iface);
        admitted_iface = (uu___618_51572.admitted_iface);
        expect_typ = (uu___618_51572.expect_typ);
        docs = (uu___618_51572.docs);
        remaining_iface_decls = (uu___618_51572.remaining_iface_decls);
        syntax_only = (uu___618_51572.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___618_51572.dep_graph)
      }
  
let new_sigmap : 'Auu____51578 . unit -> 'Auu____51578 FStar_Util.smap =
  fun uu____51585  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____51593 = new_sigmap ()  in
    let uu____51598 = new_sigmap ()  in
    let uu____51603 = new_sigmap ()  in
    let uu____51614 = new_sigmap ()  in
    let uu____51627 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____51593;
      trans_exported_ids = uu____51598;
      includes = uu____51603;
      sigaccum = [];
      sigmap = uu____51614;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____51627;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___625_51661 = env  in
      {
        curmodule = (uu___625_51661.curmodule);
        curmonad = (uu___625_51661.curmonad);
        modules = (uu___625_51661.modules);
        scope_mods = (uu___625_51661.scope_mods);
        exported_ids = (uu___625_51661.exported_ids);
        trans_exported_ids = (uu___625_51661.trans_exported_ids);
        includes = (uu___625_51661.includes);
        sigaccum = (uu___625_51661.sigaccum);
        sigmap = (uu___625_51661.sigmap);
        iface = (uu___625_51661.iface);
        admitted_iface = (uu___625_51661.admitted_iface);
        expect_typ = (uu___625_51661.expect_typ);
        docs = (uu___625_51661.docs);
        remaining_iface_decls = (uu___625_51661.remaining_iface_decls);
        syntax_only = (uu___625_51661.syntax_only);
        ds_hooks = (uu___625_51661.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____51689  ->
         match uu____51689 with
         | (m,uu____51696) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___634_51709 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___634_51709.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___637_51710 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index =
          (uu___637_51710.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___637_51710.FStar_Syntax_Syntax.sort)
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
      (fun uu____51813  ->
         match uu____51813 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____51844 =
                 let uu____51845 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____51845 dd dq  in
               FStar_Pervasives_Native.Some uu____51844
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____51885 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____51922 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____51943 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___421_51973  ->
      match uu___421_51973 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____51992 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____51992 cont_t) -> 'Auu____51992 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____52029 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____52029
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____52045  ->
                   match uu____52045 with
                   | (f,uu____52053) ->
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
  fun uu___422_52127  ->
    match uu___422_52127 with
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
              let rec aux uu___423_52203 =
                match uu___423_52203 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____52216 = get_exported_id_set env mname  in
                      match uu____52216 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____52243 = mex eikind  in
                            FStar_ST.op_Bang uu____52243  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____52305 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____52305 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____52360 = qual modul id1  in
                        find_in_module uu____52360
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____52365 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___424_52374  ->
    match uu___424_52374 with
    | Exported_id_field  -> true
    | uu____52377 -> false
  
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
                  let check_local_binding_id uu___425_52501 =
                    match uu___425_52501 with
                    | (id',uu____52504) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___426_52512 =
                    match uu___426_52512 with
                    | (id',uu____52515,uu____52516) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____52521 = current_module env  in
                    FStar_Ident.ids_of_lid uu____52521  in
                  let proc uu___427_52529 =
                    match uu___427_52529 with
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
                        let uu____52538 = FStar_Ident.lid_of_ids curmod_ns
                           in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____52538 id1
                    | uu____52543 -> Cont_ignore  in
                  let rec aux uu___428_52553 =
                    match uu___428_52553 with
                    | a::q ->
                        let uu____52562 = proc a  in
                        option_of_cont (fun uu____52566  -> aux q)
                          uu____52562
                    | [] ->
                        let uu____52567 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____52571  -> FStar_Pervasives_Native.None)
                          uu____52567
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____52579 .
    FStar_Range.range ->
      ('Auu____52579 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____52593  -> match uu____52593 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____52611 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____52611)
          -> 'Auu____52611 -> 'Auu____52611
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____52652 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____52652 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____52696 = unmangleOpName id1  in
      match uu____52696 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____52702 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____52708 =
                 found_local_binding id1.FStar_Ident.idRange r  in
               Cont_ok uu____52708) (fun uu____52710  -> Cont_fail)
            (fun uu____52712  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____52719  -> fun uu____52720  -> Cont_fail)
                 Cont_ignore)
            (fun uu____52728  -> fun uu____52729  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____52803 ->
                let lid = qualify env id1  in
                let uu____52805 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____52805 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____52833 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____52833
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____52857 = current_module env  in qual uu____52857 id1
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
        let rec aux uu___429_52929 =
          match uu___429_52929 with
          | [] ->
              let uu____52934 = module_is_defined env lid  in
              if uu____52934
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____52946 =
                  let uu____52947 = FStar_Ident.path_of_lid ns  in
                  let uu____52951 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____52947 uu____52951  in
                let uu____52956 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____52946 uu____52956  in
              let uu____52957 = module_is_defined env new_lid  in
              if uu____52957
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____52966 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____52972::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____52992 =
          let uu____52994 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____52994  in
        if uu____52992
        then
          let uu____52996 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____52996
           then ()
           else
             (let uu____53001 =
                let uu____53007 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____53007)
                 in
              let uu____53011 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____53001 uu____53011))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____53025 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____53029 = resolve_module_name env modul_orig true  in
          (match uu____53029 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____53034 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___430_53057  ->
             match uu___430_53057 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____53061 -> false) env.scope_mods
  
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
                 let uu____53190 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____53190
                   (FStar_Util.map_option
                      (fun uu____53240  ->
                         match uu____53240 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____53310 = aux ns_rev_prefix ns_last_id  in
              (match uu____53310 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____53373 =
            let uu____53376 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____53376 true  in
          match uu____53373 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____53391 -> do_shorten env ids
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
                  | uu____53512::uu____53513 ->
                      let uu____53516 =
                        let uu____53519 =
                          let uu____53520 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____53521 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____53520 uu____53521
                           in
                        resolve_module_name env uu____53519 true  in
                      (match uu____53516 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____53526 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____53530  ->
                                FStar_Pervasives_Native.None) uu____53526)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___431_53554  ->
      match uu___431_53554 with
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
              let uu____53675 = k_global_def lid1 def  in
              cont_of_option k uu____53675  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____53711 = k_local_binding l  in
                 cont_of_option Cont_fail uu____53711)
              (fun r  ->
                 let uu____53717 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____53717)
              (fun uu____53721  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____53732,uu____53733,uu____53734,l,uu____53736,uu____53737) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___432_53750  ->
               match uu___432_53750 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____53753,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____53765 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____53771,uu____53772,uu____53773) -> FStar_Pervasives_Native.None
    | uu____53774 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____53790 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____53798 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____53798
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____53790 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____53821 =
         let uu____53822 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____53822  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____53821) &&
        (let uu____53826 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____53826 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____53843 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___433_53850  ->
                     match uu___433_53850 with
                     | FStar_Syntax_Syntax.Projector uu____53852 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____53858 -> true
                     | uu____53860 -> false)))
           in
        if uu____53843
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____53865 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___434_53871  ->
                 match uu___434_53871 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____53874 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___435_53880  ->
                    match uu___435_53880 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____53883 -> false)))
             &&
             (let uu____53886 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___436_53892  ->
                        match uu___436_53892 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____53895 -> false))
                 in
              Prims.op_Negation uu____53886))
         in
      if uu____53865 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___439_53947 =
            match uu___439_53947 with
            | (uu____53955,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____53959) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____53964 ->
                     let uu____53981 =
                       let uu____53982 =
                         let uu____53989 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____53989, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____53982  in
                     FStar_Pervasives_Native.Some uu____53981
                 | FStar_Syntax_Syntax.Sig_datacon uu____53992 ->
                     let uu____54008 =
                       let uu____54009 =
                         let uu____54016 =
                           let uu____54017 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____54017
                            in
                         (uu____54016, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____54009  in
                     FStar_Pervasives_Native.Some uu____54008
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____54022,lbs),uu____54024) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____54036 =
                       let uu____54037 =
                         let uu____54044 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____54044, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____54037  in
                     FStar_Pervasives_Native.Some uu____54036
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____54048,uu____54049) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____54053 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___437_54059  ->
                                  match uu___437_54059 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____54062 -> false)))
                        in
                     if uu____54053
                     then
                       let lid2 =
                         let uu____54068 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____54068  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____54070 =
                         FStar_Util.find_map quals
                           (fun uu___438_54075  ->
                              match uu___438_54075 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____54079 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____54070 with
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
                        | uu____54088 ->
                            let uu____54091 =
                              let uu____54092 =
                                let uu____54099 =
                                  let uu____54100 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____54100
                                   in
                                (uu____54099,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____54092  in
                            FStar_Pervasives_Native.Some uu____54091)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____54108 =
                       let uu____54109 =
                         let uu____54114 =
                           let uu____54115 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54115
                            in
                         (se, uu____54114)  in
                       Eff_name uu____54109  in
                     FStar_Pervasives_Native.Some uu____54108
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____54117 =
                       let uu____54118 =
                         let uu____54123 =
                           let uu____54124 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54124
                            in
                         (se, uu____54123)  in
                       Eff_name uu____54118  in
                     FStar_Pervasives_Native.Some uu____54117
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____54125 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____54144 =
                       let uu____54145 =
                         let uu____54152 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____54152, [])  in
                       Term_name uu____54145  in
                     FStar_Pervasives_Native.Some uu____54144
                 | uu____54156 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____54174 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____54174 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____54190 =
            match uu____54190 with
            | (id1,l,dd) ->
                let uu____54202 =
                  let uu____54203 =
                    let uu____54210 =
                      let uu____54211 =
                        let uu____54212 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____54212  in
                      FStar_Syntax_Syntax.fvar uu____54211 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____54210, [])  in
                  Term_name uu____54203  in
                FStar_Pervasives_Native.Some uu____54202
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____54220 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____54220 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____54228 -> FStar_Pervasives_Native.None)
            | uu____54231 -> FStar_Pervasives_Native.None  in
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
        let uu____54269 = try_lookup_name true exclude_interf env lid  in
        match uu____54269 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____54285 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54305 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54305 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____54320 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54346 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54346 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____54362;
             FStar_Syntax_Syntax.sigquals = uu____54363;
             FStar_Syntax_Syntax.sigmeta = uu____54364;
             FStar_Syntax_Syntax.sigattrs = uu____54365;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____54384;
             FStar_Syntax_Syntax.sigquals = uu____54385;
             FStar_Syntax_Syntax.sigmeta = uu____54386;
             FStar_Syntax_Syntax.sigattrs = uu____54387;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____54405,uu____54406,uu____54407,uu____54408,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____54410;
             FStar_Syntax_Syntax.sigquals = uu____54411;
             FStar_Syntax_Syntax.sigmeta = uu____54412;
             FStar_Syntax_Syntax.sigattrs = uu____54413;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____54435 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54461 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54461 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____54471;
             FStar_Syntax_Syntax.sigquals = uu____54472;
             FStar_Syntax_Syntax.sigmeta = uu____54473;
             FStar_Syntax_Syntax.sigattrs = uu____54474;_},uu____54475)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____54485;
             FStar_Syntax_Syntax.sigquals = uu____54486;
             FStar_Syntax_Syntax.sigmeta = uu____54487;
             FStar_Syntax_Syntax.sigattrs = uu____54488;_},uu____54489)
          -> FStar_Pervasives_Native.Some ne
      | uu____54498 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____54517 = try_lookup_effect_name env lid  in
      match uu____54517 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____54522 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54537 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54537 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____54547,uu____54548,uu____54549,uu____54550);
             FStar_Syntax_Syntax.sigrng = uu____54551;
             FStar_Syntax_Syntax.sigquals = uu____54552;
             FStar_Syntax_Syntax.sigmeta = uu____54553;
             FStar_Syntax_Syntax.sigattrs = uu____54554;_},uu____54555)
          ->
          let rec aux new_name =
            let uu____54576 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____54576 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____54597) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____54608 =
                       let uu____54609 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____54609
                        in
                     FStar_Pervasives_Native.Some uu____54608
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____54611 =
                       let uu____54612 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____54612
                        in
                     FStar_Pervasives_Native.Some uu____54611
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____54613,uu____54614,uu____54615,cmp,uu____54617) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____54623 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____54624,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____54630 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___440_54669 =
        match uu___440_54669 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____54679,uu____54680,uu____54681);
             FStar_Syntax_Syntax.sigrng = uu____54682;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____54684;
             FStar_Syntax_Syntax.sigattrs = uu____54685;_},uu____54686)
            -> FStar_Pervasives_Native.Some quals
        | uu____54695 -> FStar_Pervasives_Native.None  in
      let uu____54703 =
        resolve_in_open_namespaces' env lid
          (fun uu____54711  -> FStar_Pervasives_Native.None)
          (fun uu____54715  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____54703 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____54725 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____54743 =
        FStar_List.tryFind
          (fun uu____54758  ->
             match uu____54758 with
             | (mlid,modul) ->
                 let uu____54766 = FStar_Ident.path_of_lid mlid  in
                 uu____54766 = path) env.modules
         in
      match uu____54743 with
      | FStar_Pervasives_Native.Some (uu____54769,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___441_54809 =
        match uu___441_54809 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____54817,lbs),uu____54819);
             FStar_Syntax_Syntax.sigrng = uu____54820;
             FStar_Syntax_Syntax.sigquals = uu____54821;
             FStar_Syntax_Syntax.sigmeta = uu____54822;
             FStar_Syntax_Syntax.sigattrs = uu____54823;_},uu____54824)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____54842 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____54842
        | uu____54843 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____54850  -> FStar_Pervasives_Native.None)
        (fun uu____54852  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___442_54885 =
        match uu___442_54885 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____54896);
             FStar_Syntax_Syntax.sigrng = uu____54897;
             FStar_Syntax_Syntax.sigquals = uu____54898;
             FStar_Syntax_Syntax.sigmeta = uu____54899;
             FStar_Syntax_Syntax.sigattrs = uu____54900;_},uu____54901)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____54927 -> FStar_Pervasives_Native.None)
        | uu____54934 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____54945  -> FStar_Pervasives_Native.None)
        (fun uu____54949  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____55009 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____55009 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____55034 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____55072) ->
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
      let uu____55130 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____55130 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55162 = try_lookup_lid env l  in
      match uu____55162 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____55168 =
            let uu____55169 = FStar_Syntax_Subst.compress e  in
            uu____55169.FStar_Syntax_Syntax.n  in
          (match uu____55168 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____55175 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____55187 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____55187 with
      | (uu____55197,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____55218 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____55222 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____55222 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____55227 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___1304_55258 = env  in
        {
          curmodule = (uu___1304_55258.curmodule);
          curmonad = (uu___1304_55258.curmonad);
          modules = (uu___1304_55258.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___1304_55258.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___1304_55258.sigaccum);
          sigmap = (uu___1304_55258.sigmap);
          iface = (uu___1304_55258.iface);
          admitted_iface = (uu___1304_55258.admitted_iface);
          expect_typ = (uu___1304_55258.expect_typ);
          docs = (uu___1304_55258.docs);
          remaining_iface_decls = (uu___1304_55258.remaining_iface_decls);
          syntax_only = (uu___1304_55258.syntax_only);
          ds_hooks = (uu___1304_55258.ds_hooks);
          dep_graph = (uu___1304_55258.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55274 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____55274 drop_attributes
  
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
               (uu____55344,uu____55345,uu____55346);
             FStar_Syntax_Syntax.sigrng = uu____55347;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____55349;
             FStar_Syntax_Syntax.sigattrs = uu____55350;_},uu____55351)
            ->
            let uu____55358 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___443_55364  ->
                      match uu___443_55364 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____55367 -> false))
               in
            if uu____55358
            then
              let uu____55372 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____55372
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____55375;
             FStar_Syntax_Syntax.sigrng = uu____55376;
             FStar_Syntax_Syntax.sigquals = uu____55377;
             FStar_Syntax_Syntax.sigmeta = uu____55378;
             FStar_Syntax_Syntax.sigattrs = uu____55379;_},uu____55380)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____55406 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____55406
        | uu____55407 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55414  -> FStar_Pervasives_Native.None)
        (fun uu____55416  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___444_55451 =
        match uu___444_55451 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____55461,uu____55462,uu____55463,uu____55464,datas,uu____55466);
             FStar_Syntax_Syntax.sigrng = uu____55467;
             FStar_Syntax_Syntax.sigquals = uu____55468;
             FStar_Syntax_Syntax.sigmeta = uu____55469;
             FStar_Syntax_Syntax.sigattrs = uu____55470;_},uu____55471)
            -> FStar_Pervasives_Native.Some datas
        | uu____55488 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55499  -> FStar_Pervasives_Native.None)
        (fun uu____55503  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____55582 =
    let uu____55583 =
      let uu____55588 =
        let uu____55591 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____55591  in
      let uu____55625 = FStar_ST.op_Bang record_cache  in uu____55588 ::
        uu____55625
       in
    FStar_ST.op_Colon_Equals record_cache uu____55583  in
  let pop1 uu____55691 =
    let uu____55692 =
      let uu____55697 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____55697  in
    FStar_ST.op_Colon_Equals record_cache uu____55692  in
  let snapshot1 uu____55768 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____55792 =
    let uu____55793 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____55793  in
  let insert r =
    let uu____55833 =
      let uu____55838 = let uu____55841 = peek1 ()  in r :: uu____55841  in
      let uu____55844 =
        let uu____55849 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____55849  in
      uu____55838 :: uu____55844  in
    FStar_ST.op_Colon_Equals record_cache uu____55833  in
  let filter1 uu____55917 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____55926 =
      let uu____55931 =
        let uu____55936 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____55936  in
      filtered :: uu____55931  in
    FStar_ST.op_Colon_Equals record_cache uu____55926  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____56862) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___445_56881  ->
                   match uu___445_56881 with
                   | FStar_Syntax_Syntax.RecordType uu____56883 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____56893 ->
                       true
                   | uu____56903 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___446_56928  ->
                      match uu___446_56928 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____56931,uu____56932,uu____56933,uu____56934,uu____56935);
                          FStar_Syntax_Syntax.sigrng = uu____56936;
                          FStar_Syntax_Syntax.sigquals = uu____56937;
                          FStar_Syntax_Syntax.sigmeta = uu____56938;
                          FStar_Syntax_Syntax.sigattrs = uu____56939;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____56950 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___447_56986  ->
                    match uu___447_56986 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____56990,uu____56991,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____56993;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____56995;
                        FStar_Syntax_Syntax.sigattrs = uu____56996;_} ->
                        let uu____57007 =
                          let uu____57008 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____57008  in
                        (match uu____57007 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____57014,t,uu____57016,uu____57017,uu____57018);
                             FStar_Syntax_Syntax.sigrng = uu____57019;
                             FStar_Syntax_Syntax.sigquals = uu____57020;
                             FStar_Syntax_Syntax.sigmeta = uu____57021;
                             FStar_Syntax_Syntax.sigattrs = uu____57022;_} ->
                             let uu____57033 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____57033 with
                              | (formals,uu____57049) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____57103  ->
                                            match uu____57103 with
                                            | (x,q) ->
                                                let uu____57116 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____57116
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____57171  ->
                                            match uu____57171 with
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
                                  ((let uu____57195 =
                                      let uu____57198 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____57198
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____57195);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____57257 =
                                            match uu____57257 with
                                            | (id1,uu____57263) ->
                                                let modul =
                                                  let uu____57266 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____57266.FStar_Ident.str
                                                   in
                                                let uu____57267 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____57267 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____57290 =
                                                         let uu____57291 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____57291
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____57290);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____57336
                                                               =
                                                               let uu____57337
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____57337.FStar_Ident.ident
                                                                in
                                                             uu____57336.FStar_Ident.idText
                                                              in
                                                           let uu____57339 =
                                                             let uu____57340
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____57340
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____57339))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____57392 -> ())
                    | uu____57393 -> ()))
        | uu____57394 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____57416 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____57416 with
        | (ns,id1) ->
            let uu____57433 = peek_record_cache ()  in
            FStar_Util.find_map uu____57433
              (fun record  ->
                 let uu____57439 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____57445  -> FStar_Pervasives_Native.None)
                   uu____57439)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____57447  -> Cont_ignore) (fun uu____57449  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____57455 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____57455)
        (fun k  -> fun uu____57461  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____57477 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____57477 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____57483 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____57503 = try_lookup_record_by_field_name env lid  in
        match uu____57503 with
        | FStar_Pervasives_Native.Some record' when
            let uu____57508 =
              let uu____57510 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____57510  in
            let uu____57511 =
              let uu____57513 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____57513  in
            uu____57508 = uu____57511 ->
            let uu____57515 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____57519  -> Cont_ok ())
               in
            (match uu____57515 with
             | Cont_ok uu____57521 -> true
             | uu____57523 -> false)
        | uu____57527 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____57549 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____57549 with
      | FStar_Pervasives_Native.Some r ->
          let uu____57560 =
            let uu____57566 =
              let uu____57567 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____57568 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____57567 uu____57568  in
            (uu____57566, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____57560
      | uu____57575 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____57593  ->
    let uu____57594 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____57594
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____57615  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___448_57628  ->
      match uu___448_57628 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___449_57666 =
            match uu___449_57666 with
            | Rec_binding uu____57668 -> true
            | uu____57670 -> false  in
          let this_env =
            let uu___1530_57673 = env  in
            let uu____57674 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1530_57673.curmodule);
              curmonad = (uu___1530_57673.curmonad);
              modules = (uu___1530_57673.modules);
              scope_mods = uu____57674;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1530_57673.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1530_57673.sigaccum);
              sigmap = (uu___1530_57673.sigmap);
              iface = (uu___1530_57673.iface);
              admitted_iface = (uu___1530_57673.admitted_iface);
              expect_typ = (uu___1530_57673.expect_typ);
              docs = (uu___1530_57673.docs);
              remaining_iface_decls = (uu___1530_57673.remaining_iface_decls);
              syntax_only = (uu___1530_57673.syntax_only);
              ds_hooks = (uu___1530_57673.ds_hooks);
              dep_graph = (uu___1530_57673.dep_graph)
            }  in
          let uu____57677 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____57677 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____57694 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1538_57719 = env  in
      {
        curmodule = (uu___1538_57719.curmodule);
        curmonad = (uu___1538_57719.curmonad);
        modules = (uu___1538_57719.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1538_57719.exported_ids);
        trans_exported_ids = (uu___1538_57719.trans_exported_ids);
        includes = (uu___1538_57719.includes);
        sigaccum = (uu___1538_57719.sigaccum);
        sigmap = (uu___1538_57719.sigmap);
        iface = (uu___1538_57719.iface);
        admitted_iface = (uu___1538_57719.admitted_iface);
        expect_typ = (uu___1538_57719.expect_typ);
        docs = (uu___1538_57719.docs);
        remaining_iface_decls = (uu___1538_57719.remaining_iface_decls);
        syntax_only = (uu___1538_57719.syntax_only);
        ds_hooks = (uu___1538_57719.ds_hooks);
        dep_graph = (uu___1538_57719.dep_graph)
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
        let uu____57753 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____57753
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____57760 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____57760)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____57804) ->
                let uu____57812 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____57812 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____57817 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____57817
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____57826 =
            let uu____57832 =
              let uu____57834 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____57834 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____57832)  in
          let uu____57838 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____57826 uu____57838  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____57847 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____57860 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____57871 -> (false, true)
            | uu____57884 -> (false, false)  in
          match uu____57847 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____57898 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____57904 =
                       let uu____57906 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____57906  in
                     if uu____57904
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____57898 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____57914 ->
                   (extract_record env globals s;
                    (let uu___1579_57918 = env  in
                     {
                       curmodule = (uu___1579_57918.curmodule);
                       curmonad = (uu___1579_57918.curmonad);
                       modules = (uu___1579_57918.modules);
                       scope_mods = (uu___1579_57918.scope_mods);
                       exported_ids = (uu___1579_57918.exported_ids);
                       trans_exported_ids =
                         (uu___1579_57918.trans_exported_ids);
                       includes = (uu___1579_57918.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1579_57918.sigmap);
                       iface = (uu___1579_57918.iface);
                       admitted_iface = (uu___1579_57918.admitted_iface);
                       expect_typ = (uu___1579_57918.expect_typ);
                       docs = (uu___1579_57918.docs);
                       remaining_iface_decls =
                         (uu___1579_57918.remaining_iface_decls);
                       syntax_only = (uu___1579_57918.syntax_only);
                       ds_hooks = (uu___1579_57918.ds_hooks);
                       dep_graph = (uu___1579_57918.dep_graph)
                     })))
           in
        let env2 =
          let uu___1582_57920 = env1  in
          let uu____57921 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1582_57920.curmodule);
            curmonad = (uu___1582_57920.curmonad);
            modules = (uu___1582_57920.modules);
            scope_mods = uu____57921;
            exported_ids = (uu___1582_57920.exported_ids);
            trans_exported_ids = (uu___1582_57920.trans_exported_ids);
            includes = (uu___1582_57920.includes);
            sigaccum = (uu___1582_57920.sigaccum);
            sigmap = (uu___1582_57920.sigmap);
            iface = (uu___1582_57920.iface);
            admitted_iface = (uu___1582_57920.admitted_iface);
            expect_typ = (uu___1582_57920.expect_typ);
            docs = (uu___1582_57920.docs);
            remaining_iface_decls = (uu___1582_57920.remaining_iface_decls);
            syntax_only = (uu___1582_57920.syntax_only);
            ds_hooks = (uu___1582_57920.ds_hooks);
            dep_graph = (uu___1582_57920.dep_graph)
          }  in
        let uu____57947 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____57973) ->
              let uu____57982 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____57982)
          | uu____58009 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____57947 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____58068  ->
                     match uu____58068 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____58090 =
                                    let uu____58093 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____58093
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____58090);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____58144 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____58144.FStar_Ident.str  in
                                      ((let uu____58146 =
                                          get_exported_id_set env3 modul  in
                                        match uu____58146 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____58168 =
                                              let uu____58169 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____58169
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____58168
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
                let uu___1607_58226 = env3  in
                let uu____58227 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1607_58226.curmodule);
                  curmonad = (uu___1607_58226.curmonad);
                  modules = (uu___1607_58226.modules);
                  scope_mods = uu____58227;
                  exported_ids = (uu___1607_58226.exported_ids);
                  trans_exported_ids = (uu___1607_58226.trans_exported_ids);
                  includes = (uu___1607_58226.includes);
                  sigaccum = (uu___1607_58226.sigaccum);
                  sigmap = (uu___1607_58226.sigmap);
                  iface = (uu___1607_58226.iface);
                  admitted_iface = (uu___1607_58226.admitted_iface);
                  expect_typ = (uu___1607_58226.expect_typ);
                  docs = (uu___1607_58226.docs);
                  remaining_iface_decls =
                    (uu___1607_58226.remaining_iface_decls);
                  syntax_only = (uu___1607_58226.syntax_only);
                  ds_hooks = (uu___1607_58226.ds_hooks);
                  dep_graph = (uu___1607_58226.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____58288 =
        let uu____58293 = resolve_module_name env ns false  in
        match uu____58293 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____58308 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____58326  ->
                      match uu____58326 with
                      | (m,uu____58333) ->
                          let uu____58334 =
                            let uu____58336 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____58336 "."  in
                          let uu____58339 =
                            let uu____58341 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____58341 "."  in
                          FStar_Util.starts_with uu____58334 uu____58339))
               in
            if uu____58308
            then (ns, Open_namespace)
            else
              (let uu____58351 =
                 let uu____58357 =
                   let uu____58359 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____58359
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____58357)  in
               let uu____58363 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____58351 uu____58363)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____58288 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____58385 = resolve_module_name env ns false  in
      match uu____58385 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____58395 = current_module env1  in
              uu____58395.FStar_Ident.str  in
            (let uu____58397 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____58397 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____58421 =
                   let uu____58424 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____58424
                    in
                 FStar_ST.op_Colon_Equals incl uu____58421);
            (match () with
             | () ->
                 let uu____58473 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____58473 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____58493 =
                          let uu____58590 = get_exported_id_set env1 curmod
                             in
                          let uu____58637 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____58590, uu____58637)  in
                        match uu____58493 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____59053 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____59053  in
                              let ex = cur_exports k  in
                              (let uu____59154 =
                                 let uu____59158 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____59158 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____59154);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____59250 =
                                     let uu____59254 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____59254 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____59250)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____59303 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____59405 =
                        let uu____59411 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____59411)
                         in
                      let uu____59415 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____59405 uu____59415))))
      | uu____59416 ->
          let uu____59419 =
            let uu____59425 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____59425)  in
          let uu____59429 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____59419 uu____59429
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____59446 = module_is_defined env l  in
        if uu____59446
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____59453 =
             let uu____59459 =
               let uu____59461 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____59461  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____59459)  in
           let uu____59465 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____59453 uu____59465)
  
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
            ((let uu____59488 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____59488 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____59492 = FStar_Ident.range_of_lid l  in
                  let uu____59493 =
                    let uu____59499 =
                      let uu____59501 = FStar_Ident.string_of_lid l  in
                      let uu____59503 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____59505 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____59501 uu____59503 uu____59505
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____59499)  in
                  FStar_Errors.log_issue uu____59492 uu____59493);
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
                      let uu____59551 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____59551 ->
                      let uu____59556 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____59556 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____59571;
                              FStar_Syntax_Syntax.sigrng = uu____59572;
                              FStar_Syntax_Syntax.sigquals = uu____59573;
                              FStar_Syntax_Syntax.sigmeta = uu____59574;
                              FStar_Syntax_Syntax.sigattrs = uu____59575;_},uu____59576)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____59594;
                              FStar_Syntax_Syntax.sigrng = uu____59595;
                              FStar_Syntax_Syntax.sigquals = uu____59596;
                              FStar_Syntax_Syntax.sigmeta = uu____59597;
                              FStar_Syntax_Syntax.sigattrs = uu____59598;_},uu____59599)
                           -> lids
                       | uu____59627 ->
                           ((let uu____59636 =
                               let uu____59638 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____59638  in
                             if uu____59636
                             then
                               let uu____59641 = FStar_Ident.range_of_lid l
                                  in
                               let uu____59642 =
                                 let uu____59648 =
                                   let uu____59650 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____59650
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____59648)
                                  in
                               FStar_Errors.log_issue uu____59641 uu____59642
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1710_59667 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1710_59667.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1710_59667.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1710_59667.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1710_59667.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____59669 -> lids) [])
         in
      let uu___1715_59670 = m  in
      let uu____59671 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____59681,uu____59682) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1724_59685 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1724_59685.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1724_59685.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1724_59685.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1724_59685.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____59686 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1715_59670.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____59671;
        FStar_Syntax_Syntax.exports =
          (uu___1715_59670.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1715_59670.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____59710) ->
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
                                (lid,uu____59731,uu____59732,uu____59733,uu____59734,uu____59735)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____59751,uu____59752)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____59769 =
                                        let uu____59776 =
                                          let uu____59777 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____59778 =
                                            let uu____59785 =
                                              let uu____59786 =
                                                let uu____59801 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____59801)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____59786
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____59785
                                             in
                                          uu____59778
                                            FStar_Pervasives_Native.None
                                            uu____59777
                                           in
                                        (lid, univ_names, uu____59776)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____59769
                                       in
                                    let se2 =
                                      let uu___1756_59815 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1756_59815.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1756_59815.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1756_59815.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____59825 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____59829,uu____59830) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____59839,lbs),uu____59841)
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
                             let uu____59859 =
                               let uu____59861 =
                                 let uu____59862 =
                                   let uu____59865 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____59865.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____59862.FStar_Syntax_Syntax.v  in
                               uu____59861.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____59859))
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
                               let uu____59882 =
                                 let uu____59885 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____59885.FStar_Syntax_Syntax.fv_name  in
                               uu____59882.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1779_59890 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1779_59890.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1779_59890.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1779_59890.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____59900 -> ()));
      (let curmod =
         let uu____59903 = current_module env  in uu____59903.FStar_Ident.str
          in
       (let uu____59905 =
          let uu____60002 = get_exported_id_set env curmod  in
          let uu____60049 = get_trans_exported_id_set env curmod  in
          (uu____60002, uu____60049)  in
        match uu____59905 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____60468 = cur_ex eikind  in
                FStar_ST.op_Bang uu____60468  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____60574 =
                let uu____60578 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____60578  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____60574  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____60627 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1797_60725 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1797_60725.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1797_60725.exported_ids);
                    trans_exported_ids = (uu___1797_60725.trans_exported_ids);
                    includes = (uu___1797_60725.includes);
                    sigaccum = [];
                    sigmap = (uu___1797_60725.sigmap);
                    iface = (uu___1797_60725.iface);
                    admitted_iface = (uu___1797_60725.admitted_iface);
                    expect_typ = (uu___1797_60725.expect_typ);
                    docs = (uu___1797_60725.docs);
                    remaining_iface_decls =
                      (uu___1797_60725.remaining_iface_decls);
                    syntax_only = (uu___1797_60725.syntax_only);
                    ds_hooks = (uu___1797_60725.ds_hooks);
                    dep_graph = (uu___1797_60725.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____60752  ->
         push_record_cache ();
         (let uu____60755 =
            let uu____60758 = FStar_ST.op_Bang stack  in env :: uu____60758
             in
          FStar_ST.op_Colon_Equals stack uu____60755);
         (let uu___1803_60807 = env  in
          let uu____60808 = FStar_Util.smap_copy env.exported_ids  in
          let uu____60813 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____60818 = FStar_Util.smap_copy env.includes  in
          let uu____60829 = FStar_Util.smap_copy env.sigmap  in
          let uu____60842 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1803_60807.curmodule);
            curmonad = (uu___1803_60807.curmonad);
            modules = (uu___1803_60807.modules);
            scope_mods = (uu___1803_60807.scope_mods);
            exported_ids = uu____60808;
            trans_exported_ids = uu____60813;
            includes = uu____60818;
            sigaccum = (uu___1803_60807.sigaccum);
            sigmap = uu____60829;
            iface = (uu___1803_60807.iface);
            admitted_iface = (uu___1803_60807.admitted_iface);
            expect_typ = (uu___1803_60807.expect_typ);
            docs = uu____60842;
            remaining_iface_decls = (uu___1803_60807.remaining_iface_decls);
            syntax_only = (uu___1803_60807.syntax_only);
            ds_hooks = (uu___1803_60807.ds_hooks);
            dep_graph = (uu___1803_60807.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____60850  ->
    FStar_Util.atomically
      (fun uu____60857  ->
         let uu____60858 = FStar_ST.op_Bang stack  in
         match uu____60858 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____60913 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____60960 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____60964 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____61006 = FStar_Util.smap_try_find sm' k  in
              match uu____61006 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1838_61037 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1838_61037.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1838_61037.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1838_61037.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1838_61037.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____61038 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____61046 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____61073 = finish env modul1  in (uu____61073, modul1)
  
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
      let uu____61142 =
        let uu____61146 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____61146  in
      FStar_Util.set_elements uu____61142  in
    let fields =
      let uu____61209 =
        let uu____61213 = e Exported_id_field  in
        FStar_ST.op_Bang uu____61213  in
      FStar_Util.set_elements uu____61209  in
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
          let uu____61305 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____61305  in
        let fields =
          let uu____61319 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____61319  in
        (fun uu___450_61327  ->
           match uu___450_61327 with
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
  'Auu____61431 .
    'Auu____61431 Prims.list FStar_Pervasives_Native.option ->
      'Auu____61431 Prims.list FStar_ST.ref
  =
  fun uu___451_61444  ->
    match uu___451_61444 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____61487 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____61487 as_exported_ids  in
      let uu____61493 = as_ids_opt env.exported_ids  in
      let uu____61496 = as_ids_opt env.trans_exported_ids  in
      let uu____61499 =
        let uu____61504 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____61504 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____61493;
        mii_trans_exported_ids = uu____61496;
        mii_includes = uu____61499
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
                let uu____61593 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____61593 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___452_61615 =
                  match uu___452_61615 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____61627  ->
                     match uu____61627 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____61653 =
                    let uu____61658 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____61658, Open_namespace)  in
                  [uu____61653]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____61689 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____61689);
              (match () with
               | () ->
                   ((let uu____61694 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____61694);
                    (match () with
                     | () ->
                         ((let uu____61699 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____61699);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1908_61709 = env1  in
                                 let uu____61710 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1908_61709.curmonad);
                                   modules = (uu___1908_61709.modules);
                                   scope_mods = uu____61710;
                                   exported_ids =
                                     (uu___1908_61709.exported_ids);
                                   trans_exported_ids =
                                     (uu___1908_61709.trans_exported_ids);
                                   includes = (uu___1908_61709.includes);
                                   sigaccum = (uu___1908_61709.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1908_61709.expect_typ);
                                   docs = (uu___1908_61709.docs);
                                   remaining_iface_decls =
                                     (uu___1908_61709.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1908_61709.syntax_only);
                                   ds_hooks = (uu___1908_61709.ds_hooks);
                                   dep_graph = (uu___1908_61709.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____61722 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____61748  ->
                      match uu____61748 with
                      | (l,uu____61755) -> FStar_Ident.lid_equals l mname))
               in
            match uu____61722 with
            | FStar_Pervasives_Native.None  ->
                let uu____61765 = prep env  in (uu____61765, false)
            | FStar_Pervasives_Native.Some (uu____61768,m) ->
                ((let uu____61775 =
                    (let uu____61779 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____61779) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____61775
                  then
                    let uu____61782 =
                      let uu____61788 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____61788)
                       in
                    let uu____61792 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____61782 uu____61792
                  else ());
                 (let uu____61795 =
                    let uu____61796 = push env  in prep uu____61796  in
                  (uu____61795, true)))
  
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
          let uu___1929_61814 = env  in
          {
            curmodule = (uu___1929_61814.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1929_61814.modules);
            scope_mods = (uu___1929_61814.scope_mods);
            exported_ids = (uu___1929_61814.exported_ids);
            trans_exported_ids = (uu___1929_61814.trans_exported_ids);
            includes = (uu___1929_61814.includes);
            sigaccum = (uu___1929_61814.sigaccum);
            sigmap = (uu___1929_61814.sigmap);
            iface = (uu___1929_61814.iface);
            admitted_iface = (uu___1929_61814.admitted_iface);
            expect_typ = (uu___1929_61814.expect_typ);
            docs = (uu___1929_61814.docs);
            remaining_iface_decls = (uu___1929_61814.remaining_iface_decls);
            syntax_only = (uu___1929_61814.syntax_only);
            ds_hooks = (uu___1929_61814.ds_hooks);
            dep_graph = (uu___1929_61814.dep_graph)
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
        let uu____61849 = lookup1 lid  in
        match uu____61849 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____61864  ->
                   match uu____61864 with
                   | (lid1,uu____61871) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____61874 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____61874  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____61886 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____61887 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____61886 uu____61887  in
                 let uu____61888 = resolve_module_name env modul true  in
                 match uu____61888 with
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
            let uu____61909 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____61909
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____61939 = lookup1 id1  in
      match uu____61939 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  