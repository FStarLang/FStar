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
    match projectee with | Open_module  -> true | uu____49012 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____49023 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____49243 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____49262 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____49281 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____49300 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____49319 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____49338 -> false
  
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
    | uu____49359 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____49370 -> false
  
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
    ds_push_open_hook = (fun uu____50990  -> fun uu____50991  -> ());
    ds_push_include_hook = (fun uu____50994  -> fun uu____50995  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____50999  -> fun uu____51000  -> fun uu____51001  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____51038 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____51079 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___549_51113 = env  in
      {
        curmodule = (uu___549_51113.curmodule);
        curmonad = (uu___549_51113.curmonad);
        modules = (uu___549_51113.modules);
        scope_mods = (uu___549_51113.scope_mods);
        exported_ids = (uu___549_51113.exported_ids);
        trans_exported_ids = (uu___549_51113.trans_exported_ids);
        includes = (uu___549_51113.includes);
        sigaccum = (uu___549_51113.sigaccum);
        sigmap = (uu___549_51113.sigmap);
        iface = b;
        admitted_iface = (uu___549_51113.admitted_iface);
        expect_typ = (uu___549_51113.expect_typ);
        docs = (uu___549_51113.docs);
        remaining_iface_decls = (uu___549_51113.remaining_iface_decls);
        syntax_only = (uu___549_51113.syntax_only);
        ds_hooks = (uu___549_51113.ds_hooks);
        dep_graph = (uu___549_51113.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___554_51134 = e  in
      {
        curmodule = (uu___554_51134.curmodule);
        curmonad = (uu___554_51134.curmonad);
        modules = (uu___554_51134.modules);
        scope_mods = (uu___554_51134.scope_mods);
        exported_ids = (uu___554_51134.exported_ids);
        trans_exported_ids = (uu___554_51134.trans_exported_ids);
        includes = (uu___554_51134.includes);
        sigaccum = (uu___554_51134.sigaccum);
        sigmap = (uu___554_51134.sigmap);
        iface = (uu___554_51134.iface);
        admitted_iface = b;
        expect_typ = (uu___554_51134.expect_typ);
        docs = (uu___554_51134.docs);
        remaining_iface_decls = (uu___554_51134.remaining_iface_decls);
        syntax_only = (uu___554_51134.syntax_only);
        ds_hooks = (uu___554_51134.ds_hooks);
        dep_graph = (uu___554_51134.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___559_51155 = e  in
      {
        curmodule = (uu___559_51155.curmodule);
        curmonad = (uu___559_51155.curmonad);
        modules = (uu___559_51155.modules);
        scope_mods = (uu___559_51155.scope_mods);
        exported_ids = (uu___559_51155.exported_ids);
        trans_exported_ids = (uu___559_51155.trans_exported_ids);
        includes = (uu___559_51155.includes);
        sigaccum = (uu___559_51155.sigaccum);
        sigmap = (uu___559_51155.sigmap);
        iface = (uu___559_51155.iface);
        admitted_iface = (uu___559_51155.admitted_iface);
        expect_typ = b;
        docs = (uu___559_51155.docs);
        remaining_iface_decls = (uu___559_51155.remaining_iface_decls);
        syntax_only = (uu___559_51155.syntax_only);
        ds_hooks = (uu___559_51155.ds_hooks);
        dep_graph = (uu___559_51155.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____51182 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____51182 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____51195 =
            let uu____51199 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____51199  in
          FStar_All.pipe_right uu____51195 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___420_51287  ->
         match uu___420_51287 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____51292 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___578_51304 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___578_51304.curmonad);
        modules = (uu___578_51304.modules);
        scope_mods = (uu___578_51304.scope_mods);
        exported_ids = (uu___578_51304.exported_ids);
        trans_exported_ids = (uu___578_51304.trans_exported_ids);
        includes = (uu___578_51304.includes);
        sigaccum = (uu___578_51304.sigaccum);
        sigmap = (uu___578_51304.sigmap);
        iface = (uu___578_51304.iface);
        admitted_iface = (uu___578_51304.admitted_iface);
        expect_typ = (uu___578_51304.expect_typ);
        docs = (uu___578_51304.docs);
        remaining_iface_decls = (uu___578_51304.remaining_iface_decls);
        syntax_only = (uu___578_51304.syntax_only);
        ds_hooks = (uu___578_51304.ds_hooks);
        dep_graph = (uu___578_51304.dep_graph)
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
      let uu____51328 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____51362  ->
                match uu____51362 with
                | (m,uu____51371) -> FStar_Ident.lid_equals l m))
         in
      match uu____51328 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____51388,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____51422 =
          FStar_List.partition
            (fun uu____51452  ->
               match uu____51452 with
               | (m,uu____51461) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____51422 with
        | (uu____51466,rest) ->
            let uu___603_51500 = env  in
            {
              curmodule = (uu___603_51500.curmodule);
              curmonad = (uu___603_51500.curmonad);
              modules = (uu___603_51500.modules);
              scope_mods = (uu___603_51500.scope_mods);
              exported_ids = (uu___603_51500.exported_ids);
              trans_exported_ids = (uu___603_51500.trans_exported_ids);
              includes = (uu___603_51500.includes);
              sigaccum = (uu___603_51500.sigaccum);
              sigmap = (uu___603_51500.sigmap);
              iface = (uu___603_51500.iface);
              admitted_iface = (uu___603_51500.admitted_iface);
              expect_typ = (uu___603_51500.expect_typ);
              docs = (uu___603_51500.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___603_51500.syntax_only);
              ds_hooks = (uu___603_51500.ds_hooks);
              dep_graph = (uu___603_51500.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____51529 = current_module env  in qual uu____51529 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____51531 =
            let uu____51532 = current_module env  in qual uu____51532 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____51531
            id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___613_51553 = env  in
      {
        curmodule = (uu___613_51553.curmodule);
        curmonad = (uu___613_51553.curmonad);
        modules = (uu___613_51553.modules);
        scope_mods = (uu___613_51553.scope_mods);
        exported_ids = (uu___613_51553.exported_ids);
        trans_exported_ids = (uu___613_51553.trans_exported_ids);
        includes = (uu___613_51553.includes);
        sigaccum = (uu___613_51553.sigaccum);
        sigmap = (uu___613_51553.sigmap);
        iface = (uu___613_51553.iface);
        admitted_iface = (uu___613_51553.admitted_iface);
        expect_typ = (uu___613_51553.expect_typ);
        docs = (uu___613_51553.docs);
        remaining_iface_decls = (uu___613_51553.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___613_51553.ds_hooks);
        dep_graph = (uu___613_51553.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___618_51571 = env  in
      {
        curmodule = (uu___618_51571.curmodule);
        curmonad = (uu___618_51571.curmonad);
        modules = (uu___618_51571.modules);
        scope_mods = (uu___618_51571.scope_mods);
        exported_ids = (uu___618_51571.exported_ids);
        trans_exported_ids = (uu___618_51571.trans_exported_ids);
        includes = (uu___618_51571.includes);
        sigaccum = (uu___618_51571.sigaccum);
        sigmap = (uu___618_51571.sigmap);
        iface = (uu___618_51571.iface);
        admitted_iface = (uu___618_51571.admitted_iface);
        expect_typ = (uu___618_51571.expect_typ);
        docs = (uu___618_51571.docs);
        remaining_iface_decls = (uu___618_51571.remaining_iface_decls);
        syntax_only = (uu___618_51571.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___618_51571.dep_graph)
      }
  
let new_sigmap : 'Auu____51577 . unit -> 'Auu____51577 FStar_Util.smap =
  fun uu____51584  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____51592 = new_sigmap ()  in
    let uu____51597 = new_sigmap ()  in
    let uu____51602 = new_sigmap ()  in
    let uu____51613 = new_sigmap ()  in
    let uu____51626 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____51592;
      trans_exported_ids = uu____51597;
      includes = uu____51602;
      sigaccum = [];
      sigmap = uu____51613;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____51626;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___625_51660 = env  in
      {
        curmodule = (uu___625_51660.curmodule);
        curmonad = (uu___625_51660.curmonad);
        modules = (uu___625_51660.modules);
        scope_mods = (uu___625_51660.scope_mods);
        exported_ids = (uu___625_51660.exported_ids);
        trans_exported_ids = (uu___625_51660.trans_exported_ids);
        includes = (uu___625_51660.includes);
        sigaccum = (uu___625_51660.sigaccum);
        sigmap = (uu___625_51660.sigmap);
        iface = (uu___625_51660.iface);
        admitted_iface = (uu___625_51660.admitted_iface);
        expect_typ = (uu___625_51660.expect_typ);
        docs = (uu___625_51660.docs);
        remaining_iface_decls = (uu___625_51660.remaining_iface_decls);
        syntax_only = (uu___625_51660.syntax_only);
        ds_hooks = (uu___625_51660.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____51688  ->
         match uu____51688 with
         | (m,uu____51695) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___634_51708 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___634_51708.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___637_51709 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index =
          (uu___637_51709.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___637_51709.FStar_Syntax_Syntax.sort)
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
      (fun uu____51812  ->
         match uu____51812 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____51843 =
                 let uu____51844 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____51844 dd dq  in
               FStar_Pervasives_Native.Some uu____51843
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____51884 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____51921 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____51942 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___421_51972  ->
      match uu___421_51972 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____51991 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____51991 cont_t) -> 'Auu____51991 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____52028 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____52028
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____52044  ->
                   match uu____52044 with
                   | (f,uu____52052) ->
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
  fun uu___422_52126  ->
    match uu___422_52126 with
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
              let rec aux uu___423_52202 =
                match uu___423_52202 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____52215 = get_exported_id_set env mname  in
                      match uu____52215 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____52242 = mex eikind  in
                            FStar_ST.op_Bang uu____52242  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____52304 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____52304 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____52359 = qual modul id1  in
                        find_in_module uu____52359
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____52364 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___424_52373  ->
    match uu___424_52373 with
    | Exported_id_field  -> true
    | uu____52376 -> false
  
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
                  let check_local_binding_id uu___425_52500 =
                    match uu___425_52500 with
                    | (id',uu____52503) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___426_52511 =
                    match uu___426_52511 with
                    | (id',uu____52514,uu____52515) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____52520 = current_module env  in
                    FStar_Ident.ids_of_lid uu____52520  in
                  let proc uu___427_52528 =
                    match uu___427_52528 with
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
                        let uu____52537 = FStar_Ident.lid_of_ids curmod_ns
                           in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____52537 id1
                    | uu____52542 -> Cont_ignore  in
                  let rec aux uu___428_52552 =
                    match uu___428_52552 with
                    | a::q ->
                        let uu____52561 = proc a  in
                        option_of_cont (fun uu____52565  -> aux q)
                          uu____52561
                    | [] ->
                        let uu____52566 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____52570  -> FStar_Pervasives_Native.None)
                          uu____52566
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____52578 .
    FStar_Range.range ->
      ('Auu____52578 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____52592  -> match uu____52592 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____52610 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____52610)
          -> 'Auu____52610 -> 'Auu____52610
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____52651 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____52651 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____52695 = unmangleOpName id1  in
      match uu____52695 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____52701 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____52707 =
                 found_local_binding id1.FStar_Ident.idRange r  in
               Cont_ok uu____52707) (fun uu____52709  -> Cont_fail)
            (fun uu____52711  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____52718  -> fun uu____52719  -> Cont_fail)
                 Cont_ignore)
            (fun uu____52727  -> fun uu____52728  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____52802 ->
                let lid = qualify env id1  in
                let uu____52804 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____52804 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____52832 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____52832
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____52856 = current_module env  in qual uu____52856 id1
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
        let rec aux uu___429_52928 =
          match uu___429_52928 with
          | [] ->
              let uu____52933 = module_is_defined env lid  in
              if uu____52933
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____52945 =
                  let uu____52946 = FStar_Ident.path_of_lid ns  in
                  let uu____52950 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____52946 uu____52950  in
                let uu____52955 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____52945 uu____52955  in
              let uu____52956 = module_is_defined env new_lid  in
              if uu____52956
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____52965 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____52971::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____52991 =
          let uu____52993 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____52993  in
        if uu____52991
        then
          let uu____52995 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____52995
           then ()
           else
             (let uu____53000 =
                let uu____53006 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____53006)
                 in
              let uu____53010 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____53000 uu____53010))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____53024 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____53028 = resolve_module_name env modul_orig true  in
          (match uu____53028 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____53033 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___430_53056  ->
             match uu___430_53056 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____53060 -> false) env.scope_mods
  
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
                 let uu____53189 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____53189
                   (FStar_Util.map_option
                      (fun uu____53239  ->
                         match uu____53239 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____53309 = aux ns_rev_prefix ns_last_id  in
              (match uu____53309 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____53372 =
            let uu____53375 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____53375 true  in
          match uu____53372 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____53390 -> do_shorten env ids
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
                  | uu____53511::uu____53512 ->
                      let uu____53515 =
                        let uu____53518 =
                          let uu____53519 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____53520 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____53519 uu____53520
                           in
                        resolve_module_name env uu____53518 true  in
                      (match uu____53515 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____53525 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____53529  ->
                                FStar_Pervasives_Native.None) uu____53525)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___431_53553  ->
      match uu___431_53553 with
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
              let uu____53674 = k_global_def lid1 def  in
              cont_of_option k uu____53674  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____53710 = k_local_binding l  in
                 cont_of_option Cont_fail uu____53710)
              (fun r  ->
                 let uu____53716 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____53716)
              (fun uu____53720  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____53731,uu____53732,uu____53733,l,uu____53735,uu____53736) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___432_53749  ->
               match uu___432_53749 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____53752,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____53764 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____53770,uu____53771,uu____53772) -> FStar_Pervasives_Native.None
    | uu____53773 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____53789 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____53797 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____53797
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____53789 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____53820 =
         let uu____53821 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____53821  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____53820) &&
        (let uu____53825 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____53825 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____53842 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___433_53849  ->
                     match uu___433_53849 with
                     | FStar_Syntax_Syntax.Projector uu____53851 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____53857 -> true
                     | uu____53859 -> false)))
           in
        if uu____53842
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____53864 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___434_53870  ->
                 match uu___434_53870 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____53873 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___435_53879  ->
                    match uu___435_53879 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____53882 -> false)))
             &&
             (let uu____53885 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___436_53891  ->
                        match uu___436_53891 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____53894 -> false))
                 in
              Prims.op_Negation uu____53885))
         in
      if uu____53864 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___439_53946 =
            match uu___439_53946 with
            | (uu____53954,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____53958) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____53963 ->
                     let uu____53980 =
                       let uu____53981 =
                         let uu____53988 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____53988, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____53981  in
                     FStar_Pervasives_Native.Some uu____53980
                 | FStar_Syntax_Syntax.Sig_datacon uu____53991 ->
                     let uu____54007 =
                       let uu____54008 =
                         let uu____54015 =
                           let uu____54016 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____54016
                            in
                         (uu____54015, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____54008  in
                     FStar_Pervasives_Native.Some uu____54007
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____54021,lbs),uu____54023) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____54035 =
                       let uu____54036 =
                         let uu____54043 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____54043, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____54036  in
                     FStar_Pervasives_Native.Some uu____54035
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____54047,uu____54048) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____54052 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___437_54058  ->
                                  match uu___437_54058 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____54061 -> false)))
                        in
                     if uu____54052
                     then
                       let lid2 =
                         let uu____54067 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____54067  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____54069 =
                         FStar_Util.find_map quals
                           (fun uu___438_54074  ->
                              match uu___438_54074 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____54078 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____54069 with
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
                        | uu____54087 ->
                            let uu____54090 =
                              let uu____54091 =
                                let uu____54098 =
                                  let uu____54099 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____54099
                                   in
                                (uu____54098,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____54091  in
                            FStar_Pervasives_Native.Some uu____54090)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____54107 =
                       let uu____54108 =
                         let uu____54113 =
                           let uu____54114 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54114
                            in
                         (se, uu____54113)  in
                       Eff_name uu____54108  in
                     FStar_Pervasives_Native.Some uu____54107
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____54116 =
                       let uu____54117 =
                         let uu____54122 =
                           let uu____54123 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____54123
                            in
                         (se, uu____54122)  in
                       Eff_name uu____54117  in
                     FStar_Pervasives_Native.Some uu____54116
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____54124 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____54143 =
                       let uu____54144 =
                         let uu____54151 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____54151, [])  in
                       Term_name uu____54144  in
                     FStar_Pervasives_Native.Some uu____54143
                 | uu____54155 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____54173 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____54173 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____54189 =
            match uu____54189 with
            | (id1,l,dd) ->
                let uu____54201 =
                  let uu____54202 =
                    let uu____54209 =
                      let uu____54210 =
                        let uu____54211 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____54211  in
                      FStar_Syntax_Syntax.fvar uu____54210 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____54209, [])  in
                  Term_name uu____54202  in
                FStar_Pervasives_Native.Some uu____54201
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____54219 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____54219 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____54227 -> FStar_Pervasives_Native.None)
            | uu____54230 -> FStar_Pervasives_Native.None  in
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
        let uu____54268 = try_lookup_name true exclude_interf env lid  in
        match uu____54268 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____54284 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54304 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54304 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____54319 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54345 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54345 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____54361;
             FStar_Syntax_Syntax.sigquals = uu____54362;
             FStar_Syntax_Syntax.sigmeta = uu____54363;
             FStar_Syntax_Syntax.sigattrs = uu____54364;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____54383;
             FStar_Syntax_Syntax.sigquals = uu____54384;
             FStar_Syntax_Syntax.sigmeta = uu____54385;
             FStar_Syntax_Syntax.sigattrs = uu____54386;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____54404,uu____54405,uu____54406,uu____54407,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____54409;
             FStar_Syntax_Syntax.sigquals = uu____54410;
             FStar_Syntax_Syntax.sigmeta = uu____54411;
             FStar_Syntax_Syntax.sigattrs = uu____54412;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____54434 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54460 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54460 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____54470;
             FStar_Syntax_Syntax.sigquals = uu____54471;
             FStar_Syntax_Syntax.sigmeta = uu____54472;
             FStar_Syntax_Syntax.sigattrs = uu____54473;_},uu____54474)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____54484;
             FStar_Syntax_Syntax.sigquals = uu____54485;
             FStar_Syntax_Syntax.sigmeta = uu____54486;
             FStar_Syntax_Syntax.sigattrs = uu____54487;_},uu____54488)
          -> FStar_Pervasives_Native.Some ne
      | uu____54497 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____54516 = try_lookup_effect_name env lid  in
      match uu____54516 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____54521 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____54536 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____54536 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____54546,uu____54547,uu____54548,uu____54549);
             FStar_Syntax_Syntax.sigrng = uu____54550;
             FStar_Syntax_Syntax.sigquals = uu____54551;
             FStar_Syntax_Syntax.sigmeta = uu____54552;
             FStar_Syntax_Syntax.sigattrs = uu____54553;_},uu____54554)
          ->
          let rec aux new_name =
            let uu____54575 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____54575 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____54596) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____54607 =
                       let uu____54608 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____54608
                        in
                     FStar_Pervasives_Native.Some uu____54607
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____54610 =
                       let uu____54611 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____54611
                        in
                     FStar_Pervasives_Native.Some uu____54610
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____54612,uu____54613,uu____54614,cmp,uu____54616) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____54622 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____54623,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____54629 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___440_54668 =
        match uu___440_54668 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____54678,uu____54679,uu____54680);
             FStar_Syntax_Syntax.sigrng = uu____54681;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____54683;
             FStar_Syntax_Syntax.sigattrs = uu____54684;_},uu____54685)
            -> FStar_Pervasives_Native.Some quals
        | uu____54694 -> FStar_Pervasives_Native.None  in
      let uu____54702 =
        resolve_in_open_namespaces' env lid
          (fun uu____54710  -> FStar_Pervasives_Native.None)
          (fun uu____54714  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____54702 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____54724 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____54742 =
        FStar_List.tryFind
          (fun uu____54757  ->
             match uu____54757 with
             | (mlid,modul) ->
                 let uu____54765 = FStar_Ident.path_of_lid mlid  in
                 uu____54765 = path) env.modules
         in
      match uu____54742 with
      | FStar_Pervasives_Native.Some (uu____54768,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___441_54808 =
        match uu___441_54808 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____54816,lbs),uu____54818);
             FStar_Syntax_Syntax.sigrng = uu____54819;
             FStar_Syntax_Syntax.sigquals = uu____54820;
             FStar_Syntax_Syntax.sigmeta = uu____54821;
             FStar_Syntax_Syntax.sigattrs = uu____54822;_},uu____54823)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____54841 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____54841
        | uu____54842 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____54849  -> FStar_Pervasives_Native.None)
        (fun uu____54851  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___442_54884 =
        match uu___442_54884 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____54895);
             FStar_Syntax_Syntax.sigrng = uu____54896;
             FStar_Syntax_Syntax.sigquals = uu____54897;
             FStar_Syntax_Syntax.sigmeta = uu____54898;
             FStar_Syntax_Syntax.sigattrs = uu____54899;_},uu____54900)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____54926 -> FStar_Pervasives_Native.None)
        | uu____54933 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____54944  -> FStar_Pervasives_Native.None)
        (fun uu____54948  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____55008 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____55008 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____55033 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____55071) ->
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
      let uu____55129 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____55129 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55161 = try_lookup_lid env l  in
      match uu____55161 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____55167 =
            let uu____55168 = FStar_Syntax_Subst.compress e  in
            uu____55168.FStar_Syntax_Syntax.n  in
          (match uu____55167 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____55174 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____55186 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____55186 with
      | (uu____55196,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____55217 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____55221 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____55221 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____55226 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___1304_55257 = env  in
        {
          curmodule = (uu___1304_55257.curmodule);
          curmonad = (uu___1304_55257.curmonad);
          modules = (uu___1304_55257.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___1304_55257.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___1304_55257.sigaccum);
          sigmap = (uu___1304_55257.sigmap);
          iface = (uu___1304_55257.iface);
          admitted_iface = (uu___1304_55257.admitted_iface);
          expect_typ = (uu___1304_55257.expect_typ);
          docs = (uu___1304_55257.docs);
          remaining_iface_decls = (uu___1304_55257.remaining_iface_decls);
          syntax_only = (uu___1304_55257.syntax_only);
          ds_hooks = (uu___1304_55257.ds_hooks);
          dep_graph = (uu___1304_55257.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____55273 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____55273 drop_attributes
  
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
               (uu____55343,uu____55344,uu____55345);
             FStar_Syntax_Syntax.sigrng = uu____55346;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____55348;
             FStar_Syntax_Syntax.sigattrs = uu____55349;_},uu____55350)
            ->
            let uu____55357 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___443_55363  ->
                      match uu___443_55363 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____55366 -> false))
               in
            if uu____55357
            then
              let uu____55371 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____55371
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____55374;
             FStar_Syntax_Syntax.sigrng = uu____55375;
             FStar_Syntax_Syntax.sigquals = uu____55376;
             FStar_Syntax_Syntax.sigmeta = uu____55377;
             FStar_Syntax_Syntax.sigattrs = uu____55378;_},uu____55379)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____55405 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____55405
        | uu____55406 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55413  -> FStar_Pervasives_Native.None)
        (fun uu____55415  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___444_55450 =
        match uu___444_55450 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____55460,uu____55461,uu____55462,uu____55463,datas,uu____55465);
             FStar_Syntax_Syntax.sigrng = uu____55466;
             FStar_Syntax_Syntax.sigquals = uu____55467;
             FStar_Syntax_Syntax.sigmeta = uu____55468;
             FStar_Syntax_Syntax.sigattrs = uu____55469;_},uu____55470)
            -> FStar_Pervasives_Native.Some datas
        | uu____55487 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____55498  -> FStar_Pervasives_Native.None)
        (fun uu____55502  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____55581 =
    let uu____55582 =
      let uu____55587 =
        let uu____55590 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____55590  in
      let uu____55624 = FStar_ST.op_Bang record_cache  in uu____55587 ::
        uu____55624
       in
    FStar_ST.op_Colon_Equals record_cache uu____55582  in
  let pop1 uu____55690 =
    let uu____55691 =
      let uu____55696 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____55696  in
    FStar_ST.op_Colon_Equals record_cache uu____55691  in
  let snapshot1 uu____55767 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____55791 =
    let uu____55792 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____55792  in
  let insert r =
    let uu____55832 =
      let uu____55837 = let uu____55840 = peek1 ()  in r :: uu____55840  in
      let uu____55843 =
        let uu____55848 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____55848  in
      uu____55837 :: uu____55843  in
    FStar_ST.op_Colon_Equals record_cache uu____55832  in
  let filter1 uu____55916 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____55925 =
      let uu____55930 =
        let uu____55935 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____55935  in
      filtered :: uu____55930  in
    FStar_ST.op_Colon_Equals record_cache uu____55925  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____56861) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___445_56880  ->
                   match uu___445_56880 with
                   | FStar_Syntax_Syntax.RecordType uu____56882 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____56892 ->
                       true
                   | uu____56902 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___446_56927  ->
                      match uu___446_56927 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____56930,uu____56931,uu____56932,uu____56933,uu____56934);
                          FStar_Syntax_Syntax.sigrng = uu____56935;
                          FStar_Syntax_Syntax.sigquals = uu____56936;
                          FStar_Syntax_Syntax.sigmeta = uu____56937;
                          FStar_Syntax_Syntax.sigattrs = uu____56938;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____56949 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___447_56985  ->
                    match uu___447_56985 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____56989,uu____56990,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____56992;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____56994;
                        FStar_Syntax_Syntax.sigattrs = uu____56995;_} ->
                        let uu____57006 =
                          let uu____57007 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____57007  in
                        (match uu____57006 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____57013,t,uu____57015,uu____57016,uu____57017);
                             FStar_Syntax_Syntax.sigrng = uu____57018;
                             FStar_Syntax_Syntax.sigquals = uu____57019;
                             FStar_Syntax_Syntax.sigmeta = uu____57020;
                             FStar_Syntax_Syntax.sigattrs = uu____57021;_} ->
                             let uu____57032 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____57032 with
                              | (formals,uu____57048) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____57102  ->
                                            match uu____57102 with
                                            | (x,q) ->
                                                let uu____57115 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____57115
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____57170  ->
                                            match uu____57170 with
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
                                  ((let uu____57194 =
                                      let uu____57197 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____57197
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____57194);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____57256 =
                                            match uu____57256 with
                                            | (id1,uu____57262) ->
                                                let modul =
                                                  let uu____57265 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____57265.FStar_Ident.str
                                                   in
                                                let uu____57266 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____57266 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____57289 =
                                                         let uu____57290 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____57290
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____57289);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____57335
                                                               =
                                                               let uu____57336
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____57336.FStar_Ident.ident
                                                                in
                                                             uu____57335.FStar_Ident.idText
                                                              in
                                                           let uu____57338 =
                                                             let uu____57339
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____57339
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____57338))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____57391 -> ())
                    | uu____57392 -> ()))
        | uu____57393 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____57415 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____57415 with
        | (ns,id1) ->
            let uu____57432 = peek_record_cache ()  in
            FStar_Util.find_map uu____57432
              (fun record  ->
                 let uu____57438 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____57444  -> FStar_Pervasives_Native.None)
                   uu____57438)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____57446  -> Cont_ignore) (fun uu____57448  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____57454 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____57454)
        (fun k  -> fun uu____57460  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____57476 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____57476 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____57482 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____57502 = try_lookup_record_by_field_name env lid  in
        match uu____57502 with
        | FStar_Pervasives_Native.Some record' when
            let uu____57507 =
              let uu____57509 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____57509  in
            let uu____57510 =
              let uu____57512 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____57512  in
            uu____57507 = uu____57510 ->
            let uu____57514 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____57518  -> Cont_ok ())
               in
            (match uu____57514 with
             | Cont_ok uu____57520 -> true
             | uu____57522 -> false)
        | uu____57526 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____57548 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____57548 with
      | FStar_Pervasives_Native.Some r ->
          let uu____57559 =
            let uu____57565 =
              let uu____57566 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____57567 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____57566 uu____57567  in
            (uu____57565, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____57559
      | uu____57574 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____57592  ->
    let uu____57593 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____57593
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____57614  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___448_57627  ->
      match uu___448_57627 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___449_57665 =
            match uu___449_57665 with
            | Rec_binding uu____57667 -> true
            | uu____57669 -> false  in
          let this_env =
            let uu___1530_57672 = env  in
            let uu____57673 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1530_57672.curmodule);
              curmonad = (uu___1530_57672.curmonad);
              modules = (uu___1530_57672.modules);
              scope_mods = uu____57673;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1530_57672.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1530_57672.sigaccum);
              sigmap = (uu___1530_57672.sigmap);
              iface = (uu___1530_57672.iface);
              admitted_iface = (uu___1530_57672.admitted_iface);
              expect_typ = (uu___1530_57672.expect_typ);
              docs = (uu___1530_57672.docs);
              remaining_iface_decls = (uu___1530_57672.remaining_iface_decls);
              syntax_only = (uu___1530_57672.syntax_only);
              ds_hooks = (uu___1530_57672.ds_hooks);
              dep_graph = (uu___1530_57672.dep_graph)
            }  in
          let uu____57676 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____57676 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____57693 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1538_57718 = env  in
      {
        curmodule = (uu___1538_57718.curmodule);
        curmonad = (uu___1538_57718.curmonad);
        modules = (uu___1538_57718.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1538_57718.exported_ids);
        trans_exported_ids = (uu___1538_57718.trans_exported_ids);
        includes = (uu___1538_57718.includes);
        sigaccum = (uu___1538_57718.sigaccum);
        sigmap = (uu___1538_57718.sigmap);
        iface = (uu___1538_57718.iface);
        admitted_iface = (uu___1538_57718.admitted_iface);
        expect_typ = (uu___1538_57718.expect_typ);
        docs = (uu___1538_57718.docs);
        remaining_iface_decls = (uu___1538_57718.remaining_iface_decls);
        syntax_only = (uu___1538_57718.syntax_only);
        ds_hooks = (uu___1538_57718.ds_hooks);
        dep_graph = (uu___1538_57718.dep_graph)
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
        let uu____57752 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____57752
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____57759 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____57759)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____57803) ->
                let uu____57811 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____57811 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____57816 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____57816
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____57825 =
            let uu____57831 =
              let uu____57833 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____57833 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____57831)  in
          let uu____57837 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____57825 uu____57837  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____57846 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____57859 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____57870 -> (false, true)
            | uu____57883 -> (false, false)  in
          match uu____57846 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____57897 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____57903 =
                       let uu____57905 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____57905  in
                     if uu____57903
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____57897 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____57913 ->
                   (extract_record env globals s;
                    (let uu___1579_57917 = env  in
                     {
                       curmodule = (uu___1579_57917.curmodule);
                       curmonad = (uu___1579_57917.curmonad);
                       modules = (uu___1579_57917.modules);
                       scope_mods = (uu___1579_57917.scope_mods);
                       exported_ids = (uu___1579_57917.exported_ids);
                       trans_exported_ids =
                         (uu___1579_57917.trans_exported_ids);
                       includes = (uu___1579_57917.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1579_57917.sigmap);
                       iface = (uu___1579_57917.iface);
                       admitted_iface = (uu___1579_57917.admitted_iface);
                       expect_typ = (uu___1579_57917.expect_typ);
                       docs = (uu___1579_57917.docs);
                       remaining_iface_decls =
                         (uu___1579_57917.remaining_iface_decls);
                       syntax_only = (uu___1579_57917.syntax_only);
                       ds_hooks = (uu___1579_57917.ds_hooks);
                       dep_graph = (uu___1579_57917.dep_graph)
                     })))
           in
        let env2 =
          let uu___1582_57919 = env1  in
          let uu____57920 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1582_57919.curmodule);
            curmonad = (uu___1582_57919.curmonad);
            modules = (uu___1582_57919.modules);
            scope_mods = uu____57920;
            exported_ids = (uu___1582_57919.exported_ids);
            trans_exported_ids = (uu___1582_57919.trans_exported_ids);
            includes = (uu___1582_57919.includes);
            sigaccum = (uu___1582_57919.sigaccum);
            sigmap = (uu___1582_57919.sigmap);
            iface = (uu___1582_57919.iface);
            admitted_iface = (uu___1582_57919.admitted_iface);
            expect_typ = (uu___1582_57919.expect_typ);
            docs = (uu___1582_57919.docs);
            remaining_iface_decls = (uu___1582_57919.remaining_iface_decls);
            syntax_only = (uu___1582_57919.syntax_only);
            ds_hooks = (uu___1582_57919.ds_hooks);
            dep_graph = (uu___1582_57919.dep_graph)
          }  in
        let uu____57946 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____57972) ->
              let uu____57981 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____57981)
          | uu____58008 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____57946 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____58067  ->
                     match uu____58067 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____58089 =
                                    let uu____58092 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____58092
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____58089);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____58143 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____58143.FStar_Ident.str  in
                                      ((let uu____58145 =
                                          get_exported_id_set env3 modul  in
                                        match uu____58145 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____58167 =
                                              let uu____58168 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____58168
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____58167
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
                let uu___1607_58225 = env3  in
                let uu____58226 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1607_58225.curmodule);
                  curmonad = (uu___1607_58225.curmonad);
                  modules = (uu___1607_58225.modules);
                  scope_mods = uu____58226;
                  exported_ids = (uu___1607_58225.exported_ids);
                  trans_exported_ids = (uu___1607_58225.trans_exported_ids);
                  includes = (uu___1607_58225.includes);
                  sigaccum = (uu___1607_58225.sigaccum);
                  sigmap = (uu___1607_58225.sigmap);
                  iface = (uu___1607_58225.iface);
                  admitted_iface = (uu___1607_58225.admitted_iface);
                  expect_typ = (uu___1607_58225.expect_typ);
                  docs = (uu___1607_58225.docs);
                  remaining_iface_decls =
                    (uu___1607_58225.remaining_iface_decls);
                  syntax_only = (uu___1607_58225.syntax_only);
                  ds_hooks = (uu___1607_58225.ds_hooks);
                  dep_graph = (uu___1607_58225.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____58287 =
        let uu____58292 = resolve_module_name env ns false  in
        match uu____58292 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____58307 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____58325  ->
                      match uu____58325 with
                      | (m,uu____58332) ->
                          let uu____58333 =
                            let uu____58335 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____58335 "."  in
                          let uu____58338 =
                            let uu____58340 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____58340 "."  in
                          FStar_Util.starts_with uu____58333 uu____58338))
               in
            if uu____58307
            then (ns, Open_namespace)
            else
              (let uu____58350 =
                 let uu____58356 =
                   let uu____58358 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____58358
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____58356)  in
               let uu____58362 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____58350 uu____58362)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____58287 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____58384 = resolve_module_name env ns false  in
      match uu____58384 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____58394 = current_module env1  in
              uu____58394.FStar_Ident.str  in
            (let uu____58396 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____58396 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____58420 =
                   let uu____58423 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____58423
                    in
                 FStar_ST.op_Colon_Equals incl uu____58420);
            (match () with
             | () ->
                 let uu____58472 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____58472 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____58492 =
                          let uu____58589 = get_exported_id_set env1 curmod
                             in
                          let uu____58636 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____58589, uu____58636)  in
                        match uu____58492 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____59052 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____59052  in
                              let ex = cur_exports k  in
                              (let uu____59153 =
                                 let uu____59157 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____59157 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____59153);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____59249 =
                                     let uu____59253 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____59253 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____59249)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____59302 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____59404 =
                        let uu____59410 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____59410)
                         in
                      let uu____59414 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____59404 uu____59414))))
      | uu____59415 ->
          let uu____59418 =
            let uu____59424 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____59424)  in
          let uu____59428 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____59418 uu____59428
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____59445 = module_is_defined env l  in
        if uu____59445
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____59452 =
             let uu____59458 =
               let uu____59460 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____59460  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____59458)  in
           let uu____59464 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____59452 uu____59464)
  
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
            ((let uu____59487 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____59487 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____59491 = FStar_Ident.range_of_lid l  in
                  let uu____59492 =
                    let uu____59498 =
                      let uu____59500 = FStar_Ident.string_of_lid l  in
                      let uu____59502 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____59504 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____59500 uu____59502 uu____59504
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____59498)  in
                  FStar_Errors.log_issue uu____59491 uu____59492);
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
                      let uu____59550 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____59550 ->
                      let uu____59555 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____59555 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____59570;
                              FStar_Syntax_Syntax.sigrng = uu____59571;
                              FStar_Syntax_Syntax.sigquals = uu____59572;
                              FStar_Syntax_Syntax.sigmeta = uu____59573;
                              FStar_Syntax_Syntax.sigattrs = uu____59574;_},uu____59575)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____59593;
                              FStar_Syntax_Syntax.sigrng = uu____59594;
                              FStar_Syntax_Syntax.sigquals = uu____59595;
                              FStar_Syntax_Syntax.sigmeta = uu____59596;
                              FStar_Syntax_Syntax.sigattrs = uu____59597;_},uu____59598)
                           -> lids
                       | uu____59626 ->
                           ((let uu____59635 =
                               let uu____59637 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____59637  in
                             if uu____59635
                             then
                               let uu____59640 = FStar_Ident.range_of_lid l
                                  in
                               let uu____59641 =
                                 let uu____59647 =
                                   let uu____59649 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____59649
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____59647)
                                  in
                               FStar_Errors.log_issue uu____59640 uu____59641
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1710_59666 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1710_59666.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1710_59666.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1710_59666.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1710_59666.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____59668 -> lids) [])
         in
      let uu___1715_59669 = m  in
      let uu____59670 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____59680,uu____59681) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1724_59684 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1724_59684.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1724_59684.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1724_59684.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1724_59684.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____59685 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1715_59669.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____59670;
        FStar_Syntax_Syntax.exports =
          (uu___1715_59669.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1715_59669.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____59709) ->
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
                                (lid,uu____59730,uu____59731,uu____59732,uu____59733,uu____59734)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____59750,uu____59751)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____59768 =
                                        let uu____59775 =
                                          let uu____59776 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____59777 =
                                            let uu____59784 =
                                              let uu____59785 =
                                                let uu____59800 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____59800)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____59785
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____59784
                                             in
                                          uu____59777
                                            FStar_Pervasives_Native.None
                                            uu____59776
                                           in
                                        (lid, univ_names, uu____59775)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____59768
                                       in
                                    let se2 =
                                      let uu___1756_59814 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1756_59814.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1756_59814.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1756_59814.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____59824 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____59828,uu____59829) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____59838,lbs),uu____59840)
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
                             let uu____59858 =
                               let uu____59860 =
                                 let uu____59861 =
                                   let uu____59864 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____59864.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____59861.FStar_Syntax_Syntax.v  in
                               uu____59860.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____59858))
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
                               let uu____59881 =
                                 let uu____59884 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____59884.FStar_Syntax_Syntax.fv_name  in
                               uu____59881.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1779_59889 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1779_59889.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1779_59889.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1779_59889.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____59899 -> ()));
      (let curmod =
         let uu____59902 = current_module env  in uu____59902.FStar_Ident.str
          in
       (let uu____59904 =
          let uu____60001 = get_exported_id_set env curmod  in
          let uu____60048 = get_trans_exported_id_set env curmod  in
          (uu____60001, uu____60048)  in
        match uu____59904 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____60467 = cur_ex eikind  in
                FStar_ST.op_Bang uu____60467  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____60573 =
                let uu____60577 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____60577  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____60573  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____60626 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1797_60724 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1797_60724.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1797_60724.exported_ids);
                    trans_exported_ids = (uu___1797_60724.trans_exported_ids);
                    includes = (uu___1797_60724.includes);
                    sigaccum = [];
                    sigmap = (uu___1797_60724.sigmap);
                    iface = (uu___1797_60724.iface);
                    admitted_iface = (uu___1797_60724.admitted_iface);
                    expect_typ = (uu___1797_60724.expect_typ);
                    docs = (uu___1797_60724.docs);
                    remaining_iface_decls =
                      (uu___1797_60724.remaining_iface_decls);
                    syntax_only = (uu___1797_60724.syntax_only);
                    ds_hooks = (uu___1797_60724.ds_hooks);
                    dep_graph = (uu___1797_60724.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____60751  ->
         push_record_cache ();
         (let uu____60754 =
            let uu____60757 = FStar_ST.op_Bang stack  in env :: uu____60757
             in
          FStar_ST.op_Colon_Equals stack uu____60754);
         (let uu___1803_60806 = env  in
          let uu____60807 = FStar_Util.smap_copy env.exported_ids  in
          let uu____60812 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____60817 = FStar_Util.smap_copy env.includes  in
          let uu____60828 = FStar_Util.smap_copy env.sigmap  in
          let uu____60841 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1803_60806.curmodule);
            curmonad = (uu___1803_60806.curmonad);
            modules = (uu___1803_60806.modules);
            scope_mods = (uu___1803_60806.scope_mods);
            exported_ids = uu____60807;
            trans_exported_ids = uu____60812;
            includes = uu____60817;
            sigaccum = (uu___1803_60806.sigaccum);
            sigmap = uu____60828;
            iface = (uu___1803_60806.iface);
            admitted_iface = (uu___1803_60806.admitted_iface);
            expect_typ = (uu___1803_60806.expect_typ);
            docs = uu____60841;
            remaining_iface_decls = (uu___1803_60806.remaining_iface_decls);
            syntax_only = (uu___1803_60806.syntax_only);
            ds_hooks = (uu___1803_60806.ds_hooks);
            dep_graph = (uu___1803_60806.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____60849  ->
    FStar_Util.atomically
      (fun uu____60856  ->
         let uu____60857 = FStar_ST.op_Bang stack  in
         match uu____60857 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____60912 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____60959 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____60963 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____61005 = FStar_Util.smap_try_find sm' k  in
              match uu____61005 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1838_61036 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1838_61036.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1838_61036.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1838_61036.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1838_61036.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____61037 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____61045 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____61072 = finish env modul1  in (uu____61072, modul1)
  
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
      let uu____61141 =
        let uu____61145 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____61145  in
      FStar_Util.set_elements uu____61141  in
    let fields =
      let uu____61208 =
        let uu____61212 = e Exported_id_field  in
        FStar_ST.op_Bang uu____61212  in
      FStar_Util.set_elements uu____61208  in
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
          let uu____61304 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____61304  in
        let fields =
          let uu____61318 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____61318  in
        (fun uu___450_61326  ->
           match uu___450_61326 with
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
  'Auu____61430 .
    'Auu____61430 Prims.list FStar_Pervasives_Native.option ->
      'Auu____61430 Prims.list FStar_ST.ref
  =
  fun uu___451_61443  ->
    match uu___451_61443 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____61486 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____61486 as_exported_ids  in
      let uu____61492 = as_ids_opt env.exported_ids  in
      let uu____61495 = as_ids_opt env.trans_exported_ids  in
      let uu____61498 =
        let uu____61503 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____61503 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____61492;
        mii_trans_exported_ids = uu____61495;
        mii_includes = uu____61498
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
                let uu____61592 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____61592 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___452_61614 =
                  match uu___452_61614 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____61626  ->
                     match uu____61626 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____61652 =
                    let uu____61657 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____61657, Open_namespace)  in
                  [uu____61652]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____61688 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____61688);
              (match () with
               | () ->
                   ((let uu____61693 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____61693);
                    (match () with
                     | () ->
                         ((let uu____61698 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____61698);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1908_61708 = env1  in
                                 let uu____61709 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1908_61708.curmonad);
                                   modules = (uu___1908_61708.modules);
                                   scope_mods = uu____61709;
                                   exported_ids =
                                     (uu___1908_61708.exported_ids);
                                   trans_exported_ids =
                                     (uu___1908_61708.trans_exported_ids);
                                   includes = (uu___1908_61708.includes);
                                   sigaccum = (uu___1908_61708.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1908_61708.expect_typ);
                                   docs = (uu___1908_61708.docs);
                                   remaining_iface_decls =
                                     (uu___1908_61708.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1908_61708.syntax_only);
                                   ds_hooks = (uu___1908_61708.ds_hooks);
                                   dep_graph = (uu___1908_61708.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____61721 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____61747  ->
                      match uu____61747 with
                      | (l,uu____61754) -> FStar_Ident.lid_equals l mname))
               in
            match uu____61721 with
            | FStar_Pervasives_Native.None  ->
                let uu____61764 = prep env  in (uu____61764, false)
            | FStar_Pervasives_Native.Some (uu____61767,m) ->
                ((let uu____61774 =
                    (let uu____61778 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____61778) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____61774
                  then
                    let uu____61781 =
                      let uu____61787 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____61787)
                       in
                    let uu____61791 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____61781 uu____61791
                  else ());
                 (let uu____61794 =
                    let uu____61795 = push env  in prep uu____61795  in
                  (uu____61794, true)))
  
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
          let uu___1929_61813 = env  in
          {
            curmodule = (uu___1929_61813.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1929_61813.modules);
            scope_mods = (uu___1929_61813.scope_mods);
            exported_ids = (uu___1929_61813.exported_ids);
            trans_exported_ids = (uu___1929_61813.trans_exported_ids);
            includes = (uu___1929_61813.includes);
            sigaccum = (uu___1929_61813.sigaccum);
            sigmap = (uu___1929_61813.sigmap);
            iface = (uu___1929_61813.iface);
            admitted_iface = (uu___1929_61813.admitted_iface);
            expect_typ = (uu___1929_61813.expect_typ);
            docs = (uu___1929_61813.docs);
            remaining_iface_decls = (uu___1929_61813.remaining_iface_decls);
            syntax_only = (uu___1929_61813.syntax_only);
            ds_hooks = (uu___1929_61813.ds_hooks);
            dep_graph = (uu___1929_61813.dep_graph)
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
        let uu____61848 = lookup1 lid  in
        match uu____61848 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____61863  ->
                   match uu____61863 with
                   | (lid1,uu____61870) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____61873 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____61873  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____61885 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____61886 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____61885 uu____61886  in
                 let uu____61887 = resolve_module_name env modul true  in
                 match uu____61887 with
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
            let uu____61908 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____61908
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____61938 = lookup1 id1  in
      match uu____61938 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  