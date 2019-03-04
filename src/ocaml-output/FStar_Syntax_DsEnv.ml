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
    match projectee with | Open_module  -> true | uu____53603 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____53614 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____53834 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____53854 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____53874 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____53894 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____53914 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____53934 -> false
  
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
    | uu____53956 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____53967 -> false
  
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
    ds_push_open_hook = (fun uu____55587  -> fun uu____55588  -> ());
    ds_push_include_hook = (fun uu____55591  -> fun uu____55592  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____55596  -> fun uu____55597  -> fun uu____55598  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____55635 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____55677 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___549_55712 = env  in
      {
        curmodule = (uu___549_55712.curmodule);
        curmonad = (uu___549_55712.curmonad);
        modules = (uu___549_55712.modules);
        scope_mods = (uu___549_55712.scope_mods);
        exported_ids = (uu___549_55712.exported_ids);
        trans_exported_ids = (uu___549_55712.trans_exported_ids);
        includes = (uu___549_55712.includes);
        sigaccum = (uu___549_55712.sigaccum);
        sigmap = (uu___549_55712.sigmap);
        iface = b;
        admitted_iface = (uu___549_55712.admitted_iface);
        expect_typ = (uu___549_55712.expect_typ);
        docs = (uu___549_55712.docs);
        remaining_iface_decls = (uu___549_55712.remaining_iface_decls);
        syntax_only = (uu___549_55712.syntax_only);
        ds_hooks = (uu___549_55712.ds_hooks);
        dep_graph = (uu___549_55712.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___554_55733 = e  in
      {
        curmodule = (uu___554_55733.curmodule);
        curmonad = (uu___554_55733.curmonad);
        modules = (uu___554_55733.modules);
        scope_mods = (uu___554_55733.scope_mods);
        exported_ids = (uu___554_55733.exported_ids);
        trans_exported_ids = (uu___554_55733.trans_exported_ids);
        includes = (uu___554_55733.includes);
        sigaccum = (uu___554_55733.sigaccum);
        sigmap = (uu___554_55733.sigmap);
        iface = (uu___554_55733.iface);
        admitted_iface = b;
        expect_typ = (uu___554_55733.expect_typ);
        docs = (uu___554_55733.docs);
        remaining_iface_decls = (uu___554_55733.remaining_iface_decls);
        syntax_only = (uu___554_55733.syntax_only);
        ds_hooks = (uu___554_55733.ds_hooks);
        dep_graph = (uu___554_55733.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___559_55754 = e  in
      {
        curmodule = (uu___559_55754.curmodule);
        curmonad = (uu___559_55754.curmonad);
        modules = (uu___559_55754.modules);
        scope_mods = (uu___559_55754.scope_mods);
        exported_ids = (uu___559_55754.exported_ids);
        trans_exported_ids = (uu___559_55754.trans_exported_ids);
        includes = (uu___559_55754.includes);
        sigaccum = (uu___559_55754.sigaccum);
        sigmap = (uu___559_55754.sigmap);
        iface = (uu___559_55754.iface);
        admitted_iface = (uu___559_55754.admitted_iface);
        expect_typ = b;
        docs = (uu___559_55754.docs);
        remaining_iface_decls = (uu___559_55754.remaining_iface_decls);
        syntax_only = (uu___559_55754.syntax_only);
        ds_hooks = (uu___559_55754.ds_hooks);
        dep_graph = (uu___559_55754.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____55781 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____55781 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____55794 =
            let uu____55798 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____55798  in
          FStar_All.pipe_right uu____55794 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___420_55939  ->
         match uu___420_55939 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____55944 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___578_55956 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___578_55956.curmonad);
        modules = (uu___578_55956.modules);
        scope_mods = (uu___578_55956.scope_mods);
        exported_ids = (uu___578_55956.exported_ids);
        trans_exported_ids = (uu___578_55956.trans_exported_ids);
        includes = (uu___578_55956.includes);
        sigaccum = (uu___578_55956.sigaccum);
        sigmap = (uu___578_55956.sigmap);
        iface = (uu___578_55956.iface);
        admitted_iface = (uu___578_55956.admitted_iface);
        expect_typ = (uu___578_55956.expect_typ);
        docs = (uu___578_55956.docs);
        remaining_iface_decls = (uu___578_55956.remaining_iface_decls);
        syntax_only = (uu___578_55956.syntax_only);
        ds_hooks = (uu___578_55956.ds_hooks);
        dep_graph = (uu___578_55956.dep_graph)
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
      let uu____55980 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____56014  ->
                match uu____56014 with
                | (m,uu____56023) -> FStar_Ident.lid_equals l m))
         in
      match uu____55980 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____56040,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____56074 =
          FStar_List.partition
            (fun uu____56104  ->
               match uu____56104 with
               | (m,uu____56113) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____56074 with
        | (uu____56118,rest) ->
            let uu___603_56152 = env  in
            {
              curmodule = (uu___603_56152.curmodule);
              curmonad = (uu___603_56152.curmonad);
              modules = (uu___603_56152.modules);
              scope_mods = (uu___603_56152.scope_mods);
              exported_ids = (uu___603_56152.exported_ids);
              trans_exported_ids = (uu___603_56152.trans_exported_ids);
              includes = (uu___603_56152.includes);
              sigaccum = (uu___603_56152.sigaccum);
              sigmap = (uu___603_56152.sigmap);
              iface = (uu___603_56152.iface);
              admitted_iface = (uu___603_56152.admitted_iface);
              expect_typ = (uu___603_56152.expect_typ);
              docs = (uu___603_56152.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___603_56152.syntax_only);
              ds_hooks = (uu___603_56152.ds_hooks);
              dep_graph = (uu___603_56152.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____56181 = current_module env  in qual uu____56181 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____56183 =
            let uu____56184 = current_module env  in qual uu____56184 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____56183
            id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___613_56205 = env  in
      {
        curmodule = (uu___613_56205.curmodule);
        curmonad = (uu___613_56205.curmonad);
        modules = (uu___613_56205.modules);
        scope_mods = (uu___613_56205.scope_mods);
        exported_ids = (uu___613_56205.exported_ids);
        trans_exported_ids = (uu___613_56205.trans_exported_ids);
        includes = (uu___613_56205.includes);
        sigaccum = (uu___613_56205.sigaccum);
        sigmap = (uu___613_56205.sigmap);
        iface = (uu___613_56205.iface);
        admitted_iface = (uu___613_56205.admitted_iface);
        expect_typ = (uu___613_56205.expect_typ);
        docs = (uu___613_56205.docs);
        remaining_iface_decls = (uu___613_56205.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___613_56205.ds_hooks);
        dep_graph = (uu___613_56205.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___618_56223 = env  in
      {
        curmodule = (uu___618_56223.curmodule);
        curmonad = (uu___618_56223.curmonad);
        modules = (uu___618_56223.modules);
        scope_mods = (uu___618_56223.scope_mods);
        exported_ids = (uu___618_56223.exported_ids);
        trans_exported_ids = (uu___618_56223.trans_exported_ids);
        includes = (uu___618_56223.includes);
        sigaccum = (uu___618_56223.sigaccum);
        sigmap = (uu___618_56223.sigmap);
        iface = (uu___618_56223.iface);
        admitted_iface = (uu___618_56223.admitted_iface);
        expect_typ = (uu___618_56223.expect_typ);
        docs = (uu___618_56223.docs);
        remaining_iface_decls = (uu___618_56223.remaining_iface_decls);
        syntax_only = (uu___618_56223.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___618_56223.dep_graph)
      }
  
let new_sigmap : 'Auu____56229 . unit -> 'Auu____56229 FStar_Util.smap =
  fun uu____56236  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____56244 = new_sigmap ()  in
    let uu____56249 = new_sigmap ()  in
    let uu____56254 = new_sigmap ()  in
    let uu____56265 = new_sigmap ()  in
    let uu____56278 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____56244;
      trans_exported_ids = uu____56249;
      includes = uu____56254;
      sigaccum = [];
      sigmap = uu____56265;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____56278;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___625_56312 = env  in
      {
        curmodule = (uu___625_56312.curmodule);
        curmonad = (uu___625_56312.curmonad);
        modules = (uu___625_56312.modules);
        scope_mods = (uu___625_56312.scope_mods);
        exported_ids = (uu___625_56312.exported_ids);
        trans_exported_ids = (uu___625_56312.trans_exported_ids);
        includes = (uu___625_56312.includes);
        sigaccum = (uu___625_56312.sigaccum);
        sigmap = (uu___625_56312.sigmap);
        iface = (uu___625_56312.iface);
        admitted_iface = (uu___625_56312.admitted_iface);
        expect_typ = (uu___625_56312.expect_typ);
        docs = (uu___625_56312.docs);
        remaining_iface_decls = (uu___625_56312.remaining_iface_decls);
        syntax_only = (uu___625_56312.syntax_only);
        ds_hooks = (uu___625_56312.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____56340  ->
         match uu____56340 with
         | (m,uu____56347) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___634_56360 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___634_56360.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___637_56361 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index =
          (uu___637_56361.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___637_56361.FStar_Syntax_Syntax.sort)
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
      (fun uu____56464  ->
         match uu____56464 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____56495 =
                 let uu____56496 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____56496 dd dq  in
               FStar_Pervasives_Native.Some uu____56495
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____56536 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____56574 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____56595 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___421_56625  ->
      match uu___421_56625 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____56644 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____56644 cont_t) -> 'Auu____56644 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____56681 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____56681
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____56697  ->
                   match uu____56697 with
                   | (f,uu____56705) ->
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
  fun uu___422_56779  ->
    match uu___422_56779 with
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
              let rec aux uu___423_56855 =
                match uu___423_56855 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____56868 = get_exported_id_set env mname  in
                      match uu____56868 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____56895 = mex eikind  in
                            FStar_ST.op_Bang uu____56895  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____57010 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____57010 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____57087 = qual modul id1  in
                        find_in_module uu____57087
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____57092 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___424_57101  ->
    match uu___424_57101 with
    | Exported_id_field  -> true
    | uu____57104 -> false
  
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
                  let check_local_binding_id uu___425_57228 =
                    match uu___425_57228 with
                    | (id',uu____57231) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___426_57239 =
                    match uu___426_57239 with
                    | (id',uu____57242,uu____57243) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____57248 = current_module env  in
                    FStar_Ident.ids_of_lid uu____57248  in
                  let proc uu___427_57256 =
                    match uu___427_57256 with
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
                        let uu____57265 = FStar_Ident.lid_of_ids curmod_ns
                           in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____57265 id1
                    | uu____57270 -> Cont_ignore  in
                  let rec aux uu___428_57280 =
                    match uu___428_57280 with
                    | a::q ->
                        let uu____57289 = proc a  in
                        option_of_cont (fun uu____57293  -> aux q)
                          uu____57289
                    | [] ->
                        let uu____57294 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____57298  -> FStar_Pervasives_Native.None)
                          uu____57294
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____57306 .
    FStar_Range.range ->
      ('Auu____57306 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____57320  -> match uu____57320 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____57338 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____57338)
          -> 'Auu____57338 -> 'Auu____57338
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____57379 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____57379 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____57423 = unmangleOpName id1  in
      match uu____57423 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____57429 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____57435 =
                 found_local_binding id1.FStar_Ident.idRange r  in
               Cont_ok uu____57435) (fun uu____57437  -> Cont_fail)
            (fun uu____57439  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____57446  -> fun uu____57447  -> Cont_fail)
                 Cont_ignore)
            (fun uu____57455  -> fun uu____57456  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____57530 ->
                let lid = qualify env id1  in
                let uu____57532 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____57532 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____57560 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____57560
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____57584 = current_module env  in qual uu____57584 id1
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
        let rec aux uu___429_57656 =
          match uu___429_57656 with
          | [] ->
              let uu____57661 = module_is_defined env lid  in
              if uu____57661
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____57673 =
                  let uu____57674 = FStar_Ident.path_of_lid ns  in
                  let uu____57678 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____57674 uu____57678  in
                let uu____57683 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____57673 uu____57683  in
              let uu____57684 = module_is_defined env new_lid  in
              if uu____57684
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____57693 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____57703::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____57723 =
          let uu____57725 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____57725  in
        if uu____57723
        then
          let uu____57727 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____57727
           then ()
           else
             (let uu____57732 =
                let uu____57738 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____57738)
                 in
              let uu____57742 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____57732 uu____57742))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____57756 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____57760 = resolve_module_name env modul_orig true  in
          (match uu____57760 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____57765 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___430_57788  ->
             match uu___430_57788 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____57792 -> false) env.scope_mods
  
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
                 let uu____57921 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____57921
                   (FStar_Util.map_option
                      (fun uu____57971  ->
                         match uu____57971 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____58041 = aux ns_rev_prefix ns_last_id  in
              (match uu____58041 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____58104 =
            let uu____58107 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____58107 true  in
          match uu____58104 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____58122 -> do_shorten env ids
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
                  | uu____58243::uu____58244 ->
                      let uu____58247 =
                        let uu____58250 =
                          let uu____58251 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____58252 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____58251 uu____58252
                           in
                        resolve_module_name env uu____58250 true  in
                      (match uu____58247 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____58257 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____58261  ->
                                FStar_Pervasives_Native.None) uu____58257)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___431_58285  ->
      match uu___431_58285 with
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
              let uu____58406 = k_global_def lid1 def  in
              cont_of_option k uu____58406  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____58442 = k_local_binding l  in
                 cont_of_option Cont_fail uu____58442)
              (fun r  ->
                 let uu____58448 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____58448)
              (fun uu____58452  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____58463,uu____58464,uu____58465,l,uu____58467,uu____58468) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___432_58481  ->
               match uu___432_58481 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____58484,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____58496 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____58502,uu____58503,uu____58504) -> FStar_Pervasives_Native.None
    | uu____58505 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____58521 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____58529 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____58529
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____58521 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____58552 =
         let uu____58553 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____58553  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____58552) &&
        (let uu____58561 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____58561 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____58578 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___433_58585  ->
                     match uu___433_58585 with
                     | FStar_Syntax_Syntax.Projector uu____58587 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____58593 -> true
                     | uu____58595 -> false)))
           in
        if uu____58578
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____58600 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___434_58606  ->
                 match uu___434_58606 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____58609 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___435_58615  ->
                    match uu___435_58615 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____58618 -> false)))
             &&
             (let uu____58621 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___436_58627  ->
                        match uu___436_58627 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____58630 -> false))
                 in
              Prims.op_Negation uu____58621))
         in
      if uu____58600 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___439_58682 =
            match uu___439_58682 with
            | (uu____58690,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____58694) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____58699 ->
                     let uu____58716 =
                       let uu____58717 =
                         let uu____58724 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____58724, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58717  in
                     FStar_Pervasives_Native.Some uu____58716
                 | FStar_Syntax_Syntax.Sig_datacon uu____58727 ->
                     let uu____58743 =
                       let uu____58744 =
                         let uu____58751 =
                           let uu____58752 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____58752
                            in
                         (uu____58751, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58744  in
                     FStar_Pervasives_Native.Some uu____58743
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____58757,lbs),uu____58759) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____58771 =
                       let uu____58772 =
                         let uu____58779 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____58779, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58772  in
                     FStar_Pervasives_Native.Some uu____58771
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____58783,uu____58784) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____58788 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___437_58794  ->
                                  match uu___437_58794 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____58797 -> false)))
                        in
                     if uu____58788
                     then
                       let lid2 =
                         let uu____58803 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____58803  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____58805 =
                         FStar_Util.find_map quals
                           (fun uu___438_58810  ->
                              match uu___438_58810 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____58814 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____58805 with
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
                        | uu____58823 ->
                            let uu____58826 =
                              let uu____58827 =
                                let uu____58834 =
                                  let uu____58835 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____58835
                                   in
                                (uu____58834,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____58827  in
                            FStar_Pervasives_Native.Some uu____58826)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____58843 =
                       let uu____58844 =
                         let uu____58849 =
                           let uu____58850 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____58850
                            in
                         (se, uu____58849)  in
                       Eff_name uu____58844  in
                     FStar_Pervasives_Native.Some uu____58843
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____58852 =
                       let uu____58853 =
                         let uu____58858 =
                           let uu____58859 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____58859
                            in
                         (se, uu____58858)  in
                       Eff_name uu____58853  in
                     FStar_Pervasives_Native.Some uu____58852
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____58860 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____58879 =
                       let uu____58880 =
                         let uu____58887 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____58887, [])  in
                       Term_name uu____58880  in
                     FStar_Pervasives_Native.Some uu____58879
                 | uu____58891 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____58909 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____58909 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____58925 =
            match uu____58925 with
            | (id1,l,dd) ->
                let uu____58937 =
                  let uu____58938 =
                    let uu____58945 =
                      let uu____58946 =
                        let uu____58947 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____58947  in
                      FStar_Syntax_Syntax.fvar uu____58946 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____58945, [])  in
                  Term_name uu____58938  in
                FStar_Pervasives_Native.Some uu____58937
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____58955 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____58955 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____58963 -> FStar_Pervasives_Native.None)
            | uu____58966 -> FStar_Pervasives_Native.None  in
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
        let uu____59004 = try_lookup_name true exclude_interf env lid  in
        match uu____59004 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____59020 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59040 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59040 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____59055 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59081 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59081 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____59097;
             FStar_Syntax_Syntax.sigquals = uu____59098;
             FStar_Syntax_Syntax.sigmeta = uu____59099;
             FStar_Syntax_Syntax.sigattrs = uu____59100;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____59119;
             FStar_Syntax_Syntax.sigquals = uu____59120;
             FStar_Syntax_Syntax.sigmeta = uu____59121;
             FStar_Syntax_Syntax.sigattrs = uu____59122;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____59140,uu____59141,uu____59142,uu____59143,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____59145;
             FStar_Syntax_Syntax.sigquals = uu____59146;
             FStar_Syntax_Syntax.sigmeta = uu____59147;
             FStar_Syntax_Syntax.sigattrs = uu____59148;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____59170 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59196 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59196 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____59206;
             FStar_Syntax_Syntax.sigquals = uu____59207;
             FStar_Syntax_Syntax.sigmeta = uu____59208;
             FStar_Syntax_Syntax.sigattrs = uu____59209;_},uu____59210)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____59220;
             FStar_Syntax_Syntax.sigquals = uu____59221;
             FStar_Syntax_Syntax.sigmeta = uu____59222;
             FStar_Syntax_Syntax.sigattrs = uu____59223;_},uu____59224)
          -> FStar_Pervasives_Native.Some ne
      | uu____59233 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____59252 = try_lookup_effect_name env lid  in
      match uu____59252 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____59257 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59272 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59272 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____59282,uu____59283,uu____59284,uu____59285);
             FStar_Syntax_Syntax.sigrng = uu____59286;
             FStar_Syntax_Syntax.sigquals = uu____59287;
             FStar_Syntax_Syntax.sigmeta = uu____59288;
             FStar_Syntax_Syntax.sigattrs = uu____59289;_},uu____59290)
          ->
          let rec aux new_name =
            let uu____59311 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____59311 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____59332) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____59343 =
                       let uu____59344 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____59344
                        in
                     FStar_Pervasives_Native.Some uu____59343
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____59346 =
                       let uu____59347 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____59347
                        in
                     FStar_Pervasives_Native.Some uu____59346
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____59348,uu____59349,uu____59350,cmp,uu____59352) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____59358 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____59359,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____59365 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___440_59404 =
        match uu___440_59404 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____59414,uu____59415,uu____59416);
             FStar_Syntax_Syntax.sigrng = uu____59417;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____59419;
             FStar_Syntax_Syntax.sigattrs = uu____59420;_},uu____59421)
            -> FStar_Pervasives_Native.Some quals
        | uu____59430 -> FStar_Pervasives_Native.None  in
      let uu____59438 =
        resolve_in_open_namespaces' env lid
          (fun uu____59446  -> FStar_Pervasives_Native.None)
          (fun uu____59450  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____59438 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____59460 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____59478 =
        FStar_List.tryFind
          (fun uu____59493  ->
             match uu____59493 with
             | (mlid,modul) ->
                 let uu____59501 = FStar_Ident.path_of_lid mlid  in
                 uu____59501 = path) env.modules
         in
      match uu____59478 with
      | FStar_Pervasives_Native.Some (uu____59504,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___441_59544 =
        match uu___441_59544 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____59552,lbs),uu____59554);
             FStar_Syntax_Syntax.sigrng = uu____59555;
             FStar_Syntax_Syntax.sigquals = uu____59556;
             FStar_Syntax_Syntax.sigmeta = uu____59557;
             FStar_Syntax_Syntax.sigattrs = uu____59558;_},uu____59559)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____59577 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____59577
        | uu____59578 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____59585  -> FStar_Pervasives_Native.None)
        (fun uu____59587  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___442_59620 =
        match uu___442_59620 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____59631);
             FStar_Syntax_Syntax.sigrng = uu____59632;
             FStar_Syntax_Syntax.sigquals = uu____59633;
             FStar_Syntax_Syntax.sigmeta = uu____59634;
             FStar_Syntax_Syntax.sigattrs = uu____59635;_},uu____59636)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____59662 -> FStar_Pervasives_Native.None)
        | uu____59669 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____59680  -> FStar_Pervasives_Native.None)
        (fun uu____59684  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____59744 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____59744 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____59769 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____59807) ->
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
      let uu____59865 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____59865 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59897 = try_lookup_lid env l  in
      match uu____59897 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____59903 =
            let uu____59904 = FStar_Syntax_Subst.compress e  in
            uu____59904.FStar_Syntax_Syntax.n  in
          (match uu____59903 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____59910 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____59922 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____59922 with
      | (uu____59932,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____59953 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____59957 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____59957 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____59962 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___1304_59993 = env  in
        {
          curmodule = (uu___1304_59993.curmodule);
          curmonad = (uu___1304_59993.curmonad);
          modules = (uu___1304_59993.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___1304_59993.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___1304_59993.sigaccum);
          sigmap = (uu___1304_59993.sigmap);
          iface = (uu___1304_59993.iface);
          admitted_iface = (uu___1304_59993.admitted_iface);
          expect_typ = (uu___1304_59993.expect_typ);
          docs = (uu___1304_59993.docs);
          remaining_iface_decls = (uu___1304_59993.remaining_iface_decls);
          syntax_only = (uu___1304_59993.syntax_only);
          ds_hooks = (uu___1304_59993.ds_hooks);
          dep_graph = (uu___1304_59993.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____60009 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____60009 drop_attributes
  
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
               (uu____60079,uu____60080,uu____60081);
             FStar_Syntax_Syntax.sigrng = uu____60082;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____60084;
             FStar_Syntax_Syntax.sigattrs = uu____60085;_},uu____60086)
            ->
            let uu____60093 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___443_60099  ->
                      match uu___443_60099 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____60102 -> false))
               in
            if uu____60093
            then
              let uu____60107 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____60107
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____60110;
             FStar_Syntax_Syntax.sigrng = uu____60111;
             FStar_Syntax_Syntax.sigquals = uu____60112;
             FStar_Syntax_Syntax.sigmeta = uu____60113;
             FStar_Syntax_Syntax.sigattrs = uu____60114;_},uu____60115)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____60141 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____60141
        | uu____60142 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____60149  -> FStar_Pervasives_Native.None)
        (fun uu____60151  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___444_60186 =
        match uu___444_60186 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____60196,uu____60197,uu____60198,uu____60199,datas,uu____60201);
             FStar_Syntax_Syntax.sigrng = uu____60202;
             FStar_Syntax_Syntax.sigquals = uu____60203;
             FStar_Syntax_Syntax.sigmeta = uu____60204;
             FStar_Syntax_Syntax.sigattrs = uu____60205;_},uu____60206)
            -> FStar_Pervasives_Native.Some datas
        | uu____60223 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____60234  -> FStar_Pervasives_Native.None)
        (fun uu____60238  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____60317 =
    let uu____60318 =
      let uu____60323 =
        let uu____60326 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____60326  in
      let uu____60382 = FStar_ST.op_Bang record_cache  in uu____60323 ::
        uu____60382
       in
    FStar_ST.op_Colon_Equals record_cache uu____60318  in
  let pop1 uu____60492 =
    let uu____60493 =
      let uu____60498 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____60498  in
    FStar_ST.op_Colon_Equals record_cache uu____60493  in
  let snapshot1 uu____60613 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____60681 =
    let uu____60682 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____60682  in
  let insert r =
    let uu____60744 =
      let uu____60749 = let uu____60752 = peek1 ()  in r :: uu____60752  in
      let uu____60755 =
        let uu____60760 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____60760  in
      uu____60749 :: uu____60755  in
    FStar_ST.op_Colon_Equals record_cache uu____60744  in
  let filter1 uu____60872 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____60881 =
      let uu____60886 =
        let uu____60891 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____60891  in
      filtered :: uu____60886  in
    FStar_ST.op_Colon_Equals record_cache uu____60881  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____61883) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___445_61902  ->
                   match uu___445_61902 with
                   | FStar_Syntax_Syntax.RecordType uu____61904 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____61914 ->
                       true
                   | uu____61924 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___446_61949  ->
                      match uu___446_61949 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____61952,uu____61953,uu____61954,uu____61955,uu____61956);
                          FStar_Syntax_Syntax.sigrng = uu____61957;
                          FStar_Syntax_Syntax.sigquals = uu____61958;
                          FStar_Syntax_Syntax.sigmeta = uu____61959;
                          FStar_Syntax_Syntax.sigattrs = uu____61960;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____61971 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___447_62007  ->
                    match uu___447_62007 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____62011,uu____62012,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____62014;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____62016;
                        FStar_Syntax_Syntax.sigattrs = uu____62017;_} ->
                        let uu____62028 =
                          let uu____62029 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____62029  in
                        (match uu____62028 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____62035,t,uu____62037,uu____62038,uu____62039);
                             FStar_Syntax_Syntax.sigrng = uu____62040;
                             FStar_Syntax_Syntax.sigquals = uu____62041;
                             FStar_Syntax_Syntax.sigmeta = uu____62042;
                             FStar_Syntax_Syntax.sigattrs = uu____62043;_} ->
                             let uu____62054 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____62054 with
                              | (formals,uu____62070) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____62124  ->
                                            match uu____62124 with
                                            | (x,q) ->
                                                let uu____62137 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____62137
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____62192  ->
                                            match uu____62192 with
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
                                  ((let uu____62216 =
                                      let uu____62219 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____62219
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____62216);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____62322 =
                                            match uu____62322 with
                                            | (id1,uu____62328) ->
                                                let modul =
                                                  let uu____62331 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____62331.FStar_Ident.str
                                                   in
                                                let uu____62332 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____62332 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____62366 =
                                                         let uu____62367 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____62367
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____62366);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____62456
                                                               =
                                                               let uu____62457
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____62457.FStar_Ident.ident
                                                                in
                                                             uu____62456.FStar_Ident.idText
                                                              in
                                                           let uu____62459 =
                                                             let uu____62460
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____62460
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____62459))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____62556 -> ())
                    | uu____62557 -> ()))
        | uu____62558 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____62580 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____62580 with
        | (ns,id1) ->
            let uu____62597 = peek_record_cache ()  in
            FStar_Util.find_map uu____62597
              (fun record  ->
                 let uu____62603 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____62609  -> FStar_Pervasives_Native.None)
                   uu____62603)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____62611  -> Cont_ignore) (fun uu____62613  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____62619 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____62619)
        (fun k  -> fun uu____62625  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____62641 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____62641 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____62647 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____62667 = try_lookup_record_by_field_name env lid  in
        match uu____62667 with
        | FStar_Pervasives_Native.Some record' when
            let uu____62672 =
              let uu____62674 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____62674  in
            let uu____62675 =
              let uu____62677 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____62677  in
            uu____62672 = uu____62675 ->
            let uu____62679 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____62683  -> Cont_ok ())
               in
            (match uu____62679 with
             | Cont_ok uu____62685 -> true
             | uu____62687 -> false)
        | uu____62691 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____62713 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____62713 with
      | FStar_Pervasives_Native.Some r ->
          let uu____62724 =
            let uu____62730 =
              let uu____62731 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____62732 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____62731 uu____62732  in
            (uu____62730, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____62724
      | uu____62739 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____62768  ->
    let uu____62769 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____62769
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____62801  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___448_62814  ->
      match uu___448_62814 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___449_62874 =
            match uu___449_62874 with
            | Rec_binding uu____62876 -> true
            | uu____62878 -> false  in
          let this_env =
            let uu___1530_62881 = env  in
            let uu____62882 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1530_62881.curmodule);
              curmonad = (uu___1530_62881.curmonad);
              modules = (uu___1530_62881.modules);
              scope_mods = uu____62882;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1530_62881.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1530_62881.sigaccum);
              sigmap = (uu___1530_62881.sigmap);
              iface = (uu___1530_62881.iface);
              admitted_iface = (uu___1530_62881.admitted_iface);
              expect_typ = (uu___1530_62881.expect_typ);
              docs = (uu___1530_62881.docs);
              remaining_iface_decls = (uu___1530_62881.remaining_iface_decls);
              syntax_only = (uu___1530_62881.syntax_only);
              ds_hooks = (uu___1530_62881.ds_hooks);
              dep_graph = (uu___1530_62881.dep_graph)
            }  in
          let uu____62885 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____62885 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____62902 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1538_62927 = env  in
      {
        curmodule = (uu___1538_62927.curmodule);
        curmonad = (uu___1538_62927.curmonad);
        modules = (uu___1538_62927.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1538_62927.exported_ids);
        trans_exported_ids = (uu___1538_62927.trans_exported_ids);
        includes = (uu___1538_62927.includes);
        sigaccum = (uu___1538_62927.sigaccum);
        sigmap = (uu___1538_62927.sigmap);
        iface = (uu___1538_62927.iface);
        admitted_iface = (uu___1538_62927.admitted_iface);
        expect_typ = (uu___1538_62927.expect_typ);
        docs = (uu___1538_62927.docs);
        remaining_iface_decls = (uu___1538_62927.remaining_iface_decls);
        syntax_only = (uu___1538_62927.syntax_only);
        ds_hooks = (uu___1538_62927.ds_hooks);
        dep_graph = (uu___1538_62927.dep_graph)
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
        let uu____62961 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____62961
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____62968 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____62968)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____63012) ->
                let uu____63020 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____63020 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____63025 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____63025
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____63034 =
            let uu____63040 =
              let uu____63042 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____63042 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____63040)  in
          let uu____63046 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____63034 uu____63046  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____63055 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____63068 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____63079 -> (false, true)
            | uu____63092 -> (false, false)  in
          match uu____63055 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____63106 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____63112 =
                       let uu____63114 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____63114  in
                     if uu____63112
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____63106 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____63122 ->
                   (extract_record env globals s;
                    (let uu___1579_63148 = env  in
                     {
                       curmodule = (uu___1579_63148.curmodule);
                       curmonad = (uu___1579_63148.curmonad);
                       modules = (uu___1579_63148.modules);
                       scope_mods = (uu___1579_63148.scope_mods);
                       exported_ids = (uu___1579_63148.exported_ids);
                       trans_exported_ids =
                         (uu___1579_63148.trans_exported_ids);
                       includes = (uu___1579_63148.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1579_63148.sigmap);
                       iface = (uu___1579_63148.iface);
                       admitted_iface = (uu___1579_63148.admitted_iface);
                       expect_typ = (uu___1579_63148.expect_typ);
                       docs = (uu___1579_63148.docs);
                       remaining_iface_decls =
                         (uu___1579_63148.remaining_iface_decls);
                       syntax_only = (uu___1579_63148.syntax_only);
                       ds_hooks = (uu___1579_63148.ds_hooks);
                       dep_graph = (uu___1579_63148.dep_graph)
                     })))
           in
        let env2 =
          let uu___1582_63150 = env1  in
          let uu____63151 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1582_63150.curmodule);
            curmonad = (uu___1582_63150.curmonad);
            modules = (uu___1582_63150.modules);
            scope_mods = uu____63151;
            exported_ids = (uu___1582_63150.exported_ids);
            trans_exported_ids = (uu___1582_63150.trans_exported_ids);
            includes = (uu___1582_63150.includes);
            sigaccum = (uu___1582_63150.sigaccum);
            sigmap = (uu___1582_63150.sigmap);
            iface = (uu___1582_63150.iface);
            admitted_iface = (uu___1582_63150.admitted_iface);
            expect_typ = (uu___1582_63150.expect_typ);
            docs = (uu___1582_63150.docs);
            remaining_iface_decls = (uu___1582_63150.remaining_iface_decls);
            syntax_only = (uu___1582_63150.syntax_only);
            ds_hooks = (uu___1582_63150.ds_hooks);
            dep_graph = (uu___1582_63150.dep_graph)
          }  in
        let uu____63199 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____63225) ->
              let uu____63234 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____63234)
          | uu____63261 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____63199 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____63320  ->
                     match uu____63320 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____63342 =
                                    let uu____63345 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____63345
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____63342);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____63440 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____63440.FStar_Ident.str  in
                                      ((let uu____63442 =
                                          get_exported_id_set env3 modul  in
                                        match uu____63442 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____63475 =
                                              let uu____63476 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____63476
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____63475
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
                let uu___1607_63577 = env3  in
                let uu____63578 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1607_63577.curmodule);
                  curmonad = (uu___1607_63577.curmonad);
                  modules = (uu___1607_63577.modules);
                  scope_mods = uu____63578;
                  exported_ids = (uu___1607_63577.exported_ids);
                  trans_exported_ids = (uu___1607_63577.trans_exported_ids);
                  includes = (uu___1607_63577.includes);
                  sigaccum = (uu___1607_63577.sigaccum);
                  sigmap = (uu___1607_63577.sigmap);
                  iface = (uu___1607_63577.iface);
                  admitted_iface = (uu___1607_63577.admitted_iface);
                  expect_typ = (uu___1607_63577.expect_typ);
                  docs = (uu___1607_63577.docs);
                  remaining_iface_decls =
                    (uu___1607_63577.remaining_iface_decls);
                  syntax_only = (uu___1607_63577.syntax_only);
                  ds_hooks = (uu___1607_63577.ds_hooks);
                  dep_graph = (uu___1607_63577.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____63661 =
        let uu____63666 = resolve_module_name env ns false  in
        match uu____63666 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____63681 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____63699  ->
                      match uu____63699 with
                      | (m,uu____63706) ->
                          let uu____63707 =
                            let uu____63709 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____63709 "."  in
                          let uu____63712 =
                            let uu____63714 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____63714 "."  in
                          FStar_Util.starts_with uu____63707 uu____63712))
               in
            if uu____63681
            then (ns, Open_namespace)
            else
              (let uu____63724 =
                 let uu____63730 =
                   let uu____63732 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____63732
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____63730)  in
               let uu____63736 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____63724 uu____63736)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____63661 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____63758 = resolve_module_name env ns false  in
      match uu____63758 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____63768 = current_module env1  in
              uu____63768.FStar_Ident.str  in
            (let uu____63770 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____63770 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____63794 =
                   let uu____63797 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____63797
                    in
                 FStar_ST.op_Colon_Equals incl uu____63794);
            (match () with
             | () ->
                 let uu____63890 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____63890 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____63910 =
                          let uu____64007 = get_exported_id_set env1 curmod
                             in
                          let uu____64054 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____64007, uu____64054)  in
                        match uu____63910 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____64470 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____64470  in
                              let ex = cur_exports k  in
                              (let uu____64645 =
                                 let uu____64649 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____64649 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____64645);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____64846 =
                                     let uu____64850 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____64850 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____64846)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____64983 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____65085 =
                        let uu____65091 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____65091)
                         in
                      let uu____65095 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____65085 uu____65095))))
      | uu____65096 ->
          let uu____65099 =
            let uu____65105 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____65105)  in
          let uu____65109 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____65099 uu____65109
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____65126 = module_is_defined env l  in
        if uu____65126
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____65133 =
             let uu____65139 =
               let uu____65141 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____65141  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____65139)  in
           let uu____65145 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____65133 uu____65145)
  
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
            ((let uu____65168 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____65168 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____65172 = FStar_Ident.range_of_lid l  in
                  let uu____65173 =
                    let uu____65179 =
                      let uu____65181 = FStar_Ident.string_of_lid l  in
                      let uu____65183 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____65185 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____65181 uu____65183 uu____65185
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____65179)  in
                  FStar_Errors.log_issue uu____65172 uu____65173);
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
                      let uu____65231 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____65231 ->
                      let uu____65236 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____65236 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____65251;
                              FStar_Syntax_Syntax.sigrng = uu____65252;
                              FStar_Syntax_Syntax.sigquals = uu____65253;
                              FStar_Syntax_Syntax.sigmeta = uu____65254;
                              FStar_Syntax_Syntax.sigattrs = uu____65255;_},uu____65256)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____65274;
                              FStar_Syntax_Syntax.sigrng = uu____65275;
                              FStar_Syntax_Syntax.sigquals = uu____65276;
                              FStar_Syntax_Syntax.sigmeta = uu____65277;
                              FStar_Syntax_Syntax.sigattrs = uu____65278;_},uu____65279)
                           -> lids
                       | uu____65307 ->
                           ((let uu____65316 =
                               let uu____65318 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____65318  in
                             if uu____65316
                             then
                               let uu____65321 = FStar_Ident.range_of_lid l
                                  in
                               let uu____65322 =
                                 let uu____65328 =
                                   let uu____65330 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____65330
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____65328)
                                  in
                               FStar_Errors.log_issue uu____65321 uu____65322
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1710_65347 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1710_65347.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1710_65347.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1710_65347.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1710_65347.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____65349 -> lids) [])
         in
      let uu___1715_65350 = m  in
      let uu____65351 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____65361,uu____65362) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1724_65365 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1724_65365.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1724_65365.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1724_65365.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1724_65365.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____65366 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1715_65350.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____65351;
        FStar_Syntax_Syntax.exports =
          (uu___1715_65350.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1715_65350.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____65390) ->
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
                                (lid,uu____65411,uu____65412,uu____65413,uu____65414,uu____65415)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____65431,uu____65432)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____65449 =
                                        let uu____65456 =
                                          let uu____65457 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____65458 =
                                            let uu____65465 =
                                              let uu____65466 =
                                                let uu____65481 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____65481)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____65466
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____65465
                                             in
                                          uu____65458
                                            FStar_Pervasives_Native.None
                                            uu____65457
                                           in
                                        (lid, univ_names, uu____65456)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____65449
                                       in
                                    let se2 =
                                      let uu___1756_65498 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1756_65498.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1756_65498.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1756_65498.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____65508 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____65512,uu____65513) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____65522,lbs),uu____65524)
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
                             let uu____65542 =
                               let uu____65544 =
                                 let uu____65545 =
                                   let uu____65548 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____65548.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____65545.FStar_Syntax_Syntax.v  in
                               uu____65544.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____65542))
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
                               let uu____65565 =
                                 let uu____65568 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____65568.FStar_Syntax_Syntax.fv_name  in
                               uu____65565.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1779_65573 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1779_65573.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1779_65573.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1779_65573.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____65583 -> ()));
      (let curmod =
         let uu____65586 = current_module env  in uu____65586.FStar_Ident.str
          in
       (let uu____65588 =
          let uu____65685 = get_exported_id_set env curmod  in
          let uu____65732 = get_trans_exported_id_set env curmod  in
          (uu____65685, uu____65732)  in
        match uu____65588 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____66151 = cur_ex eikind  in
                FStar_ST.op_Bang uu____66151  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____66341 =
                let uu____66345 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____66345  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____66341  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____66478 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1797_66576 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1797_66576.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1797_66576.exported_ids);
                    trans_exported_ids = (uu___1797_66576.trans_exported_ids);
                    includes = (uu___1797_66576.includes);
                    sigaccum = [];
                    sigmap = (uu___1797_66576.sigmap);
                    iface = (uu___1797_66576.iface);
                    admitted_iface = (uu___1797_66576.admitted_iface);
                    expect_typ = (uu___1797_66576.expect_typ);
                    docs = (uu___1797_66576.docs);
                    remaining_iface_decls =
                      (uu___1797_66576.remaining_iface_decls);
                    syntax_only = (uu___1797_66576.syntax_only);
                    ds_hooks = (uu___1797_66576.ds_hooks);
                    dep_graph = (uu___1797_66576.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____66614  ->
         push_record_cache ();
         (let uu____66617 =
            let uu____66620 = FStar_ST.op_Bang stack  in env :: uu____66620
             in
          FStar_ST.op_Colon_Equals stack uu____66617);
         (let uu___1803_66669 = env  in
          let uu____66670 = FStar_Util.smap_copy env.exported_ids  in
          let uu____66675 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____66680 = FStar_Util.smap_copy env.includes  in
          let uu____66691 = FStar_Util.smap_copy env.sigmap  in
          let uu____66704 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1803_66669.curmodule);
            curmonad = (uu___1803_66669.curmonad);
            modules = (uu___1803_66669.modules);
            scope_mods = (uu___1803_66669.scope_mods);
            exported_ids = uu____66670;
            trans_exported_ids = uu____66675;
            includes = uu____66680;
            sigaccum = (uu___1803_66669.sigaccum);
            sigmap = uu____66691;
            iface = (uu___1803_66669.iface);
            admitted_iface = (uu___1803_66669.admitted_iface);
            expect_typ = (uu___1803_66669.expect_typ);
            docs = uu____66704;
            remaining_iface_decls = (uu___1803_66669.remaining_iface_decls);
            syntax_only = (uu___1803_66669.syntax_only);
            ds_hooks = (uu___1803_66669.ds_hooks);
            dep_graph = (uu___1803_66669.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____66712  ->
    FStar_Util.atomically
      (fun uu____66719  ->
         let uu____66720 = FStar_ST.op_Bang stack  in
         match uu____66720 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____66775 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____66822 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____66826 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____66868 = FStar_Util.smap_try_find sm' k  in
              match uu____66868 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1838_66899 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1838_66899.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1838_66899.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1838_66899.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1838_66899.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____66900 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____66908 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____66935 = finish env modul1  in (uu____66935, modul1)
  
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
      let uu____67037 =
        let uu____67041 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____67041  in
      FStar_Util.set_elements uu____67037  in
    let fields =
      let uu____67157 =
        let uu____67161 = e Exported_id_field  in
        FStar_ST.op_Bang uu____67161  in
      FStar_Util.set_elements uu____67157  in
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
          let uu____67317 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____67317  in
        let fields =
          let uu____67331 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____67331  in
        (fun uu___450_67339  ->
           match uu___450_67339 with
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
  'Auu____67476 .
    'Auu____67476 Prims.list FStar_Pervasives_Native.option ->
      'Auu____67476 Prims.list FStar_ST.ref
  =
  fun uu___451_67489  ->
    match uu___451_67489 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____67532 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____67532 as_exported_ids  in
      let uu____67538 = as_ids_opt env.exported_ids  in
      let uu____67541 = as_ids_opt env.trans_exported_ids  in
      let uu____67544 =
        let uu____67549 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____67549 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____67538;
        mii_trans_exported_ids = uu____67541;
        mii_includes = uu____67544
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
                let uu____67671 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____67671 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___452_67693 =
                  match uu___452_67693 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____67705  ->
                     match uu____67705 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____67731 =
                    let uu____67736 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____67736, Open_namespace)  in
                  [uu____67731]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____67767 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____67767);
              (match () with
               | () ->
                   ((let uu____67794 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____67794);
                    (match () with
                     | () ->
                         ((let uu____67821 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____67821);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1908_67853 = env1  in
                                 let uu____67854 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1908_67853.curmonad);
                                   modules = (uu___1908_67853.modules);
                                   scope_mods = uu____67854;
                                   exported_ids =
                                     (uu___1908_67853.exported_ids);
                                   trans_exported_ids =
                                     (uu___1908_67853.trans_exported_ids);
                                   includes = (uu___1908_67853.includes);
                                   sigaccum = (uu___1908_67853.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1908_67853.expect_typ);
                                   docs = (uu___1908_67853.docs);
                                   remaining_iface_decls =
                                     (uu___1908_67853.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1908_67853.syntax_only);
                                   ds_hooks = (uu___1908_67853.ds_hooks);
                                   dep_graph = (uu___1908_67853.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____67866 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____67892  ->
                      match uu____67892 with
                      | (l,uu____67899) -> FStar_Ident.lid_equals l mname))
               in
            match uu____67866 with
            | FStar_Pervasives_Native.None  ->
                let uu____67909 = prep env  in (uu____67909, false)
            | FStar_Pervasives_Native.Some (uu____67912,m) ->
                ((let uu____67919 =
                    (let uu____67923 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____67923) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____67919
                  then
                    let uu____67926 =
                      let uu____67932 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____67932)
                       in
                    let uu____67936 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____67926 uu____67936
                  else ());
                 (let uu____67939 =
                    let uu____67940 = push env  in prep uu____67940  in
                  (uu____67939, true)))
  
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
          let uu___1929_67958 = env  in
          {
            curmodule = (uu___1929_67958.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1929_67958.modules);
            scope_mods = (uu___1929_67958.scope_mods);
            exported_ids = (uu___1929_67958.exported_ids);
            trans_exported_ids = (uu___1929_67958.trans_exported_ids);
            includes = (uu___1929_67958.includes);
            sigaccum = (uu___1929_67958.sigaccum);
            sigmap = (uu___1929_67958.sigmap);
            iface = (uu___1929_67958.iface);
            admitted_iface = (uu___1929_67958.admitted_iface);
            expect_typ = (uu___1929_67958.expect_typ);
            docs = (uu___1929_67958.docs);
            remaining_iface_decls = (uu___1929_67958.remaining_iface_decls);
            syntax_only = (uu___1929_67958.syntax_only);
            ds_hooks = (uu___1929_67958.ds_hooks);
            dep_graph = (uu___1929_67958.dep_graph)
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
        let uu____67993 = lookup1 lid  in
        match uu____67993 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____68008  ->
                   match uu____68008 with
                   | (lid1,uu____68015) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____68018 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____68018  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____68030 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____68031 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____68030 uu____68031  in
                 let uu____68032 = resolve_module_name env modul true  in
                 match uu____68032 with
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
            let uu____68053 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____68053
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____68083 = lookup1 id1  in
      match uu____68083 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  