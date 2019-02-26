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
    match projectee with | Open_module  -> true | uu____53529 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____53540 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____53760 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____53780 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____53800 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____53820 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____53840 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____53860 -> false
  
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
    | uu____53882 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____53893 -> false
  
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
    ds_push_open_hook = (fun uu____55513  -> fun uu____55514  -> ());
    ds_push_include_hook = (fun uu____55517  -> fun uu____55518  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____55522  -> fun uu____55523  -> fun uu____55524  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____55561 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____55603 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___549_55638 = env  in
      {
        curmodule = (uu___549_55638.curmodule);
        curmonad = (uu___549_55638.curmonad);
        modules = (uu___549_55638.modules);
        scope_mods = (uu___549_55638.scope_mods);
        exported_ids = (uu___549_55638.exported_ids);
        trans_exported_ids = (uu___549_55638.trans_exported_ids);
        includes = (uu___549_55638.includes);
        sigaccum = (uu___549_55638.sigaccum);
        sigmap = (uu___549_55638.sigmap);
        iface = b;
        admitted_iface = (uu___549_55638.admitted_iface);
        expect_typ = (uu___549_55638.expect_typ);
        docs = (uu___549_55638.docs);
        remaining_iface_decls = (uu___549_55638.remaining_iface_decls);
        syntax_only = (uu___549_55638.syntax_only);
        ds_hooks = (uu___549_55638.ds_hooks);
        dep_graph = (uu___549_55638.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___554_55659 = e  in
      {
        curmodule = (uu___554_55659.curmodule);
        curmonad = (uu___554_55659.curmonad);
        modules = (uu___554_55659.modules);
        scope_mods = (uu___554_55659.scope_mods);
        exported_ids = (uu___554_55659.exported_ids);
        trans_exported_ids = (uu___554_55659.trans_exported_ids);
        includes = (uu___554_55659.includes);
        sigaccum = (uu___554_55659.sigaccum);
        sigmap = (uu___554_55659.sigmap);
        iface = (uu___554_55659.iface);
        admitted_iface = b;
        expect_typ = (uu___554_55659.expect_typ);
        docs = (uu___554_55659.docs);
        remaining_iface_decls = (uu___554_55659.remaining_iface_decls);
        syntax_only = (uu___554_55659.syntax_only);
        ds_hooks = (uu___554_55659.ds_hooks);
        dep_graph = (uu___554_55659.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___559_55680 = e  in
      {
        curmodule = (uu___559_55680.curmodule);
        curmonad = (uu___559_55680.curmonad);
        modules = (uu___559_55680.modules);
        scope_mods = (uu___559_55680.scope_mods);
        exported_ids = (uu___559_55680.exported_ids);
        trans_exported_ids = (uu___559_55680.trans_exported_ids);
        includes = (uu___559_55680.includes);
        sigaccum = (uu___559_55680.sigaccum);
        sigmap = (uu___559_55680.sigmap);
        iface = (uu___559_55680.iface);
        admitted_iface = (uu___559_55680.admitted_iface);
        expect_typ = b;
        docs = (uu___559_55680.docs);
        remaining_iface_decls = (uu___559_55680.remaining_iface_decls);
        syntax_only = (uu___559_55680.syntax_only);
        ds_hooks = (uu___559_55680.ds_hooks);
        dep_graph = (uu___559_55680.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____55707 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____55707 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____55720 =
            let uu____55724 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____55724  in
          FStar_All.pipe_right uu____55720 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___420_55865  ->
         match uu___420_55865 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____55870 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___578_55882 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___578_55882.curmonad);
        modules = (uu___578_55882.modules);
        scope_mods = (uu___578_55882.scope_mods);
        exported_ids = (uu___578_55882.exported_ids);
        trans_exported_ids = (uu___578_55882.trans_exported_ids);
        includes = (uu___578_55882.includes);
        sigaccum = (uu___578_55882.sigaccum);
        sigmap = (uu___578_55882.sigmap);
        iface = (uu___578_55882.iface);
        admitted_iface = (uu___578_55882.admitted_iface);
        expect_typ = (uu___578_55882.expect_typ);
        docs = (uu___578_55882.docs);
        remaining_iface_decls = (uu___578_55882.remaining_iface_decls);
        syntax_only = (uu___578_55882.syntax_only);
        ds_hooks = (uu___578_55882.ds_hooks);
        dep_graph = (uu___578_55882.dep_graph)
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
      let uu____55906 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____55940  ->
                match uu____55940 with
                | (m,uu____55949) -> FStar_Ident.lid_equals l m))
         in
      match uu____55906 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____55966,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____56000 =
          FStar_List.partition
            (fun uu____56030  ->
               match uu____56030 with
               | (m,uu____56039) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____56000 with
        | (uu____56044,rest) ->
            let uu___603_56078 = env  in
            {
              curmodule = (uu___603_56078.curmodule);
              curmonad = (uu___603_56078.curmonad);
              modules = (uu___603_56078.modules);
              scope_mods = (uu___603_56078.scope_mods);
              exported_ids = (uu___603_56078.exported_ids);
              trans_exported_ids = (uu___603_56078.trans_exported_ids);
              includes = (uu___603_56078.includes);
              sigaccum = (uu___603_56078.sigaccum);
              sigmap = (uu___603_56078.sigmap);
              iface = (uu___603_56078.iface);
              admitted_iface = (uu___603_56078.admitted_iface);
              expect_typ = (uu___603_56078.expect_typ);
              docs = (uu___603_56078.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___603_56078.syntax_only);
              ds_hooks = (uu___603_56078.ds_hooks);
              dep_graph = (uu___603_56078.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____56107 = current_module env  in qual uu____56107 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____56109 =
            let uu____56110 = current_module env  in qual uu____56110 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____56109
            id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___613_56131 = env  in
      {
        curmodule = (uu___613_56131.curmodule);
        curmonad = (uu___613_56131.curmonad);
        modules = (uu___613_56131.modules);
        scope_mods = (uu___613_56131.scope_mods);
        exported_ids = (uu___613_56131.exported_ids);
        trans_exported_ids = (uu___613_56131.trans_exported_ids);
        includes = (uu___613_56131.includes);
        sigaccum = (uu___613_56131.sigaccum);
        sigmap = (uu___613_56131.sigmap);
        iface = (uu___613_56131.iface);
        admitted_iface = (uu___613_56131.admitted_iface);
        expect_typ = (uu___613_56131.expect_typ);
        docs = (uu___613_56131.docs);
        remaining_iface_decls = (uu___613_56131.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___613_56131.ds_hooks);
        dep_graph = (uu___613_56131.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___618_56149 = env  in
      {
        curmodule = (uu___618_56149.curmodule);
        curmonad = (uu___618_56149.curmonad);
        modules = (uu___618_56149.modules);
        scope_mods = (uu___618_56149.scope_mods);
        exported_ids = (uu___618_56149.exported_ids);
        trans_exported_ids = (uu___618_56149.trans_exported_ids);
        includes = (uu___618_56149.includes);
        sigaccum = (uu___618_56149.sigaccum);
        sigmap = (uu___618_56149.sigmap);
        iface = (uu___618_56149.iface);
        admitted_iface = (uu___618_56149.admitted_iface);
        expect_typ = (uu___618_56149.expect_typ);
        docs = (uu___618_56149.docs);
        remaining_iface_decls = (uu___618_56149.remaining_iface_decls);
        syntax_only = (uu___618_56149.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___618_56149.dep_graph)
      }
  
let new_sigmap : 'Auu____56155 . unit -> 'Auu____56155 FStar_Util.smap =
  fun uu____56162  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____56170 = new_sigmap ()  in
    let uu____56175 = new_sigmap ()  in
    let uu____56180 = new_sigmap ()  in
    let uu____56191 = new_sigmap ()  in
    let uu____56204 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____56170;
      trans_exported_ids = uu____56175;
      includes = uu____56180;
      sigaccum = [];
      sigmap = uu____56191;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____56204;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___625_56238 = env  in
      {
        curmodule = (uu___625_56238.curmodule);
        curmonad = (uu___625_56238.curmonad);
        modules = (uu___625_56238.modules);
        scope_mods = (uu___625_56238.scope_mods);
        exported_ids = (uu___625_56238.exported_ids);
        trans_exported_ids = (uu___625_56238.trans_exported_ids);
        includes = (uu___625_56238.includes);
        sigaccum = (uu___625_56238.sigaccum);
        sigmap = (uu___625_56238.sigmap);
        iface = (uu___625_56238.iface);
        admitted_iface = (uu___625_56238.admitted_iface);
        expect_typ = (uu___625_56238.expect_typ);
        docs = (uu___625_56238.docs);
        remaining_iface_decls = (uu___625_56238.remaining_iface_decls);
        syntax_only = (uu___625_56238.syntax_only);
        ds_hooks = (uu___625_56238.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____56266  ->
         match uu____56266 with
         | (m,uu____56273) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___634_56286 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___634_56286.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___637_56287 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index =
          (uu___637_56287.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___637_56287.FStar_Syntax_Syntax.sort)
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
      (fun uu____56390  ->
         match uu____56390 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____56421 =
                 let uu____56422 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____56422 dd dq  in
               FStar_Pervasives_Native.Some uu____56421
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____56462 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____56500 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____56521 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___421_56551  ->
      match uu___421_56551 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____56570 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____56570 cont_t) -> 'Auu____56570 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____56607 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____56607
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____56623  ->
                   match uu____56623 with
                   | (f,uu____56631) ->
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
  fun uu___422_56705  ->
    match uu___422_56705 with
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
              let rec aux uu___423_56781 =
                match uu___423_56781 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____56794 = get_exported_id_set env mname  in
                      match uu____56794 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____56821 = mex eikind  in
                            FStar_ST.op_Bang uu____56821  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____56936 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____56936 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____57013 = qual modul id1  in
                        find_in_module uu____57013
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____57018 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___424_57027  ->
    match uu___424_57027 with
    | Exported_id_field  -> true
    | uu____57030 -> false
  
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
                  let check_local_binding_id uu___425_57154 =
                    match uu___425_57154 with
                    | (id',uu____57157) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___426_57165 =
                    match uu___426_57165 with
                    | (id',uu____57168,uu____57169) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____57174 = current_module env  in
                    FStar_Ident.ids_of_lid uu____57174  in
                  let proc uu___427_57182 =
                    match uu___427_57182 with
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
                        let uu____57191 = FStar_Ident.lid_of_ids curmod_ns
                           in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____57191 id1
                    | uu____57196 -> Cont_ignore  in
                  let rec aux uu___428_57206 =
                    match uu___428_57206 with
                    | a::q ->
                        let uu____57215 = proc a  in
                        option_of_cont (fun uu____57219  -> aux q)
                          uu____57215
                    | [] ->
                        let uu____57220 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____57224  -> FStar_Pervasives_Native.None)
                          uu____57220
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____57232 .
    FStar_Range.range ->
      ('Auu____57232 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____57246  -> match uu____57246 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____57264 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____57264)
          -> 'Auu____57264 -> 'Auu____57264
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____57305 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____57305 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____57349 = unmangleOpName id1  in
      match uu____57349 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____57355 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____57361 =
                 found_local_binding id1.FStar_Ident.idRange r  in
               Cont_ok uu____57361) (fun uu____57363  -> Cont_fail)
            (fun uu____57365  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____57372  -> fun uu____57373  -> Cont_fail)
                 Cont_ignore)
            (fun uu____57381  -> fun uu____57382  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____57456 ->
                let lid = qualify env id1  in
                let uu____57458 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____57458 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____57486 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____57486
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____57510 = current_module env  in qual uu____57510 id1
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
        let rec aux uu___429_57582 =
          match uu___429_57582 with
          | [] ->
              let uu____57587 = module_is_defined env lid  in
              if uu____57587
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____57599 =
                  let uu____57600 = FStar_Ident.path_of_lid ns  in
                  let uu____57604 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____57600 uu____57604  in
                let uu____57609 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____57599 uu____57609  in
              let uu____57610 = module_is_defined env new_lid  in
              if uu____57610
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____57619 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____57629::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____57649 =
          let uu____57651 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____57651  in
        if uu____57649
        then
          let uu____57653 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____57653
           then ()
           else
             (let uu____57658 =
                let uu____57664 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____57664)
                 in
              let uu____57668 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____57658 uu____57668))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____57682 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____57686 = resolve_module_name env modul_orig true  in
          (match uu____57686 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____57691 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___430_57714  ->
             match uu___430_57714 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____57718 -> false) env.scope_mods
  
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
                 let uu____57847 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____57847
                   (FStar_Util.map_option
                      (fun uu____57897  ->
                         match uu____57897 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____57967 = aux ns_rev_prefix ns_last_id  in
              (match uu____57967 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____58030 =
            let uu____58033 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____58033 true  in
          match uu____58030 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____58048 -> do_shorten env ids
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
                  | uu____58169::uu____58170 ->
                      let uu____58173 =
                        let uu____58176 =
                          let uu____58177 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____58178 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____58177 uu____58178
                           in
                        resolve_module_name env uu____58176 true  in
                      (match uu____58173 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____58183 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____58187  ->
                                FStar_Pervasives_Native.None) uu____58183)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___431_58211  ->
      match uu___431_58211 with
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
              let uu____58332 = k_global_def lid1 def  in
              cont_of_option k uu____58332  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____58368 = k_local_binding l  in
                 cont_of_option Cont_fail uu____58368)
              (fun r  ->
                 let uu____58374 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____58374)
              (fun uu____58378  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____58389,uu____58390,uu____58391,l,uu____58393,uu____58394) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___432_58407  ->
               match uu___432_58407 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____58410,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____58422 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____58428,uu____58429,uu____58430) -> FStar_Pervasives_Native.None
    | uu____58431 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____58447 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____58455 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____58455
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____58447 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____58478 =
         let uu____58479 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____58479  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____58478) &&
        (let uu____58487 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____58487 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____58504 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___433_58511  ->
                     match uu___433_58511 with
                     | FStar_Syntax_Syntax.Projector uu____58513 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____58519 -> true
                     | uu____58521 -> false)))
           in
        if uu____58504
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____58526 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___434_58532  ->
                 match uu___434_58532 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____58535 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___435_58541  ->
                    match uu___435_58541 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____58544 -> false)))
             &&
             (let uu____58547 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___436_58553  ->
                        match uu___436_58553 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____58556 -> false))
                 in
              Prims.op_Negation uu____58547))
         in
      if uu____58526 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___439_58608 =
            match uu___439_58608 with
            | (uu____58616,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____58620) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____58625 ->
                     let uu____58642 =
                       let uu____58643 =
                         let uu____58650 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____58650, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58643  in
                     FStar_Pervasives_Native.Some uu____58642
                 | FStar_Syntax_Syntax.Sig_datacon uu____58653 ->
                     let uu____58669 =
                       let uu____58670 =
                         let uu____58677 =
                           let uu____58678 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____58678
                            in
                         (uu____58677, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58670  in
                     FStar_Pervasives_Native.Some uu____58669
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____58683,lbs),uu____58685) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____58697 =
                       let uu____58698 =
                         let uu____58705 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____58705, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58698  in
                     FStar_Pervasives_Native.Some uu____58697
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____58709,uu____58710) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____58714 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___437_58720  ->
                                  match uu___437_58720 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____58723 -> false)))
                        in
                     if uu____58714
                     then
                       let lid2 =
                         let uu____58729 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____58729  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____58731 =
                         FStar_Util.find_map quals
                           (fun uu___438_58736  ->
                              match uu___438_58736 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____58740 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____58731 with
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
                        | uu____58749 ->
                            let uu____58752 =
                              let uu____58753 =
                                let uu____58760 =
                                  let uu____58761 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____58761
                                   in
                                (uu____58760,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____58753  in
                            FStar_Pervasives_Native.Some uu____58752)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____58769 =
                       let uu____58770 =
                         let uu____58775 =
                           let uu____58776 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____58776
                            in
                         (se, uu____58775)  in
                       Eff_name uu____58770  in
                     FStar_Pervasives_Native.Some uu____58769
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____58778 =
                       let uu____58779 =
                         let uu____58784 =
                           let uu____58785 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____58785
                            in
                         (se, uu____58784)  in
                       Eff_name uu____58779  in
                     FStar_Pervasives_Native.Some uu____58778
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____58786 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____58805 =
                       let uu____58806 =
                         let uu____58813 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____58813, [])  in
                       Term_name uu____58806  in
                     FStar_Pervasives_Native.Some uu____58805
                 | uu____58817 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____58835 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____58835 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____58851 =
            match uu____58851 with
            | (id1,l,dd) ->
                let uu____58863 =
                  let uu____58864 =
                    let uu____58871 =
                      let uu____58872 =
                        let uu____58873 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____58873  in
                      FStar_Syntax_Syntax.fvar uu____58872 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____58871, [])  in
                  Term_name uu____58864  in
                FStar_Pervasives_Native.Some uu____58863
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____58881 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____58881 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____58889 -> FStar_Pervasives_Native.None)
            | uu____58892 -> FStar_Pervasives_Native.None  in
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
        let uu____58930 = try_lookup_name true exclude_interf env lid  in
        match uu____58930 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____58946 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____58966 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____58966 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____58981 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59007 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59007 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____59023;
             FStar_Syntax_Syntax.sigquals = uu____59024;
             FStar_Syntax_Syntax.sigmeta = uu____59025;
             FStar_Syntax_Syntax.sigattrs = uu____59026;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____59045;
             FStar_Syntax_Syntax.sigquals = uu____59046;
             FStar_Syntax_Syntax.sigmeta = uu____59047;
             FStar_Syntax_Syntax.sigattrs = uu____59048;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____59066,uu____59067,uu____59068,uu____59069,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____59071;
             FStar_Syntax_Syntax.sigquals = uu____59072;
             FStar_Syntax_Syntax.sigmeta = uu____59073;
             FStar_Syntax_Syntax.sigattrs = uu____59074;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____59096 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59122 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59122 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____59132;
             FStar_Syntax_Syntax.sigquals = uu____59133;
             FStar_Syntax_Syntax.sigmeta = uu____59134;
             FStar_Syntax_Syntax.sigattrs = uu____59135;_},uu____59136)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____59146;
             FStar_Syntax_Syntax.sigquals = uu____59147;
             FStar_Syntax_Syntax.sigmeta = uu____59148;
             FStar_Syntax_Syntax.sigattrs = uu____59149;_},uu____59150)
          -> FStar_Pervasives_Native.Some ne
      | uu____59159 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____59178 = try_lookup_effect_name env lid  in
      match uu____59178 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____59183 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59198 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59198 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____59208,uu____59209,uu____59210,uu____59211);
             FStar_Syntax_Syntax.sigrng = uu____59212;
             FStar_Syntax_Syntax.sigquals = uu____59213;
             FStar_Syntax_Syntax.sigmeta = uu____59214;
             FStar_Syntax_Syntax.sigattrs = uu____59215;_},uu____59216)
          ->
          let rec aux new_name =
            let uu____59237 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____59237 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____59258) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____59269 =
                       let uu____59270 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____59270
                        in
                     FStar_Pervasives_Native.Some uu____59269
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____59272 =
                       let uu____59273 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____59273
                        in
                     FStar_Pervasives_Native.Some uu____59272
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____59274,uu____59275,uu____59276,cmp,uu____59278) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____59284 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____59285,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____59291 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___440_59330 =
        match uu___440_59330 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____59340,uu____59341,uu____59342);
             FStar_Syntax_Syntax.sigrng = uu____59343;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____59345;
             FStar_Syntax_Syntax.sigattrs = uu____59346;_},uu____59347)
            -> FStar_Pervasives_Native.Some quals
        | uu____59356 -> FStar_Pervasives_Native.None  in
      let uu____59364 =
        resolve_in_open_namespaces' env lid
          (fun uu____59372  -> FStar_Pervasives_Native.None)
          (fun uu____59376  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____59364 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____59386 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____59404 =
        FStar_List.tryFind
          (fun uu____59419  ->
             match uu____59419 with
             | (mlid,modul) ->
                 let uu____59427 = FStar_Ident.path_of_lid mlid  in
                 uu____59427 = path) env.modules
         in
      match uu____59404 with
      | FStar_Pervasives_Native.Some (uu____59430,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___441_59470 =
        match uu___441_59470 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____59478,lbs),uu____59480);
             FStar_Syntax_Syntax.sigrng = uu____59481;
             FStar_Syntax_Syntax.sigquals = uu____59482;
             FStar_Syntax_Syntax.sigmeta = uu____59483;
             FStar_Syntax_Syntax.sigattrs = uu____59484;_},uu____59485)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____59503 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____59503
        | uu____59504 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____59511  -> FStar_Pervasives_Native.None)
        (fun uu____59513  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___442_59546 =
        match uu___442_59546 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____59557);
             FStar_Syntax_Syntax.sigrng = uu____59558;
             FStar_Syntax_Syntax.sigquals = uu____59559;
             FStar_Syntax_Syntax.sigmeta = uu____59560;
             FStar_Syntax_Syntax.sigattrs = uu____59561;_},uu____59562)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____59588 -> FStar_Pervasives_Native.None)
        | uu____59595 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____59606  -> FStar_Pervasives_Native.None)
        (fun uu____59610  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____59670 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____59670 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____59695 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____59733) ->
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
      let uu____59791 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____59791 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59823 = try_lookup_lid env l  in
      match uu____59823 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____59829 =
            let uu____59830 = FStar_Syntax_Subst.compress e  in
            uu____59830.FStar_Syntax_Syntax.n  in
          (match uu____59829 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____59836 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____59848 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____59848 with
      | (uu____59858,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____59879 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____59883 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____59883 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____59888 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___1304_59919 = env  in
        {
          curmodule = (uu___1304_59919.curmodule);
          curmonad = (uu___1304_59919.curmonad);
          modules = (uu___1304_59919.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___1304_59919.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___1304_59919.sigaccum);
          sigmap = (uu___1304_59919.sigmap);
          iface = (uu___1304_59919.iface);
          admitted_iface = (uu___1304_59919.admitted_iface);
          expect_typ = (uu___1304_59919.expect_typ);
          docs = (uu___1304_59919.docs);
          remaining_iface_decls = (uu___1304_59919.remaining_iface_decls);
          syntax_only = (uu___1304_59919.syntax_only);
          ds_hooks = (uu___1304_59919.ds_hooks);
          dep_graph = (uu___1304_59919.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59935 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____59935 drop_attributes
  
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
               (uu____60005,uu____60006,uu____60007);
             FStar_Syntax_Syntax.sigrng = uu____60008;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____60010;
             FStar_Syntax_Syntax.sigattrs = uu____60011;_},uu____60012)
            ->
            let uu____60019 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___443_60025  ->
                      match uu___443_60025 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____60028 -> false))
               in
            if uu____60019
            then
              let uu____60033 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____60033
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____60036;
             FStar_Syntax_Syntax.sigrng = uu____60037;
             FStar_Syntax_Syntax.sigquals = uu____60038;
             FStar_Syntax_Syntax.sigmeta = uu____60039;
             FStar_Syntax_Syntax.sigattrs = uu____60040;_},uu____60041)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____60067 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____60067
        | uu____60068 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____60075  -> FStar_Pervasives_Native.None)
        (fun uu____60077  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___444_60112 =
        match uu___444_60112 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____60122,uu____60123,uu____60124,uu____60125,datas,uu____60127);
             FStar_Syntax_Syntax.sigrng = uu____60128;
             FStar_Syntax_Syntax.sigquals = uu____60129;
             FStar_Syntax_Syntax.sigmeta = uu____60130;
             FStar_Syntax_Syntax.sigattrs = uu____60131;_},uu____60132)
            -> FStar_Pervasives_Native.Some datas
        | uu____60149 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____60160  -> FStar_Pervasives_Native.None)
        (fun uu____60164  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____60243 =
    let uu____60244 =
      let uu____60249 =
        let uu____60252 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____60252  in
      let uu____60308 = FStar_ST.op_Bang record_cache  in uu____60249 ::
        uu____60308
       in
    FStar_ST.op_Colon_Equals record_cache uu____60244  in
  let pop1 uu____60418 =
    let uu____60419 =
      let uu____60424 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____60424  in
    FStar_ST.op_Colon_Equals record_cache uu____60419  in
  let snapshot1 uu____60539 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____60607 =
    let uu____60608 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____60608  in
  let insert r =
    let uu____60670 =
      let uu____60675 = let uu____60678 = peek1 ()  in r :: uu____60678  in
      let uu____60681 =
        let uu____60686 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____60686  in
      uu____60675 :: uu____60681  in
    FStar_ST.op_Colon_Equals record_cache uu____60670  in
  let filter1 uu____60798 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____60807 =
      let uu____60812 =
        let uu____60817 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____60817  in
      filtered :: uu____60812  in
    FStar_ST.op_Colon_Equals record_cache uu____60807  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____61809) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___445_61828  ->
                   match uu___445_61828 with
                   | FStar_Syntax_Syntax.RecordType uu____61830 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____61840 ->
                       true
                   | uu____61850 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___446_61875  ->
                      match uu___446_61875 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____61878,uu____61879,uu____61880,uu____61881,uu____61882);
                          FStar_Syntax_Syntax.sigrng = uu____61883;
                          FStar_Syntax_Syntax.sigquals = uu____61884;
                          FStar_Syntax_Syntax.sigmeta = uu____61885;
                          FStar_Syntax_Syntax.sigattrs = uu____61886;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____61897 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___447_61933  ->
                    match uu___447_61933 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____61937,uu____61938,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____61940;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____61942;
                        FStar_Syntax_Syntax.sigattrs = uu____61943;_} ->
                        let uu____61954 =
                          let uu____61955 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____61955  in
                        (match uu____61954 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____61961,t,uu____61963,uu____61964,uu____61965);
                             FStar_Syntax_Syntax.sigrng = uu____61966;
                             FStar_Syntax_Syntax.sigquals = uu____61967;
                             FStar_Syntax_Syntax.sigmeta = uu____61968;
                             FStar_Syntax_Syntax.sigattrs = uu____61969;_} ->
                             let uu____61980 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____61980 with
                              | (formals,uu____61996) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____62050  ->
                                            match uu____62050 with
                                            | (x,q) ->
                                                let uu____62063 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____62063
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____62118  ->
                                            match uu____62118 with
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
                                  ((let uu____62142 =
                                      let uu____62145 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____62145
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____62142);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____62248 =
                                            match uu____62248 with
                                            | (id1,uu____62254) ->
                                                let modul =
                                                  let uu____62257 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____62257.FStar_Ident.str
                                                   in
                                                let uu____62258 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____62258 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____62292 =
                                                         let uu____62293 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____62293
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____62292);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____62382
                                                               =
                                                               let uu____62383
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____62383.FStar_Ident.ident
                                                                in
                                                             uu____62382.FStar_Ident.idText
                                                              in
                                                           let uu____62385 =
                                                             let uu____62386
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____62386
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____62385))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____62482 -> ())
                    | uu____62483 -> ()))
        | uu____62484 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____62506 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____62506 with
        | (ns,id1) ->
            let uu____62523 = peek_record_cache ()  in
            FStar_Util.find_map uu____62523
              (fun record  ->
                 let uu____62529 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____62535  -> FStar_Pervasives_Native.None)
                   uu____62529)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____62537  -> Cont_ignore) (fun uu____62539  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____62545 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____62545)
        (fun k  -> fun uu____62551  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____62567 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____62567 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____62573 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____62593 = try_lookup_record_by_field_name env lid  in
        match uu____62593 with
        | FStar_Pervasives_Native.Some record' when
            let uu____62598 =
              let uu____62600 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____62600  in
            let uu____62601 =
              let uu____62603 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____62603  in
            uu____62598 = uu____62601 ->
            let uu____62605 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____62609  -> Cont_ok ())
               in
            (match uu____62605 with
             | Cont_ok uu____62611 -> true
             | uu____62613 -> false)
        | uu____62617 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____62639 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____62639 with
      | FStar_Pervasives_Native.Some r ->
          let uu____62650 =
            let uu____62656 =
              let uu____62657 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____62658 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____62657 uu____62658  in
            (uu____62656, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____62650
      | uu____62665 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____62694  ->
    let uu____62695 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____62695
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____62727  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___448_62740  ->
      match uu___448_62740 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___449_62800 =
            match uu___449_62800 with
            | Rec_binding uu____62802 -> true
            | uu____62804 -> false  in
          let this_env =
            let uu___1530_62807 = env  in
            let uu____62808 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1530_62807.curmodule);
              curmonad = (uu___1530_62807.curmonad);
              modules = (uu___1530_62807.modules);
              scope_mods = uu____62808;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1530_62807.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1530_62807.sigaccum);
              sigmap = (uu___1530_62807.sigmap);
              iface = (uu___1530_62807.iface);
              admitted_iface = (uu___1530_62807.admitted_iface);
              expect_typ = (uu___1530_62807.expect_typ);
              docs = (uu___1530_62807.docs);
              remaining_iface_decls = (uu___1530_62807.remaining_iface_decls);
              syntax_only = (uu___1530_62807.syntax_only);
              ds_hooks = (uu___1530_62807.ds_hooks);
              dep_graph = (uu___1530_62807.dep_graph)
            }  in
          let uu____62811 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____62811 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____62828 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1538_62853 = env  in
      {
        curmodule = (uu___1538_62853.curmodule);
        curmonad = (uu___1538_62853.curmonad);
        modules = (uu___1538_62853.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1538_62853.exported_ids);
        trans_exported_ids = (uu___1538_62853.trans_exported_ids);
        includes = (uu___1538_62853.includes);
        sigaccum = (uu___1538_62853.sigaccum);
        sigmap = (uu___1538_62853.sigmap);
        iface = (uu___1538_62853.iface);
        admitted_iface = (uu___1538_62853.admitted_iface);
        expect_typ = (uu___1538_62853.expect_typ);
        docs = (uu___1538_62853.docs);
        remaining_iface_decls = (uu___1538_62853.remaining_iface_decls);
        syntax_only = (uu___1538_62853.syntax_only);
        ds_hooks = (uu___1538_62853.ds_hooks);
        dep_graph = (uu___1538_62853.dep_graph)
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
        let uu____62887 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____62887
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____62894 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____62894)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____62938) ->
                let uu____62946 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____62946 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____62951 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____62951
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____62960 =
            let uu____62966 =
              let uu____62968 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____62968 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____62966)  in
          let uu____62972 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____62960 uu____62972  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____62981 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____62994 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____63005 -> (false, true)
            | uu____63018 -> (false, false)  in
          match uu____62981 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____63032 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____63038 =
                       let uu____63040 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____63040  in
                     if uu____63038
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____63032 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____63048 ->
                   (extract_record env globals s;
                    (let uu___1579_63074 = env  in
                     {
                       curmodule = (uu___1579_63074.curmodule);
                       curmonad = (uu___1579_63074.curmonad);
                       modules = (uu___1579_63074.modules);
                       scope_mods = (uu___1579_63074.scope_mods);
                       exported_ids = (uu___1579_63074.exported_ids);
                       trans_exported_ids =
                         (uu___1579_63074.trans_exported_ids);
                       includes = (uu___1579_63074.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1579_63074.sigmap);
                       iface = (uu___1579_63074.iface);
                       admitted_iface = (uu___1579_63074.admitted_iface);
                       expect_typ = (uu___1579_63074.expect_typ);
                       docs = (uu___1579_63074.docs);
                       remaining_iface_decls =
                         (uu___1579_63074.remaining_iface_decls);
                       syntax_only = (uu___1579_63074.syntax_only);
                       ds_hooks = (uu___1579_63074.ds_hooks);
                       dep_graph = (uu___1579_63074.dep_graph)
                     })))
           in
        let env2 =
          let uu___1582_63076 = env1  in
          let uu____63077 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1582_63076.curmodule);
            curmonad = (uu___1582_63076.curmonad);
            modules = (uu___1582_63076.modules);
            scope_mods = uu____63077;
            exported_ids = (uu___1582_63076.exported_ids);
            trans_exported_ids = (uu___1582_63076.trans_exported_ids);
            includes = (uu___1582_63076.includes);
            sigaccum = (uu___1582_63076.sigaccum);
            sigmap = (uu___1582_63076.sigmap);
            iface = (uu___1582_63076.iface);
            admitted_iface = (uu___1582_63076.admitted_iface);
            expect_typ = (uu___1582_63076.expect_typ);
            docs = (uu___1582_63076.docs);
            remaining_iface_decls = (uu___1582_63076.remaining_iface_decls);
            syntax_only = (uu___1582_63076.syntax_only);
            ds_hooks = (uu___1582_63076.ds_hooks);
            dep_graph = (uu___1582_63076.dep_graph)
          }  in
        let uu____63125 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____63151) ->
              let uu____63160 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____63160)
          | uu____63187 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____63125 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____63246  ->
                     match uu____63246 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____63268 =
                                    let uu____63271 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____63271
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____63268);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____63366 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____63366.FStar_Ident.str  in
                                      ((let uu____63368 =
                                          get_exported_id_set env3 modul  in
                                        match uu____63368 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____63401 =
                                              let uu____63402 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____63402
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____63401
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
                let uu___1607_63503 = env3  in
                let uu____63504 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1607_63503.curmodule);
                  curmonad = (uu___1607_63503.curmonad);
                  modules = (uu___1607_63503.modules);
                  scope_mods = uu____63504;
                  exported_ids = (uu___1607_63503.exported_ids);
                  trans_exported_ids = (uu___1607_63503.trans_exported_ids);
                  includes = (uu___1607_63503.includes);
                  sigaccum = (uu___1607_63503.sigaccum);
                  sigmap = (uu___1607_63503.sigmap);
                  iface = (uu___1607_63503.iface);
                  admitted_iface = (uu___1607_63503.admitted_iface);
                  expect_typ = (uu___1607_63503.expect_typ);
                  docs = (uu___1607_63503.docs);
                  remaining_iface_decls =
                    (uu___1607_63503.remaining_iface_decls);
                  syntax_only = (uu___1607_63503.syntax_only);
                  ds_hooks = (uu___1607_63503.ds_hooks);
                  dep_graph = (uu___1607_63503.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____63587 =
        let uu____63592 = resolve_module_name env ns false  in
        match uu____63592 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____63607 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____63625  ->
                      match uu____63625 with
                      | (m,uu____63632) ->
                          let uu____63633 =
                            let uu____63635 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____63635 "."  in
                          let uu____63638 =
                            let uu____63640 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____63640 "."  in
                          FStar_Util.starts_with uu____63633 uu____63638))
               in
            if uu____63607
            then (ns, Open_namespace)
            else
              (let uu____63650 =
                 let uu____63656 =
                   let uu____63658 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____63658
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____63656)  in
               let uu____63662 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____63650 uu____63662)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____63587 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____63684 = resolve_module_name env ns false  in
      match uu____63684 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____63694 = current_module env1  in
              uu____63694.FStar_Ident.str  in
            (let uu____63696 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____63696 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____63720 =
                   let uu____63723 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____63723
                    in
                 FStar_ST.op_Colon_Equals incl uu____63720);
            (match () with
             | () ->
                 let uu____63816 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____63816 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____63836 =
                          let uu____63933 = get_exported_id_set env1 curmod
                             in
                          let uu____63980 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____63933, uu____63980)  in
                        match uu____63836 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____64396 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____64396  in
                              let ex = cur_exports k  in
                              (let uu____64571 =
                                 let uu____64575 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____64575 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____64571);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____64772 =
                                     let uu____64776 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____64776 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____64772)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____64909 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____65011 =
                        let uu____65017 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____65017)
                         in
                      let uu____65021 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____65011 uu____65021))))
      | uu____65022 ->
          let uu____65025 =
            let uu____65031 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____65031)  in
          let uu____65035 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____65025 uu____65035
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____65052 = module_is_defined env l  in
        if uu____65052
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____65059 =
             let uu____65065 =
               let uu____65067 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____65067  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____65065)  in
           let uu____65071 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____65059 uu____65071)
  
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
            ((let uu____65094 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____65094 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____65098 = FStar_Ident.range_of_lid l  in
                  let uu____65099 =
                    let uu____65105 =
                      let uu____65107 = FStar_Ident.string_of_lid l  in
                      let uu____65109 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____65111 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____65107 uu____65109 uu____65111
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____65105)  in
                  FStar_Errors.log_issue uu____65098 uu____65099);
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
                      let uu____65157 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____65157 ->
                      let uu____65162 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____65162 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____65177;
                              FStar_Syntax_Syntax.sigrng = uu____65178;
                              FStar_Syntax_Syntax.sigquals = uu____65179;
                              FStar_Syntax_Syntax.sigmeta = uu____65180;
                              FStar_Syntax_Syntax.sigattrs = uu____65181;_},uu____65182)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____65200;
                              FStar_Syntax_Syntax.sigrng = uu____65201;
                              FStar_Syntax_Syntax.sigquals = uu____65202;
                              FStar_Syntax_Syntax.sigmeta = uu____65203;
                              FStar_Syntax_Syntax.sigattrs = uu____65204;_},uu____65205)
                           -> lids
                       | uu____65233 ->
                           ((let uu____65242 =
                               let uu____65244 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____65244  in
                             if uu____65242
                             then
                               let uu____65247 = FStar_Ident.range_of_lid l
                                  in
                               let uu____65248 =
                                 let uu____65254 =
                                   let uu____65256 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____65256
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____65254)
                                  in
                               FStar_Errors.log_issue uu____65247 uu____65248
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1710_65273 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1710_65273.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1710_65273.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1710_65273.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1710_65273.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____65275 -> lids) [])
         in
      let uu___1715_65276 = m  in
      let uu____65277 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____65287,uu____65288) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1724_65291 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1724_65291.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1724_65291.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1724_65291.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1724_65291.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____65292 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1715_65276.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____65277;
        FStar_Syntax_Syntax.exports =
          (uu___1715_65276.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1715_65276.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____65316) ->
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
                                (lid,uu____65337,uu____65338,uu____65339,uu____65340,uu____65341)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____65357,uu____65358)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____65375 =
                                        let uu____65382 =
                                          let uu____65383 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____65384 =
                                            let uu____65391 =
                                              let uu____65392 =
                                                let uu____65407 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____65407)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____65392
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____65391
                                             in
                                          uu____65384
                                            FStar_Pervasives_Native.None
                                            uu____65383
                                           in
                                        (lid, univ_names, uu____65382)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____65375
                                       in
                                    let se2 =
                                      let uu___1756_65424 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1756_65424.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1756_65424.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1756_65424.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____65434 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____65438,uu____65439) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____65448,lbs),uu____65450)
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
                             let uu____65468 =
                               let uu____65470 =
                                 let uu____65471 =
                                   let uu____65474 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____65474.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____65471.FStar_Syntax_Syntax.v  in
                               uu____65470.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____65468))
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
                               let uu____65491 =
                                 let uu____65494 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____65494.FStar_Syntax_Syntax.fv_name  in
                               uu____65491.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1779_65499 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1779_65499.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1779_65499.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1779_65499.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____65509 -> ()));
      (let curmod =
         let uu____65512 = current_module env  in uu____65512.FStar_Ident.str
          in
       (let uu____65514 =
          let uu____65611 = get_exported_id_set env curmod  in
          let uu____65658 = get_trans_exported_id_set env curmod  in
          (uu____65611, uu____65658)  in
        match uu____65514 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____66077 = cur_ex eikind  in
                FStar_ST.op_Bang uu____66077  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____66267 =
                let uu____66271 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____66271  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____66267  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____66404 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1797_66502 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1797_66502.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1797_66502.exported_ids);
                    trans_exported_ids = (uu___1797_66502.trans_exported_ids);
                    includes = (uu___1797_66502.includes);
                    sigaccum = [];
                    sigmap = (uu___1797_66502.sigmap);
                    iface = (uu___1797_66502.iface);
                    admitted_iface = (uu___1797_66502.admitted_iface);
                    expect_typ = (uu___1797_66502.expect_typ);
                    docs = (uu___1797_66502.docs);
                    remaining_iface_decls =
                      (uu___1797_66502.remaining_iface_decls);
                    syntax_only = (uu___1797_66502.syntax_only);
                    ds_hooks = (uu___1797_66502.ds_hooks);
                    dep_graph = (uu___1797_66502.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____66540  ->
         push_record_cache ();
         (let uu____66543 =
            let uu____66546 = FStar_ST.op_Bang stack  in env :: uu____66546
             in
          FStar_ST.op_Colon_Equals stack uu____66543);
         (let uu___1803_66595 = env  in
          let uu____66596 = FStar_Util.smap_copy env.exported_ids  in
          let uu____66601 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____66606 = FStar_Util.smap_copy env.includes  in
          let uu____66617 = FStar_Util.smap_copy env.sigmap  in
          let uu____66630 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1803_66595.curmodule);
            curmonad = (uu___1803_66595.curmonad);
            modules = (uu___1803_66595.modules);
            scope_mods = (uu___1803_66595.scope_mods);
            exported_ids = uu____66596;
            trans_exported_ids = uu____66601;
            includes = uu____66606;
            sigaccum = (uu___1803_66595.sigaccum);
            sigmap = uu____66617;
            iface = (uu___1803_66595.iface);
            admitted_iface = (uu___1803_66595.admitted_iface);
            expect_typ = (uu___1803_66595.expect_typ);
            docs = uu____66630;
            remaining_iface_decls = (uu___1803_66595.remaining_iface_decls);
            syntax_only = (uu___1803_66595.syntax_only);
            ds_hooks = (uu___1803_66595.ds_hooks);
            dep_graph = (uu___1803_66595.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____66638  ->
    FStar_Util.atomically
      (fun uu____66645  ->
         let uu____66646 = FStar_ST.op_Bang stack  in
         match uu____66646 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____66701 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____66748 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____66752 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____66794 = FStar_Util.smap_try_find sm' k  in
              match uu____66794 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1838_66825 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1838_66825.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1838_66825.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1838_66825.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1838_66825.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____66826 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____66834 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____66861 = finish env modul1  in (uu____66861, modul1)
  
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
      let uu____66963 =
        let uu____66967 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____66967  in
      FStar_Util.set_elements uu____66963  in
    let fields =
      let uu____67083 =
        let uu____67087 = e Exported_id_field  in
        FStar_ST.op_Bang uu____67087  in
      FStar_Util.set_elements uu____67083  in
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
          let uu____67243 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____67243  in
        let fields =
          let uu____67257 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____67257  in
        (fun uu___450_67265  ->
           match uu___450_67265 with
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
  'Auu____67402 .
    'Auu____67402 Prims.list FStar_Pervasives_Native.option ->
      'Auu____67402 Prims.list FStar_ST.ref
  =
  fun uu___451_67415  ->
    match uu___451_67415 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____67458 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____67458 as_exported_ids  in
      let uu____67464 = as_ids_opt env.exported_ids  in
      let uu____67467 = as_ids_opt env.trans_exported_ids  in
      let uu____67470 =
        let uu____67475 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____67475 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____67464;
        mii_trans_exported_ids = uu____67467;
        mii_includes = uu____67470
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
                let uu____67597 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____67597 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___452_67619 =
                  match uu___452_67619 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____67631  ->
                     match uu____67631 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____67657 =
                    let uu____67662 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____67662, Open_namespace)  in
                  [uu____67657]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____67693 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____67693);
              (match () with
               | () ->
                   ((let uu____67720 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____67720);
                    (match () with
                     | () ->
                         ((let uu____67747 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____67747);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1908_67779 = env1  in
                                 let uu____67780 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1908_67779.curmonad);
                                   modules = (uu___1908_67779.modules);
                                   scope_mods = uu____67780;
                                   exported_ids =
                                     (uu___1908_67779.exported_ids);
                                   trans_exported_ids =
                                     (uu___1908_67779.trans_exported_ids);
                                   includes = (uu___1908_67779.includes);
                                   sigaccum = (uu___1908_67779.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1908_67779.expect_typ);
                                   docs = (uu___1908_67779.docs);
                                   remaining_iface_decls =
                                     (uu___1908_67779.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1908_67779.syntax_only);
                                   ds_hooks = (uu___1908_67779.ds_hooks);
                                   dep_graph = (uu___1908_67779.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____67792 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____67818  ->
                      match uu____67818 with
                      | (l,uu____67825) -> FStar_Ident.lid_equals l mname))
               in
            match uu____67792 with
            | FStar_Pervasives_Native.None  ->
                let uu____67835 = prep env  in (uu____67835, false)
            | FStar_Pervasives_Native.Some (uu____67838,m) ->
                ((let uu____67845 =
                    (let uu____67849 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____67849) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____67845
                  then
                    let uu____67852 =
                      let uu____67858 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____67858)
                       in
                    let uu____67862 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____67852 uu____67862
                  else ());
                 (let uu____67865 =
                    let uu____67866 = push env  in prep uu____67866  in
                  (uu____67865, true)))
  
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
          let uu___1929_67884 = env  in
          {
            curmodule = (uu___1929_67884.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1929_67884.modules);
            scope_mods = (uu___1929_67884.scope_mods);
            exported_ids = (uu___1929_67884.exported_ids);
            trans_exported_ids = (uu___1929_67884.trans_exported_ids);
            includes = (uu___1929_67884.includes);
            sigaccum = (uu___1929_67884.sigaccum);
            sigmap = (uu___1929_67884.sigmap);
            iface = (uu___1929_67884.iface);
            admitted_iface = (uu___1929_67884.admitted_iface);
            expect_typ = (uu___1929_67884.expect_typ);
            docs = (uu___1929_67884.docs);
            remaining_iface_decls = (uu___1929_67884.remaining_iface_decls);
            syntax_only = (uu___1929_67884.syntax_only);
            ds_hooks = (uu___1929_67884.ds_hooks);
            dep_graph = (uu___1929_67884.dep_graph)
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
        let uu____67919 = lookup1 lid  in
        match uu____67919 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____67934  ->
                   match uu____67934 with
                   | (lid1,uu____67941) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____67944 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____67944  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____67956 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____67957 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____67956 uu____67957  in
                 let uu____67958 = resolve_module_name env modul true  in
                 match uu____67958 with
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
            let uu____67979 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____67979
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____68009 = lookup1 id1  in
      match uu____68009 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  