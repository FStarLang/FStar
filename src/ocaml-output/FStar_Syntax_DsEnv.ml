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
    match projectee with | Open_module  -> true | uu____53612 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____53623 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____53843 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____53863 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____53883 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____53903 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____53923 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____53943 -> false
  
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
    | uu____53965 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____53976 -> false
  
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
    ds_push_open_hook = (fun uu____55596  -> fun uu____55597  -> ());
    ds_push_include_hook = (fun uu____55600  -> fun uu____55601  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____55605  -> fun uu____55606  -> fun uu____55607  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____55644 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____55686 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___549_55721 = env  in
      {
        curmodule = (uu___549_55721.curmodule);
        curmonad = (uu___549_55721.curmonad);
        modules = (uu___549_55721.modules);
        scope_mods = (uu___549_55721.scope_mods);
        exported_ids = (uu___549_55721.exported_ids);
        trans_exported_ids = (uu___549_55721.trans_exported_ids);
        includes = (uu___549_55721.includes);
        sigaccum = (uu___549_55721.sigaccum);
        sigmap = (uu___549_55721.sigmap);
        iface = b;
        admitted_iface = (uu___549_55721.admitted_iface);
        expect_typ = (uu___549_55721.expect_typ);
        docs = (uu___549_55721.docs);
        remaining_iface_decls = (uu___549_55721.remaining_iface_decls);
        syntax_only = (uu___549_55721.syntax_only);
        ds_hooks = (uu___549_55721.ds_hooks);
        dep_graph = (uu___549_55721.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___554_55742 = e  in
      {
        curmodule = (uu___554_55742.curmodule);
        curmonad = (uu___554_55742.curmonad);
        modules = (uu___554_55742.modules);
        scope_mods = (uu___554_55742.scope_mods);
        exported_ids = (uu___554_55742.exported_ids);
        trans_exported_ids = (uu___554_55742.trans_exported_ids);
        includes = (uu___554_55742.includes);
        sigaccum = (uu___554_55742.sigaccum);
        sigmap = (uu___554_55742.sigmap);
        iface = (uu___554_55742.iface);
        admitted_iface = b;
        expect_typ = (uu___554_55742.expect_typ);
        docs = (uu___554_55742.docs);
        remaining_iface_decls = (uu___554_55742.remaining_iface_decls);
        syntax_only = (uu___554_55742.syntax_only);
        ds_hooks = (uu___554_55742.ds_hooks);
        dep_graph = (uu___554_55742.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___559_55763 = e  in
      {
        curmodule = (uu___559_55763.curmodule);
        curmonad = (uu___559_55763.curmonad);
        modules = (uu___559_55763.modules);
        scope_mods = (uu___559_55763.scope_mods);
        exported_ids = (uu___559_55763.exported_ids);
        trans_exported_ids = (uu___559_55763.trans_exported_ids);
        includes = (uu___559_55763.includes);
        sigaccum = (uu___559_55763.sigaccum);
        sigmap = (uu___559_55763.sigmap);
        iface = (uu___559_55763.iface);
        admitted_iface = (uu___559_55763.admitted_iface);
        expect_typ = b;
        docs = (uu___559_55763.docs);
        remaining_iface_decls = (uu___559_55763.remaining_iface_decls);
        syntax_only = (uu___559_55763.syntax_only);
        ds_hooks = (uu___559_55763.ds_hooks);
        dep_graph = (uu___559_55763.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____55790 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____55790 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____55803 =
            let uu____55807 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____55807  in
          FStar_All.pipe_right uu____55803 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___420_55948  ->
         match uu___420_55948 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____55953 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___578_55965 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___578_55965.curmonad);
        modules = (uu___578_55965.modules);
        scope_mods = (uu___578_55965.scope_mods);
        exported_ids = (uu___578_55965.exported_ids);
        trans_exported_ids = (uu___578_55965.trans_exported_ids);
        includes = (uu___578_55965.includes);
        sigaccum = (uu___578_55965.sigaccum);
        sigmap = (uu___578_55965.sigmap);
        iface = (uu___578_55965.iface);
        admitted_iface = (uu___578_55965.admitted_iface);
        expect_typ = (uu___578_55965.expect_typ);
        docs = (uu___578_55965.docs);
        remaining_iface_decls = (uu___578_55965.remaining_iface_decls);
        syntax_only = (uu___578_55965.syntax_only);
        ds_hooks = (uu___578_55965.ds_hooks);
        dep_graph = (uu___578_55965.dep_graph)
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
      let uu____55989 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____56023  ->
                match uu____56023 with
                | (m,uu____56032) -> FStar_Ident.lid_equals l m))
         in
      match uu____55989 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____56049,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____56083 =
          FStar_List.partition
            (fun uu____56113  ->
               match uu____56113 with
               | (m,uu____56122) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____56083 with
        | (uu____56127,rest) ->
            let uu___603_56161 = env  in
            {
              curmodule = (uu___603_56161.curmodule);
              curmonad = (uu___603_56161.curmonad);
              modules = (uu___603_56161.modules);
              scope_mods = (uu___603_56161.scope_mods);
              exported_ids = (uu___603_56161.exported_ids);
              trans_exported_ids = (uu___603_56161.trans_exported_ids);
              includes = (uu___603_56161.includes);
              sigaccum = (uu___603_56161.sigaccum);
              sigmap = (uu___603_56161.sigmap);
              iface = (uu___603_56161.iface);
              admitted_iface = (uu___603_56161.admitted_iface);
              expect_typ = (uu___603_56161.expect_typ);
              docs = (uu___603_56161.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___603_56161.syntax_only);
              ds_hooks = (uu___603_56161.ds_hooks);
              dep_graph = (uu___603_56161.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____56190 = current_module env  in qual uu____56190 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____56192 =
            let uu____56193 = current_module env  in qual uu____56193 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____56192
            id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___613_56214 = env  in
      {
        curmodule = (uu___613_56214.curmodule);
        curmonad = (uu___613_56214.curmonad);
        modules = (uu___613_56214.modules);
        scope_mods = (uu___613_56214.scope_mods);
        exported_ids = (uu___613_56214.exported_ids);
        trans_exported_ids = (uu___613_56214.trans_exported_ids);
        includes = (uu___613_56214.includes);
        sigaccum = (uu___613_56214.sigaccum);
        sigmap = (uu___613_56214.sigmap);
        iface = (uu___613_56214.iface);
        admitted_iface = (uu___613_56214.admitted_iface);
        expect_typ = (uu___613_56214.expect_typ);
        docs = (uu___613_56214.docs);
        remaining_iface_decls = (uu___613_56214.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___613_56214.ds_hooks);
        dep_graph = (uu___613_56214.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___618_56232 = env  in
      {
        curmodule = (uu___618_56232.curmodule);
        curmonad = (uu___618_56232.curmonad);
        modules = (uu___618_56232.modules);
        scope_mods = (uu___618_56232.scope_mods);
        exported_ids = (uu___618_56232.exported_ids);
        trans_exported_ids = (uu___618_56232.trans_exported_ids);
        includes = (uu___618_56232.includes);
        sigaccum = (uu___618_56232.sigaccum);
        sigmap = (uu___618_56232.sigmap);
        iface = (uu___618_56232.iface);
        admitted_iface = (uu___618_56232.admitted_iface);
        expect_typ = (uu___618_56232.expect_typ);
        docs = (uu___618_56232.docs);
        remaining_iface_decls = (uu___618_56232.remaining_iface_decls);
        syntax_only = (uu___618_56232.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___618_56232.dep_graph)
      }
  
let new_sigmap : 'Auu____56238 . unit -> 'Auu____56238 FStar_Util.smap =
  fun uu____56245  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____56253 = new_sigmap ()  in
    let uu____56258 = new_sigmap ()  in
    let uu____56263 = new_sigmap ()  in
    let uu____56274 = new_sigmap ()  in
    let uu____56287 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____56253;
      trans_exported_ids = uu____56258;
      includes = uu____56263;
      sigaccum = [];
      sigmap = uu____56274;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____56287;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___625_56321 = env  in
      {
        curmodule = (uu___625_56321.curmodule);
        curmonad = (uu___625_56321.curmonad);
        modules = (uu___625_56321.modules);
        scope_mods = (uu___625_56321.scope_mods);
        exported_ids = (uu___625_56321.exported_ids);
        trans_exported_ids = (uu___625_56321.trans_exported_ids);
        includes = (uu___625_56321.includes);
        sigaccum = (uu___625_56321.sigaccum);
        sigmap = (uu___625_56321.sigmap);
        iface = (uu___625_56321.iface);
        admitted_iface = (uu___625_56321.admitted_iface);
        expect_typ = (uu___625_56321.expect_typ);
        docs = (uu___625_56321.docs);
        remaining_iface_decls = (uu___625_56321.remaining_iface_decls);
        syntax_only = (uu___625_56321.syntax_only);
        ds_hooks = (uu___625_56321.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____56349  ->
         match uu____56349 with
         | (m,uu____56356) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___634_56369 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___634_56369.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___637_56370 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index =
          (uu___637_56370.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___637_56370.FStar_Syntax_Syntax.sort)
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
      (fun uu____56473  ->
         match uu____56473 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____56504 =
                 let uu____56505 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____56505 dd dq  in
               FStar_Pervasives_Native.Some uu____56504
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____56545 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____56583 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____56604 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___421_56634  ->
      match uu___421_56634 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____56653 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____56653 cont_t) -> 'Auu____56653 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____56690 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____56690
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____56706  ->
                   match uu____56706 with
                   | (f,uu____56714) ->
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
  fun uu___422_56788  ->
    match uu___422_56788 with
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
              let rec aux uu___423_56864 =
                match uu___423_56864 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____56877 = get_exported_id_set env mname  in
                      match uu____56877 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____56904 = mex eikind  in
                            FStar_ST.op_Bang uu____56904  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____57019 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____57019 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____57096 = qual modul id1  in
                        find_in_module uu____57096
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____57101 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___424_57110  ->
    match uu___424_57110 with
    | Exported_id_field  -> true
    | uu____57113 -> false
  
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
                  let check_local_binding_id uu___425_57237 =
                    match uu___425_57237 with
                    | (id',uu____57240) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___426_57248 =
                    match uu___426_57248 with
                    | (id',uu____57251,uu____57252) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____57257 = current_module env  in
                    FStar_Ident.ids_of_lid uu____57257  in
                  let proc uu___427_57265 =
                    match uu___427_57265 with
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
                        let uu____57274 = FStar_Ident.lid_of_ids curmod_ns
                           in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____57274 id1
                    | uu____57279 -> Cont_ignore  in
                  let rec aux uu___428_57289 =
                    match uu___428_57289 with
                    | a::q ->
                        let uu____57298 = proc a  in
                        option_of_cont (fun uu____57302  -> aux q)
                          uu____57298
                    | [] ->
                        let uu____57303 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____57307  -> FStar_Pervasives_Native.None)
                          uu____57303
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____57315 .
    FStar_Range.range ->
      ('Auu____57315 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____57329  -> match uu____57329 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____57347 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____57347)
          -> 'Auu____57347 -> 'Auu____57347
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____57388 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____57388 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____57432 = unmangleOpName id1  in
      match uu____57432 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____57438 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____57444 =
                 found_local_binding id1.FStar_Ident.idRange r  in
               Cont_ok uu____57444) (fun uu____57446  -> Cont_fail)
            (fun uu____57448  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____57455  -> fun uu____57456  -> Cont_fail)
                 Cont_ignore)
            (fun uu____57464  -> fun uu____57465  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____57539 ->
                let lid = qualify env id1  in
                let uu____57541 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____57541 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____57569 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____57569
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____57593 = current_module env  in qual uu____57593 id1
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
        let rec aux uu___429_57665 =
          match uu___429_57665 with
          | [] ->
              let uu____57670 = module_is_defined env lid  in
              if uu____57670
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____57682 =
                  let uu____57683 = FStar_Ident.path_of_lid ns  in
                  let uu____57687 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____57683 uu____57687  in
                let uu____57692 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____57682 uu____57692  in
              let uu____57693 = module_is_defined env new_lid  in
              if uu____57693
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____57702 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____57712::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____57732 =
          let uu____57734 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____57734  in
        if uu____57732
        then
          let uu____57736 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____57736
           then ()
           else
             (let uu____57741 =
                let uu____57747 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____57747)
                 in
              let uu____57751 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____57741 uu____57751))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____57765 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____57769 = resolve_module_name env modul_orig true  in
          (match uu____57769 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____57774 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___430_57797  ->
             match uu___430_57797 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____57801 -> false) env.scope_mods
  
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
                 let uu____57930 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____57930
                   (FStar_Util.map_option
                      (fun uu____57980  ->
                         match uu____57980 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____58050 = aux ns_rev_prefix ns_last_id  in
              (match uu____58050 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____58113 =
            let uu____58116 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____58116 true  in
          match uu____58113 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____58131 -> do_shorten env ids
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
                  | uu____58252::uu____58253 ->
                      let uu____58256 =
                        let uu____58259 =
                          let uu____58260 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____58261 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____58260 uu____58261
                           in
                        resolve_module_name env uu____58259 true  in
                      (match uu____58256 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____58266 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____58270  ->
                                FStar_Pervasives_Native.None) uu____58266)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___431_58294  ->
      match uu___431_58294 with
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
              let uu____58415 = k_global_def lid1 def  in
              cont_of_option k uu____58415  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____58451 = k_local_binding l  in
                 cont_of_option Cont_fail uu____58451)
              (fun r  ->
                 let uu____58457 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____58457)
              (fun uu____58461  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____58472,uu____58473,uu____58474,l,uu____58476,uu____58477) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___432_58490  ->
               match uu___432_58490 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____58493,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____58505 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____58511,uu____58512,uu____58513) -> FStar_Pervasives_Native.None
    | uu____58514 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____58530 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____58538 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____58538
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____58530 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____58561 =
         let uu____58562 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____58562  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____58561) &&
        (let uu____58570 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____58570 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____58587 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___433_58594  ->
                     match uu___433_58594 with
                     | FStar_Syntax_Syntax.Projector uu____58596 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____58602 -> true
                     | uu____58604 -> false)))
           in
        if uu____58587
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____58609 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___434_58615  ->
                 match uu___434_58615 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____58618 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___435_58624  ->
                    match uu___435_58624 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____58627 -> false)))
             &&
             (let uu____58630 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___436_58636  ->
                        match uu___436_58636 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____58639 -> false))
                 in
              Prims.op_Negation uu____58630))
         in
      if uu____58609 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___439_58691 =
            match uu___439_58691 with
            | (uu____58699,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____58703) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____58708 ->
                     let uu____58725 =
                       let uu____58726 =
                         let uu____58733 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____58733, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58726  in
                     FStar_Pervasives_Native.Some uu____58725
                 | FStar_Syntax_Syntax.Sig_datacon uu____58736 ->
                     let uu____58752 =
                       let uu____58753 =
                         let uu____58760 =
                           let uu____58761 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____58761
                            in
                         (uu____58760, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58753  in
                     FStar_Pervasives_Native.Some uu____58752
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____58766,lbs),uu____58768) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____58780 =
                       let uu____58781 =
                         let uu____58788 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____58788, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58781  in
                     FStar_Pervasives_Native.Some uu____58780
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____58792,uu____58793) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____58797 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___437_58803  ->
                                  match uu___437_58803 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____58806 -> false)))
                        in
                     if uu____58797
                     then
                       let lid2 =
                         let uu____58812 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____58812  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____58814 =
                         FStar_Util.find_map quals
                           (fun uu___438_58819  ->
                              match uu___438_58819 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____58823 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____58814 with
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
                        | uu____58832 ->
                            let uu____58835 =
                              let uu____58836 =
                                let uu____58843 =
                                  let uu____58844 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____58844
                                   in
                                (uu____58843,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____58836  in
                            FStar_Pervasives_Native.Some uu____58835)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
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
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____58861 =
                       let uu____58862 =
                         let uu____58867 =
                           let uu____58868 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____58868
                            in
                         (se, uu____58867)  in
                       Eff_name uu____58862  in
                     FStar_Pervasives_Native.Some uu____58861
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____58869 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____58888 =
                       let uu____58889 =
                         let uu____58896 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____58896, [])  in
                       Term_name uu____58889  in
                     FStar_Pervasives_Native.Some uu____58888
                 | uu____58900 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____58918 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____58918 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____58934 =
            match uu____58934 with
            | (id1,l,dd) ->
                let uu____58946 =
                  let uu____58947 =
                    let uu____58954 =
                      let uu____58955 =
                        let uu____58956 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____58956  in
                      FStar_Syntax_Syntax.fvar uu____58955 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____58954, [])  in
                  Term_name uu____58947  in
                FStar_Pervasives_Native.Some uu____58946
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____58964 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____58964 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____58972 -> FStar_Pervasives_Native.None)
            | uu____58975 -> FStar_Pervasives_Native.None  in
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
        let uu____59013 = try_lookup_name true exclude_interf env lid  in
        match uu____59013 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____59029 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59049 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59049 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____59064 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59090 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59090 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____59106;
             FStar_Syntax_Syntax.sigquals = uu____59107;
             FStar_Syntax_Syntax.sigmeta = uu____59108;
             FStar_Syntax_Syntax.sigattrs = uu____59109;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____59128;
             FStar_Syntax_Syntax.sigquals = uu____59129;
             FStar_Syntax_Syntax.sigmeta = uu____59130;
             FStar_Syntax_Syntax.sigattrs = uu____59131;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____59149,uu____59150,uu____59151,uu____59152,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____59154;
             FStar_Syntax_Syntax.sigquals = uu____59155;
             FStar_Syntax_Syntax.sigmeta = uu____59156;
             FStar_Syntax_Syntax.sigattrs = uu____59157;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____59179 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59205 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59205 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____59215;
             FStar_Syntax_Syntax.sigquals = uu____59216;
             FStar_Syntax_Syntax.sigmeta = uu____59217;
             FStar_Syntax_Syntax.sigattrs = uu____59218;_},uu____59219)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____59229;
             FStar_Syntax_Syntax.sigquals = uu____59230;
             FStar_Syntax_Syntax.sigmeta = uu____59231;
             FStar_Syntax_Syntax.sigattrs = uu____59232;_},uu____59233)
          -> FStar_Pervasives_Native.Some ne
      | uu____59242 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____59261 = try_lookup_effect_name env lid  in
      match uu____59261 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____59266 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59281 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59281 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____59291,uu____59292,uu____59293,uu____59294);
             FStar_Syntax_Syntax.sigrng = uu____59295;
             FStar_Syntax_Syntax.sigquals = uu____59296;
             FStar_Syntax_Syntax.sigmeta = uu____59297;
             FStar_Syntax_Syntax.sigattrs = uu____59298;_},uu____59299)
          ->
          let rec aux new_name =
            let uu____59320 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____59320 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____59341) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____59352 =
                       let uu____59353 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____59353
                        in
                     FStar_Pervasives_Native.Some uu____59352
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____59355 =
                       let uu____59356 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____59356
                        in
                     FStar_Pervasives_Native.Some uu____59355
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____59357,uu____59358,uu____59359,cmp,uu____59361) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____59367 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____59368,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____59374 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___440_59413 =
        match uu___440_59413 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____59423,uu____59424,uu____59425);
             FStar_Syntax_Syntax.sigrng = uu____59426;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____59428;
             FStar_Syntax_Syntax.sigattrs = uu____59429;_},uu____59430)
            -> FStar_Pervasives_Native.Some quals
        | uu____59439 -> FStar_Pervasives_Native.None  in
      let uu____59447 =
        resolve_in_open_namespaces' env lid
          (fun uu____59455  -> FStar_Pervasives_Native.None)
          (fun uu____59459  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____59447 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____59469 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____59487 =
        FStar_List.tryFind
          (fun uu____59502  ->
             match uu____59502 with
             | (mlid,modul) ->
                 let uu____59510 = FStar_Ident.path_of_lid mlid  in
                 uu____59510 = path) env.modules
         in
      match uu____59487 with
      | FStar_Pervasives_Native.Some (uu____59513,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___441_59553 =
        match uu___441_59553 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____59561,lbs),uu____59563);
             FStar_Syntax_Syntax.sigrng = uu____59564;
             FStar_Syntax_Syntax.sigquals = uu____59565;
             FStar_Syntax_Syntax.sigmeta = uu____59566;
             FStar_Syntax_Syntax.sigattrs = uu____59567;_},uu____59568)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____59586 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____59586
        | uu____59587 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____59594  -> FStar_Pervasives_Native.None)
        (fun uu____59596  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___442_59629 =
        match uu___442_59629 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____59640);
             FStar_Syntax_Syntax.sigrng = uu____59641;
             FStar_Syntax_Syntax.sigquals = uu____59642;
             FStar_Syntax_Syntax.sigmeta = uu____59643;
             FStar_Syntax_Syntax.sigattrs = uu____59644;_},uu____59645)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____59671 -> FStar_Pervasives_Native.None)
        | uu____59678 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____59689  -> FStar_Pervasives_Native.None)
        (fun uu____59693  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____59753 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____59753 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____59778 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____59816) ->
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
      let uu____59874 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____59874 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59906 = try_lookup_lid env l  in
      match uu____59906 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____59912 =
            let uu____59913 = FStar_Syntax_Subst.compress e  in
            uu____59913.FStar_Syntax_Syntax.n  in
          (match uu____59912 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____59919 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____59931 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____59931 with
      | (uu____59941,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____59962 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____59966 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____59966 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____59971 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___1304_60002 = env  in
        {
          curmodule = (uu___1304_60002.curmodule);
          curmonad = (uu___1304_60002.curmonad);
          modules = (uu___1304_60002.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___1304_60002.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___1304_60002.sigaccum);
          sigmap = (uu___1304_60002.sigmap);
          iface = (uu___1304_60002.iface);
          admitted_iface = (uu___1304_60002.admitted_iface);
          expect_typ = (uu___1304_60002.expect_typ);
          docs = (uu___1304_60002.docs);
          remaining_iface_decls = (uu___1304_60002.remaining_iface_decls);
          syntax_only = (uu___1304_60002.syntax_only);
          ds_hooks = (uu___1304_60002.ds_hooks);
          dep_graph = (uu___1304_60002.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____60018 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____60018 drop_attributes
  
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
               (uu____60088,uu____60089,uu____60090);
             FStar_Syntax_Syntax.sigrng = uu____60091;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____60093;
             FStar_Syntax_Syntax.sigattrs = uu____60094;_},uu____60095)
            ->
            let uu____60102 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___443_60108  ->
                      match uu___443_60108 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____60111 -> false))
               in
            if uu____60102
            then
              let uu____60116 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____60116
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____60119;
             FStar_Syntax_Syntax.sigrng = uu____60120;
             FStar_Syntax_Syntax.sigquals = uu____60121;
             FStar_Syntax_Syntax.sigmeta = uu____60122;
             FStar_Syntax_Syntax.sigattrs = uu____60123;_},uu____60124)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____60150 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____60150
        | uu____60151 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____60158  -> FStar_Pervasives_Native.None)
        (fun uu____60160  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___444_60195 =
        match uu___444_60195 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____60205,uu____60206,uu____60207,uu____60208,datas,uu____60210);
             FStar_Syntax_Syntax.sigrng = uu____60211;
             FStar_Syntax_Syntax.sigquals = uu____60212;
             FStar_Syntax_Syntax.sigmeta = uu____60213;
             FStar_Syntax_Syntax.sigattrs = uu____60214;_},uu____60215)
            -> FStar_Pervasives_Native.Some datas
        | uu____60232 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____60243  -> FStar_Pervasives_Native.None)
        (fun uu____60247  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____60326 =
    let uu____60327 =
      let uu____60332 =
        let uu____60335 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____60335  in
      let uu____60391 = FStar_ST.op_Bang record_cache  in uu____60332 ::
        uu____60391
       in
    FStar_ST.op_Colon_Equals record_cache uu____60327  in
  let pop1 uu____60501 =
    let uu____60502 =
      let uu____60507 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____60507  in
    FStar_ST.op_Colon_Equals record_cache uu____60502  in
  let snapshot1 uu____60622 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____60690 =
    let uu____60691 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____60691  in
  let insert r =
    let uu____60753 =
      let uu____60758 = let uu____60761 = peek1 ()  in r :: uu____60761  in
      let uu____60764 =
        let uu____60769 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____60769  in
      uu____60758 :: uu____60764  in
    FStar_ST.op_Colon_Equals record_cache uu____60753  in
  let filter1 uu____60881 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____60890 =
      let uu____60895 =
        let uu____60900 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____60900  in
      filtered :: uu____60895  in
    FStar_ST.op_Colon_Equals record_cache uu____60890  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____61892) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___445_61911  ->
                   match uu___445_61911 with
                   | FStar_Syntax_Syntax.RecordType uu____61913 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____61923 ->
                       true
                   | uu____61933 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___446_61958  ->
                      match uu___446_61958 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____61961,uu____61962,uu____61963,uu____61964,uu____61965);
                          FStar_Syntax_Syntax.sigrng = uu____61966;
                          FStar_Syntax_Syntax.sigquals = uu____61967;
                          FStar_Syntax_Syntax.sigmeta = uu____61968;
                          FStar_Syntax_Syntax.sigattrs = uu____61969;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____61980 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___447_62016  ->
                    match uu___447_62016 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____62020,uu____62021,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____62023;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____62025;
                        FStar_Syntax_Syntax.sigattrs = uu____62026;_} ->
                        let uu____62037 =
                          let uu____62038 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____62038  in
                        (match uu____62037 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____62044,t,uu____62046,uu____62047,uu____62048);
                             FStar_Syntax_Syntax.sigrng = uu____62049;
                             FStar_Syntax_Syntax.sigquals = uu____62050;
                             FStar_Syntax_Syntax.sigmeta = uu____62051;
                             FStar_Syntax_Syntax.sigattrs = uu____62052;_} ->
                             let uu____62063 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____62063 with
                              | (formals,uu____62079) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____62133  ->
                                            match uu____62133 with
                                            | (x,q) ->
                                                let uu____62146 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____62146
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____62201  ->
                                            match uu____62201 with
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
                                  ((let uu____62225 =
                                      let uu____62228 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____62228
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____62225);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____62331 =
                                            match uu____62331 with
                                            | (id1,uu____62337) ->
                                                let modul =
                                                  let uu____62340 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____62340.FStar_Ident.str
                                                   in
                                                let uu____62341 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____62341 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____62375 =
                                                         let uu____62376 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____62376
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____62375);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____62465
                                                               =
                                                               let uu____62466
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____62466.FStar_Ident.ident
                                                                in
                                                             uu____62465.FStar_Ident.idText
                                                              in
                                                           let uu____62468 =
                                                             let uu____62469
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____62469
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____62468))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____62565 -> ())
                    | uu____62566 -> ()))
        | uu____62567 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____62589 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____62589 with
        | (ns,id1) ->
            let uu____62606 = peek_record_cache ()  in
            FStar_Util.find_map uu____62606
              (fun record  ->
                 let uu____62612 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____62618  -> FStar_Pervasives_Native.None)
                   uu____62612)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____62620  -> Cont_ignore) (fun uu____62622  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____62628 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____62628)
        (fun k  -> fun uu____62634  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____62650 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____62650 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____62656 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____62676 = try_lookup_record_by_field_name env lid  in
        match uu____62676 with
        | FStar_Pervasives_Native.Some record' when
            let uu____62681 =
              let uu____62683 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____62683  in
            let uu____62684 =
              let uu____62686 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____62686  in
            uu____62681 = uu____62684 ->
            let uu____62688 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____62692  -> Cont_ok ())
               in
            (match uu____62688 with
             | Cont_ok uu____62694 -> true
             | uu____62696 -> false)
        | uu____62700 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____62722 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____62722 with
      | FStar_Pervasives_Native.Some r ->
          let uu____62733 =
            let uu____62739 =
              let uu____62740 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____62741 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____62740 uu____62741  in
            (uu____62739, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____62733
      | uu____62748 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____62777  ->
    let uu____62778 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____62778
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____62810  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___448_62823  ->
      match uu___448_62823 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___449_62883 =
            match uu___449_62883 with
            | Rec_binding uu____62885 -> true
            | uu____62887 -> false  in
          let this_env =
            let uu___1530_62890 = env  in
            let uu____62891 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1530_62890.curmodule);
              curmonad = (uu___1530_62890.curmonad);
              modules = (uu___1530_62890.modules);
              scope_mods = uu____62891;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1530_62890.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1530_62890.sigaccum);
              sigmap = (uu___1530_62890.sigmap);
              iface = (uu___1530_62890.iface);
              admitted_iface = (uu___1530_62890.admitted_iface);
              expect_typ = (uu___1530_62890.expect_typ);
              docs = (uu___1530_62890.docs);
              remaining_iface_decls = (uu___1530_62890.remaining_iface_decls);
              syntax_only = (uu___1530_62890.syntax_only);
              ds_hooks = (uu___1530_62890.ds_hooks);
              dep_graph = (uu___1530_62890.dep_graph)
            }  in
          let uu____62894 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____62894 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____62911 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1538_62936 = env  in
      {
        curmodule = (uu___1538_62936.curmodule);
        curmonad = (uu___1538_62936.curmonad);
        modules = (uu___1538_62936.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1538_62936.exported_ids);
        trans_exported_ids = (uu___1538_62936.trans_exported_ids);
        includes = (uu___1538_62936.includes);
        sigaccum = (uu___1538_62936.sigaccum);
        sigmap = (uu___1538_62936.sigmap);
        iface = (uu___1538_62936.iface);
        admitted_iface = (uu___1538_62936.admitted_iface);
        expect_typ = (uu___1538_62936.expect_typ);
        docs = (uu___1538_62936.docs);
        remaining_iface_decls = (uu___1538_62936.remaining_iface_decls);
        syntax_only = (uu___1538_62936.syntax_only);
        ds_hooks = (uu___1538_62936.ds_hooks);
        dep_graph = (uu___1538_62936.dep_graph)
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
        let uu____62970 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____62970
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____62977 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____62977)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____63021) ->
                let uu____63029 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____63029 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____63034 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____63034
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____63043 =
            let uu____63049 =
              let uu____63051 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____63051 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____63049)  in
          let uu____63055 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____63043 uu____63055  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____63064 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____63077 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____63088 -> (false, true)
            | uu____63101 -> (false, false)  in
          match uu____63064 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____63115 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____63121 =
                       let uu____63123 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____63123  in
                     if uu____63121
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____63115 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____63131 ->
                   (extract_record env globals s;
                    (let uu___1579_63157 = env  in
                     {
                       curmodule = (uu___1579_63157.curmodule);
                       curmonad = (uu___1579_63157.curmonad);
                       modules = (uu___1579_63157.modules);
                       scope_mods = (uu___1579_63157.scope_mods);
                       exported_ids = (uu___1579_63157.exported_ids);
                       trans_exported_ids =
                         (uu___1579_63157.trans_exported_ids);
                       includes = (uu___1579_63157.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1579_63157.sigmap);
                       iface = (uu___1579_63157.iface);
                       admitted_iface = (uu___1579_63157.admitted_iface);
                       expect_typ = (uu___1579_63157.expect_typ);
                       docs = (uu___1579_63157.docs);
                       remaining_iface_decls =
                         (uu___1579_63157.remaining_iface_decls);
                       syntax_only = (uu___1579_63157.syntax_only);
                       ds_hooks = (uu___1579_63157.ds_hooks);
                       dep_graph = (uu___1579_63157.dep_graph)
                     })))
           in
        let env2 =
          let uu___1582_63159 = env1  in
          let uu____63160 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1582_63159.curmodule);
            curmonad = (uu___1582_63159.curmonad);
            modules = (uu___1582_63159.modules);
            scope_mods = uu____63160;
            exported_ids = (uu___1582_63159.exported_ids);
            trans_exported_ids = (uu___1582_63159.trans_exported_ids);
            includes = (uu___1582_63159.includes);
            sigaccum = (uu___1582_63159.sigaccum);
            sigmap = (uu___1582_63159.sigmap);
            iface = (uu___1582_63159.iface);
            admitted_iface = (uu___1582_63159.admitted_iface);
            expect_typ = (uu___1582_63159.expect_typ);
            docs = (uu___1582_63159.docs);
            remaining_iface_decls = (uu___1582_63159.remaining_iface_decls);
            syntax_only = (uu___1582_63159.syntax_only);
            ds_hooks = (uu___1582_63159.ds_hooks);
            dep_graph = (uu___1582_63159.dep_graph)
          }  in
        let uu____63208 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____63234) ->
              let uu____63243 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____63243)
          | uu____63270 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____63208 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____63329  ->
                     match uu____63329 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____63351 =
                                    let uu____63354 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____63354
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____63351);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____63449 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____63449.FStar_Ident.str  in
                                      ((let uu____63451 =
                                          get_exported_id_set env3 modul  in
                                        match uu____63451 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____63484 =
                                              let uu____63485 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____63485
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____63484
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
                let uu___1607_63586 = env3  in
                let uu____63587 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1607_63586.curmodule);
                  curmonad = (uu___1607_63586.curmonad);
                  modules = (uu___1607_63586.modules);
                  scope_mods = uu____63587;
                  exported_ids = (uu___1607_63586.exported_ids);
                  trans_exported_ids = (uu___1607_63586.trans_exported_ids);
                  includes = (uu___1607_63586.includes);
                  sigaccum = (uu___1607_63586.sigaccum);
                  sigmap = (uu___1607_63586.sigmap);
                  iface = (uu___1607_63586.iface);
                  admitted_iface = (uu___1607_63586.admitted_iface);
                  expect_typ = (uu___1607_63586.expect_typ);
                  docs = (uu___1607_63586.docs);
                  remaining_iface_decls =
                    (uu___1607_63586.remaining_iface_decls);
                  syntax_only = (uu___1607_63586.syntax_only);
                  ds_hooks = (uu___1607_63586.ds_hooks);
                  dep_graph = (uu___1607_63586.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____63670 =
        let uu____63675 = resolve_module_name env ns false  in
        match uu____63675 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____63690 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____63708  ->
                      match uu____63708 with
                      | (m,uu____63715) ->
                          let uu____63716 =
                            let uu____63718 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____63718 "."  in
                          let uu____63721 =
                            let uu____63723 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____63723 "."  in
                          FStar_Util.starts_with uu____63716 uu____63721))
               in
            if uu____63690
            then (ns, Open_namespace)
            else
              (let uu____63733 =
                 let uu____63739 =
                   let uu____63741 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____63741
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____63739)  in
               let uu____63745 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____63733 uu____63745)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____63670 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____63767 = resolve_module_name env ns false  in
      match uu____63767 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____63777 = current_module env1  in
              uu____63777.FStar_Ident.str  in
            (let uu____63779 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____63779 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____63803 =
                   let uu____63806 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____63806
                    in
                 FStar_ST.op_Colon_Equals incl uu____63803);
            (match () with
             | () ->
                 let uu____63899 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____63899 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____63919 =
                          let uu____64016 = get_exported_id_set env1 curmod
                             in
                          let uu____64063 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____64016, uu____64063)  in
                        match uu____63919 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____64479 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____64479  in
                              let ex = cur_exports k  in
                              (let uu____64654 =
                                 let uu____64658 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____64658 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____64654);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____64855 =
                                     let uu____64859 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____64859 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____64855)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____64992 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____65094 =
                        let uu____65100 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____65100)
                         in
                      let uu____65104 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____65094 uu____65104))))
      | uu____65105 ->
          let uu____65108 =
            let uu____65114 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____65114)  in
          let uu____65118 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____65108 uu____65118
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____65135 = module_is_defined env l  in
        if uu____65135
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____65142 =
             let uu____65148 =
               let uu____65150 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____65150  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____65148)  in
           let uu____65154 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____65142 uu____65154)
  
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
            ((let uu____65177 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____65177 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____65181 = FStar_Ident.range_of_lid l  in
                  let uu____65182 =
                    let uu____65188 =
                      let uu____65190 = FStar_Ident.string_of_lid l  in
                      let uu____65192 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____65194 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____65190 uu____65192 uu____65194
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____65188)  in
                  FStar_Errors.log_issue uu____65181 uu____65182);
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
                      let uu____65240 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____65240 ->
                      let uu____65245 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____65245 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____65260;
                              FStar_Syntax_Syntax.sigrng = uu____65261;
                              FStar_Syntax_Syntax.sigquals = uu____65262;
                              FStar_Syntax_Syntax.sigmeta = uu____65263;
                              FStar_Syntax_Syntax.sigattrs = uu____65264;_},uu____65265)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____65283;
                              FStar_Syntax_Syntax.sigrng = uu____65284;
                              FStar_Syntax_Syntax.sigquals = uu____65285;
                              FStar_Syntax_Syntax.sigmeta = uu____65286;
                              FStar_Syntax_Syntax.sigattrs = uu____65287;_},uu____65288)
                           -> lids
                       | uu____65316 ->
                           ((let uu____65325 =
                               let uu____65327 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____65327  in
                             if uu____65325
                             then
                               let uu____65330 = FStar_Ident.range_of_lid l
                                  in
                               let uu____65331 =
                                 let uu____65337 =
                                   let uu____65339 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____65339
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____65337)
                                  in
                               FStar_Errors.log_issue uu____65330 uu____65331
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1710_65356 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1710_65356.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1710_65356.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1710_65356.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1710_65356.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____65358 -> lids) [])
         in
      let uu___1715_65359 = m  in
      let uu____65360 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____65370,uu____65371) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1724_65374 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1724_65374.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1724_65374.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1724_65374.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1724_65374.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____65375 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1715_65359.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____65360;
        FStar_Syntax_Syntax.exports =
          (uu___1715_65359.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1715_65359.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____65399) ->
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
                                (lid,uu____65420,uu____65421,uu____65422,uu____65423,uu____65424)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____65440,uu____65441)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____65458 =
                                        let uu____65465 =
                                          let uu____65466 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____65467 =
                                            let uu____65474 =
                                              let uu____65475 =
                                                let uu____65490 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____65490)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____65475
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____65474
                                             in
                                          uu____65467
                                            FStar_Pervasives_Native.None
                                            uu____65466
                                           in
                                        (lid, univ_names, uu____65465)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____65458
                                       in
                                    let se2 =
                                      let uu___1756_65507 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1756_65507.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1756_65507.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1756_65507.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____65517 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____65521,uu____65522) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____65531,lbs),uu____65533)
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
                             let uu____65551 =
                               let uu____65553 =
                                 let uu____65554 =
                                   let uu____65557 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____65557.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____65554.FStar_Syntax_Syntax.v  in
                               uu____65553.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____65551))
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
                               let uu____65574 =
                                 let uu____65577 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____65577.FStar_Syntax_Syntax.fv_name  in
                               uu____65574.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1779_65582 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1779_65582.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1779_65582.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1779_65582.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____65592 -> ()));
      (let curmod =
         let uu____65595 = current_module env  in uu____65595.FStar_Ident.str
          in
       (let uu____65597 =
          let uu____65694 = get_exported_id_set env curmod  in
          let uu____65741 = get_trans_exported_id_set env curmod  in
          (uu____65694, uu____65741)  in
        match uu____65597 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____66160 = cur_ex eikind  in
                FStar_ST.op_Bang uu____66160  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____66350 =
                let uu____66354 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____66354  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____66350  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____66487 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1797_66585 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1797_66585.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1797_66585.exported_ids);
                    trans_exported_ids = (uu___1797_66585.trans_exported_ids);
                    includes = (uu___1797_66585.includes);
                    sigaccum = [];
                    sigmap = (uu___1797_66585.sigmap);
                    iface = (uu___1797_66585.iface);
                    admitted_iface = (uu___1797_66585.admitted_iface);
                    expect_typ = (uu___1797_66585.expect_typ);
                    docs = (uu___1797_66585.docs);
                    remaining_iface_decls =
                      (uu___1797_66585.remaining_iface_decls);
                    syntax_only = (uu___1797_66585.syntax_only);
                    ds_hooks = (uu___1797_66585.ds_hooks);
                    dep_graph = (uu___1797_66585.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____66623  ->
         push_record_cache ();
         (let uu____66626 =
            let uu____66629 = FStar_ST.op_Bang stack  in env :: uu____66629
             in
          FStar_ST.op_Colon_Equals stack uu____66626);
         (let uu___1803_66678 = env  in
          let uu____66679 = FStar_Util.smap_copy env.exported_ids  in
          let uu____66684 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____66689 = FStar_Util.smap_copy env.includes  in
          let uu____66700 = FStar_Util.smap_copy env.sigmap  in
          let uu____66713 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1803_66678.curmodule);
            curmonad = (uu___1803_66678.curmonad);
            modules = (uu___1803_66678.modules);
            scope_mods = (uu___1803_66678.scope_mods);
            exported_ids = uu____66679;
            trans_exported_ids = uu____66684;
            includes = uu____66689;
            sigaccum = (uu___1803_66678.sigaccum);
            sigmap = uu____66700;
            iface = (uu___1803_66678.iface);
            admitted_iface = (uu___1803_66678.admitted_iface);
            expect_typ = (uu___1803_66678.expect_typ);
            docs = uu____66713;
            remaining_iface_decls = (uu___1803_66678.remaining_iface_decls);
            syntax_only = (uu___1803_66678.syntax_only);
            ds_hooks = (uu___1803_66678.ds_hooks);
            dep_graph = (uu___1803_66678.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____66721  ->
    FStar_Util.atomically
      (fun uu____66728  ->
         let uu____66729 = FStar_ST.op_Bang stack  in
         match uu____66729 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____66784 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____66831 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____66835 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____66877 = FStar_Util.smap_try_find sm' k  in
              match uu____66877 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1838_66908 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1838_66908.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1838_66908.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1838_66908.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1838_66908.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____66909 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____66917 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____66944 = finish env modul1  in (uu____66944, modul1)
  
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
      let uu____67046 =
        let uu____67050 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____67050  in
      FStar_Util.set_elements uu____67046  in
    let fields =
      let uu____67166 =
        let uu____67170 = e Exported_id_field  in
        FStar_ST.op_Bang uu____67170  in
      FStar_Util.set_elements uu____67166  in
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
          let uu____67326 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____67326  in
        let fields =
          let uu____67340 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____67340  in
        (fun uu___450_67348  ->
           match uu___450_67348 with
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
  'Auu____67485 .
    'Auu____67485 Prims.list FStar_Pervasives_Native.option ->
      'Auu____67485 Prims.list FStar_ST.ref
  =
  fun uu___451_67498  ->
    match uu___451_67498 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____67541 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____67541 as_exported_ids  in
      let uu____67547 = as_ids_opt env.exported_ids  in
      let uu____67550 = as_ids_opt env.trans_exported_ids  in
      let uu____67553 =
        let uu____67558 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____67558 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____67547;
        mii_trans_exported_ids = uu____67550;
        mii_includes = uu____67553
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
                let uu____67680 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____67680 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___452_67702 =
                  match uu___452_67702 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____67714  ->
                     match uu____67714 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____67740 =
                    let uu____67745 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____67745, Open_namespace)  in
                  [uu____67740]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____67776 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____67776);
              (match () with
               | () ->
                   ((let uu____67803 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____67803);
                    (match () with
                     | () ->
                         ((let uu____67830 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____67830);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1908_67862 = env1  in
                                 let uu____67863 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1908_67862.curmonad);
                                   modules = (uu___1908_67862.modules);
                                   scope_mods = uu____67863;
                                   exported_ids =
                                     (uu___1908_67862.exported_ids);
                                   trans_exported_ids =
                                     (uu___1908_67862.trans_exported_ids);
                                   includes = (uu___1908_67862.includes);
                                   sigaccum = (uu___1908_67862.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1908_67862.expect_typ);
                                   docs = (uu___1908_67862.docs);
                                   remaining_iface_decls =
                                     (uu___1908_67862.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1908_67862.syntax_only);
                                   ds_hooks = (uu___1908_67862.ds_hooks);
                                   dep_graph = (uu___1908_67862.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____67875 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____67901  ->
                      match uu____67901 with
                      | (l,uu____67908) -> FStar_Ident.lid_equals l mname))
               in
            match uu____67875 with
            | FStar_Pervasives_Native.None  ->
                let uu____67918 = prep env  in (uu____67918, false)
            | FStar_Pervasives_Native.Some (uu____67921,m) ->
                ((let uu____67928 =
                    (let uu____67932 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____67932) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____67928
                  then
                    let uu____67935 =
                      let uu____67941 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____67941)
                       in
                    let uu____67945 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____67935 uu____67945
                  else ());
                 (let uu____67948 =
                    let uu____67949 = push env  in prep uu____67949  in
                  (uu____67948, true)))
  
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
          let uu___1929_67967 = env  in
          {
            curmodule = (uu___1929_67967.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1929_67967.modules);
            scope_mods = (uu___1929_67967.scope_mods);
            exported_ids = (uu___1929_67967.exported_ids);
            trans_exported_ids = (uu___1929_67967.trans_exported_ids);
            includes = (uu___1929_67967.includes);
            sigaccum = (uu___1929_67967.sigaccum);
            sigmap = (uu___1929_67967.sigmap);
            iface = (uu___1929_67967.iface);
            admitted_iface = (uu___1929_67967.admitted_iface);
            expect_typ = (uu___1929_67967.expect_typ);
            docs = (uu___1929_67967.docs);
            remaining_iface_decls = (uu___1929_67967.remaining_iface_decls);
            syntax_only = (uu___1929_67967.syntax_only);
            ds_hooks = (uu___1929_67967.ds_hooks);
            dep_graph = (uu___1929_67967.dep_graph)
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
        let uu____68002 = lookup1 lid  in
        match uu____68002 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____68017  ->
                   match uu____68017 with
                   | (lid1,uu____68024) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____68027 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____68027  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____68039 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____68040 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____68039 uu____68040  in
                 let uu____68041 = resolve_module_name env modul true  in
                 match uu____68041 with
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
            let uu____68062 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____68062
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____68092 = lookup1 id1  in
      match uu____68092 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  