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
    match projectee with | Open_module  -> true | uu____53607 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____53618 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____53838 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____53858 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____53878 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____53898 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____53918 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____53938 -> false
  
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
    | uu____53960 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____53971 -> false
  
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
    ds_push_open_hook = (fun uu____55591  -> fun uu____55592  -> ());
    ds_push_include_hook = (fun uu____55595  -> fun uu____55596  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____55600  -> fun uu____55601  -> fun uu____55602  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____55639 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____55681 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___549_55716 = env  in
      {
        curmodule = (uu___549_55716.curmodule);
        curmonad = (uu___549_55716.curmonad);
        modules = (uu___549_55716.modules);
        scope_mods = (uu___549_55716.scope_mods);
        exported_ids = (uu___549_55716.exported_ids);
        trans_exported_ids = (uu___549_55716.trans_exported_ids);
        includes = (uu___549_55716.includes);
        sigaccum = (uu___549_55716.sigaccum);
        sigmap = (uu___549_55716.sigmap);
        iface = b;
        admitted_iface = (uu___549_55716.admitted_iface);
        expect_typ = (uu___549_55716.expect_typ);
        docs = (uu___549_55716.docs);
        remaining_iface_decls = (uu___549_55716.remaining_iface_decls);
        syntax_only = (uu___549_55716.syntax_only);
        ds_hooks = (uu___549_55716.ds_hooks);
        dep_graph = (uu___549_55716.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___554_55737 = e  in
      {
        curmodule = (uu___554_55737.curmodule);
        curmonad = (uu___554_55737.curmonad);
        modules = (uu___554_55737.modules);
        scope_mods = (uu___554_55737.scope_mods);
        exported_ids = (uu___554_55737.exported_ids);
        trans_exported_ids = (uu___554_55737.trans_exported_ids);
        includes = (uu___554_55737.includes);
        sigaccum = (uu___554_55737.sigaccum);
        sigmap = (uu___554_55737.sigmap);
        iface = (uu___554_55737.iface);
        admitted_iface = b;
        expect_typ = (uu___554_55737.expect_typ);
        docs = (uu___554_55737.docs);
        remaining_iface_decls = (uu___554_55737.remaining_iface_decls);
        syntax_only = (uu___554_55737.syntax_only);
        ds_hooks = (uu___554_55737.ds_hooks);
        dep_graph = (uu___554_55737.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___559_55758 = e  in
      {
        curmodule = (uu___559_55758.curmodule);
        curmonad = (uu___559_55758.curmonad);
        modules = (uu___559_55758.modules);
        scope_mods = (uu___559_55758.scope_mods);
        exported_ids = (uu___559_55758.exported_ids);
        trans_exported_ids = (uu___559_55758.trans_exported_ids);
        includes = (uu___559_55758.includes);
        sigaccum = (uu___559_55758.sigaccum);
        sigmap = (uu___559_55758.sigmap);
        iface = (uu___559_55758.iface);
        admitted_iface = (uu___559_55758.admitted_iface);
        expect_typ = b;
        docs = (uu___559_55758.docs);
        remaining_iface_decls = (uu___559_55758.remaining_iface_decls);
        syntax_only = (uu___559_55758.syntax_only);
        ds_hooks = (uu___559_55758.ds_hooks);
        dep_graph = (uu___559_55758.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____55785 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____55785 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____55798 =
            let uu____55802 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____55802  in
          FStar_All.pipe_right uu____55798 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___420_55943  ->
         match uu___420_55943 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____55948 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___578_55960 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___578_55960.curmonad);
        modules = (uu___578_55960.modules);
        scope_mods = (uu___578_55960.scope_mods);
        exported_ids = (uu___578_55960.exported_ids);
        trans_exported_ids = (uu___578_55960.trans_exported_ids);
        includes = (uu___578_55960.includes);
        sigaccum = (uu___578_55960.sigaccum);
        sigmap = (uu___578_55960.sigmap);
        iface = (uu___578_55960.iface);
        admitted_iface = (uu___578_55960.admitted_iface);
        expect_typ = (uu___578_55960.expect_typ);
        docs = (uu___578_55960.docs);
        remaining_iface_decls = (uu___578_55960.remaining_iface_decls);
        syntax_only = (uu___578_55960.syntax_only);
        ds_hooks = (uu___578_55960.ds_hooks);
        dep_graph = (uu___578_55960.dep_graph)
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
      let uu____55984 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____56018  ->
                match uu____56018 with
                | (m,uu____56027) -> FStar_Ident.lid_equals l m))
         in
      match uu____55984 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____56044,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____56078 =
          FStar_List.partition
            (fun uu____56108  ->
               match uu____56108 with
               | (m,uu____56117) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____56078 with
        | (uu____56122,rest) ->
            let uu___603_56156 = env  in
            {
              curmodule = (uu___603_56156.curmodule);
              curmonad = (uu___603_56156.curmonad);
              modules = (uu___603_56156.modules);
              scope_mods = (uu___603_56156.scope_mods);
              exported_ids = (uu___603_56156.exported_ids);
              trans_exported_ids = (uu___603_56156.trans_exported_ids);
              includes = (uu___603_56156.includes);
              sigaccum = (uu___603_56156.sigaccum);
              sigmap = (uu___603_56156.sigmap);
              iface = (uu___603_56156.iface);
              admitted_iface = (uu___603_56156.admitted_iface);
              expect_typ = (uu___603_56156.expect_typ);
              docs = (uu___603_56156.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___603_56156.syntax_only);
              ds_hooks = (uu___603_56156.ds_hooks);
              dep_graph = (uu___603_56156.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____56185 = current_module env  in qual uu____56185 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____56187 =
            let uu____56188 = current_module env  in qual uu____56188 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____56187
            id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___613_56209 = env  in
      {
        curmodule = (uu___613_56209.curmodule);
        curmonad = (uu___613_56209.curmonad);
        modules = (uu___613_56209.modules);
        scope_mods = (uu___613_56209.scope_mods);
        exported_ids = (uu___613_56209.exported_ids);
        trans_exported_ids = (uu___613_56209.trans_exported_ids);
        includes = (uu___613_56209.includes);
        sigaccum = (uu___613_56209.sigaccum);
        sigmap = (uu___613_56209.sigmap);
        iface = (uu___613_56209.iface);
        admitted_iface = (uu___613_56209.admitted_iface);
        expect_typ = (uu___613_56209.expect_typ);
        docs = (uu___613_56209.docs);
        remaining_iface_decls = (uu___613_56209.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___613_56209.ds_hooks);
        dep_graph = (uu___613_56209.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___618_56227 = env  in
      {
        curmodule = (uu___618_56227.curmodule);
        curmonad = (uu___618_56227.curmonad);
        modules = (uu___618_56227.modules);
        scope_mods = (uu___618_56227.scope_mods);
        exported_ids = (uu___618_56227.exported_ids);
        trans_exported_ids = (uu___618_56227.trans_exported_ids);
        includes = (uu___618_56227.includes);
        sigaccum = (uu___618_56227.sigaccum);
        sigmap = (uu___618_56227.sigmap);
        iface = (uu___618_56227.iface);
        admitted_iface = (uu___618_56227.admitted_iface);
        expect_typ = (uu___618_56227.expect_typ);
        docs = (uu___618_56227.docs);
        remaining_iface_decls = (uu___618_56227.remaining_iface_decls);
        syntax_only = (uu___618_56227.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___618_56227.dep_graph)
      }
  
let new_sigmap : 'Auu____56233 . unit -> 'Auu____56233 FStar_Util.smap =
  fun uu____56240  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____56248 = new_sigmap ()  in
    let uu____56253 = new_sigmap ()  in
    let uu____56258 = new_sigmap ()  in
    let uu____56269 = new_sigmap ()  in
    let uu____56282 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____56248;
      trans_exported_ids = uu____56253;
      includes = uu____56258;
      sigaccum = [];
      sigmap = uu____56269;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____56282;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___625_56316 = env  in
      {
        curmodule = (uu___625_56316.curmodule);
        curmonad = (uu___625_56316.curmonad);
        modules = (uu___625_56316.modules);
        scope_mods = (uu___625_56316.scope_mods);
        exported_ids = (uu___625_56316.exported_ids);
        trans_exported_ids = (uu___625_56316.trans_exported_ids);
        includes = (uu___625_56316.includes);
        sigaccum = (uu___625_56316.sigaccum);
        sigmap = (uu___625_56316.sigmap);
        iface = (uu___625_56316.iface);
        admitted_iface = (uu___625_56316.admitted_iface);
        expect_typ = (uu___625_56316.expect_typ);
        docs = (uu___625_56316.docs);
        remaining_iface_decls = (uu___625_56316.remaining_iface_decls);
        syntax_only = (uu___625_56316.syntax_only);
        ds_hooks = (uu___625_56316.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____56344  ->
         match uu____56344 with
         | (m,uu____56351) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___634_56364 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___634_56364.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___637_56365 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index =
          (uu___637_56365.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___637_56365.FStar_Syntax_Syntax.sort)
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
      (fun uu____56468  ->
         match uu____56468 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____56499 =
                 let uu____56500 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____56500 dd dq  in
               FStar_Pervasives_Native.Some uu____56499
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____56540 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____56578 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____56599 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___421_56629  ->
      match uu___421_56629 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____56648 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____56648 cont_t) -> 'Auu____56648 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____56685 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____56685
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____56701  ->
                   match uu____56701 with
                   | (f,uu____56709) ->
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
  fun uu___422_56783  ->
    match uu___422_56783 with
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
              let rec aux uu___423_56859 =
                match uu___423_56859 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____56872 = get_exported_id_set env mname  in
                      match uu____56872 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____56899 = mex eikind  in
                            FStar_ST.op_Bang uu____56899  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____57014 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____57014 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____57091 = qual modul id1  in
                        find_in_module uu____57091
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____57096 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___424_57105  ->
    match uu___424_57105 with
    | Exported_id_field  -> true
    | uu____57108 -> false
  
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
                  let check_local_binding_id uu___425_57232 =
                    match uu___425_57232 with
                    | (id',uu____57235) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___426_57243 =
                    match uu___426_57243 with
                    | (id',uu____57246,uu____57247) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____57252 = current_module env  in
                    FStar_Ident.ids_of_lid uu____57252  in
                  let proc uu___427_57260 =
                    match uu___427_57260 with
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
                        let uu____57269 = FStar_Ident.lid_of_ids curmod_ns
                           in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____57269 id1
                    | uu____57274 -> Cont_ignore  in
                  let rec aux uu___428_57284 =
                    match uu___428_57284 with
                    | a::q ->
                        let uu____57293 = proc a  in
                        option_of_cont (fun uu____57297  -> aux q)
                          uu____57293
                    | [] ->
                        let uu____57298 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____57302  -> FStar_Pervasives_Native.None)
                          uu____57298
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____57310 .
    FStar_Range.range ->
      ('Auu____57310 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____57324  -> match uu____57324 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____57342 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____57342)
          -> 'Auu____57342 -> 'Auu____57342
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____57383 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____57383 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____57427 = unmangleOpName id1  in
      match uu____57427 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____57433 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____57439 =
                 found_local_binding id1.FStar_Ident.idRange r  in
               Cont_ok uu____57439) (fun uu____57441  -> Cont_fail)
            (fun uu____57443  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____57450  -> fun uu____57451  -> Cont_fail)
                 Cont_ignore)
            (fun uu____57459  -> fun uu____57460  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____57534 ->
                let lid = qualify env id1  in
                let uu____57536 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____57536 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____57564 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____57564
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____57588 = current_module env  in qual uu____57588 id1
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
        let rec aux uu___429_57660 =
          match uu___429_57660 with
          | [] ->
              let uu____57665 = module_is_defined env lid  in
              if uu____57665
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____57677 =
                  let uu____57678 = FStar_Ident.path_of_lid ns  in
                  let uu____57682 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____57678 uu____57682  in
                let uu____57687 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____57677 uu____57687  in
              let uu____57688 = module_is_defined env new_lid  in
              if uu____57688
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____57697 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____57707::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____57727 =
          let uu____57729 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____57729  in
        if uu____57727
        then
          let uu____57731 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____57731
           then ()
           else
             (let uu____57736 =
                let uu____57742 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____57742)
                 in
              let uu____57746 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____57736 uu____57746))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____57760 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____57764 = resolve_module_name env modul_orig true  in
          (match uu____57764 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____57769 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___430_57792  ->
             match uu___430_57792 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____57796 -> false) env.scope_mods
  
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
                 let uu____57925 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____57925
                   (FStar_Util.map_option
                      (fun uu____57975  ->
                         match uu____57975 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____58045 = aux ns_rev_prefix ns_last_id  in
              (match uu____58045 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____58108 =
            let uu____58111 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____58111 true  in
          match uu____58108 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____58126 -> do_shorten env ids
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
                  | uu____58247::uu____58248 ->
                      let uu____58251 =
                        let uu____58254 =
                          let uu____58255 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____58256 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____58255 uu____58256
                           in
                        resolve_module_name env uu____58254 true  in
                      (match uu____58251 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____58261 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____58265  ->
                                FStar_Pervasives_Native.None) uu____58261)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___431_58289  ->
      match uu___431_58289 with
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
              let uu____58410 = k_global_def lid1 def  in
              cont_of_option k uu____58410  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____58446 = k_local_binding l  in
                 cont_of_option Cont_fail uu____58446)
              (fun r  ->
                 let uu____58452 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____58452)
              (fun uu____58456  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____58467,uu____58468,uu____58469,l,uu____58471,uu____58472) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___432_58485  ->
               match uu___432_58485 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____58488,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____58500 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____58506,uu____58507,uu____58508) -> FStar_Pervasives_Native.None
    | uu____58509 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____58525 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____58533 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____58533
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____58525 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____58556 =
         let uu____58557 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____58557  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____58556) &&
        (let uu____58565 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____58565 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____58582 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___433_58589  ->
                     match uu___433_58589 with
                     | FStar_Syntax_Syntax.Projector uu____58591 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____58597 -> true
                     | uu____58599 -> false)))
           in
        if uu____58582
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____58604 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___434_58610  ->
                 match uu___434_58610 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____58613 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___435_58619  ->
                    match uu___435_58619 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____58622 -> false)))
             &&
             (let uu____58625 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___436_58631  ->
                        match uu___436_58631 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____58634 -> false))
                 in
              Prims.op_Negation uu____58625))
         in
      if uu____58604 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___439_58686 =
            match uu___439_58686 with
            | (uu____58694,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____58698) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____58703 ->
                     let uu____58720 =
                       let uu____58721 =
                         let uu____58728 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____58728, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58721  in
                     FStar_Pervasives_Native.Some uu____58720
                 | FStar_Syntax_Syntax.Sig_datacon uu____58731 ->
                     let uu____58747 =
                       let uu____58748 =
                         let uu____58755 =
                           let uu____58756 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____58756
                            in
                         (uu____58755, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58748  in
                     FStar_Pervasives_Native.Some uu____58747
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____58761,lbs),uu____58763) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____58775 =
                       let uu____58776 =
                         let uu____58783 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____58783, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58776  in
                     FStar_Pervasives_Native.Some uu____58775
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____58787,uu____58788) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____58792 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___437_58798  ->
                                  match uu___437_58798 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____58801 -> false)))
                        in
                     if uu____58792
                     then
                       let lid2 =
                         let uu____58807 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____58807  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____58809 =
                         FStar_Util.find_map quals
                           (fun uu___438_58814  ->
                              match uu___438_58814 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____58818 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____58809 with
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
                        | uu____58827 ->
                            let uu____58830 =
                              let uu____58831 =
                                let uu____58838 =
                                  let uu____58839 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____58839
                                   in
                                (uu____58838,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____58831  in
                            FStar_Pervasives_Native.Some uu____58830)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____58847 =
                       let uu____58848 =
                         let uu____58853 =
                           let uu____58854 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____58854
                            in
                         (se, uu____58853)  in
                       Eff_name uu____58848  in
                     FStar_Pervasives_Native.Some uu____58847
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____58856 =
                       let uu____58857 =
                         let uu____58862 =
                           let uu____58863 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____58863
                            in
                         (se, uu____58862)  in
                       Eff_name uu____58857  in
                     FStar_Pervasives_Native.Some uu____58856
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____58864 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____58883 =
                       let uu____58884 =
                         let uu____58891 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____58891, [])  in
                       Term_name uu____58884  in
                     FStar_Pervasives_Native.Some uu____58883
                 | uu____58895 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____58913 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____58913 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____58929 =
            match uu____58929 with
            | (id1,l,dd) ->
                let uu____58941 =
                  let uu____58942 =
                    let uu____58949 =
                      let uu____58950 =
                        let uu____58951 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____58951  in
                      FStar_Syntax_Syntax.fvar uu____58950 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____58949, [])  in
                  Term_name uu____58942  in
                FStar_Pervasives_Native.Some uu____58941
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____58959 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____58959 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____58967 -> FStar_Pervasives_Native.None)
            | uu____58970 -> FStar_Pervasives_Native.None  in
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
        let uu____59008 = try_lookup_name true exclude_interf env lid  in
        match uu____59008 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____59024 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59044 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59044 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____59059 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59085 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59085 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____59101;
             FStar_Syntax_Syntax.sigquals = uu____59102;
             FStar_Syntax_Syntax.sigmeta = uu____59103;
             FStar_Syntax_Syntax.sigattrs = uu____59104;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____59123;
             FStar_Syntax_Syntax.sigquals = uu____59124;
             FStar_Syntax_Syntax.sigmeta = uu____59125;
             FStar_Syntax_Syntax.sigattrs = uu____59126;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____59144,uu____59145,uu____59146,uu____59147,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____59149;
             FStar_Syntax_Syntax.sigquals = uu____59150;
             FStar_Syntax_Syntax.sigmeta = uu____59151;
             FStar_Syntax_Syntax.sigattrs = uu____59152;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____59174 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59200 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59200 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____59210;
             FStar_Syntax_Syntax.sigquals = uu____59211;
             FStar_Syntax_Syntax.sigmeta = uu____59212;
             FStar_Syntax_Syntax.sigattrs = uu____59213;_},uu____59214)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____59224;
             FStar_Syntax_Syntax.sigquals = uu____59225;
             FStar_Syntax_Syntax.sigmeta = uu____59226;
             FStar_Syntax_Syntax.sigattrs = uu____59227;_},uu____59228)
          -> FStar_Pervasives_Native.Some ne
      | uu____59237 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____59256 = try_lookup_effect_name env lid  in
      match uu____59256 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____59261 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59276 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59276 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____59286,uu____59287,uu____59288,uu____59289);
             FStar_Syntax_Syntax.sigrng = uu____59290;
             FStar_Syntax_Syntax.sigquals = uu____59291;
             FStar_Syntax_Syntax.sigmeta = uu____59292;
             FStar_Syntax_Syntax.sigattrs = uu____59293;_},uu____59294)
          ->
          let rec aux new_name =
            let uu____59315 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____59315 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____59336) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____59347 =
                       let uu____59348 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____59348
                        in
                     FStar_Pervasives_Native.Some uu____59347
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____59350 =
                       let uu____59351 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____59351
                        in
                     FStar_Pervasives_Native.Some uu____59350
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____59352,uu____59353,uu____59354,cmp,uu____59356) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____59362 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____59363,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____59369 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___440_59408 =
        match uu___440_59408 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____59418,uu____59419,uu____59420);
             FStar_Syntax_Syntax.sigrng = uu____59421;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____59423;
             FStar_Syntax_Syntax.sigattrs = uu____59424;_},uu____59425)
            -> FStar_Pervasives_Native.Some quals
        | uu____59434 -> FStar_Pervasives_Native.None  in
      let uu____59442 =
        resolve_in_open_namespaces' env lid
          (fun uu____59450  -> FStar_Pervasives_Native.None)
          (fun uu____59454  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____59442 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____59464 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____59482 =
        FStar_List.tryFind
          (fun uu____59497  ->
             match uu____59497 with
             | (mlid,modul) ->
                 let uu____59505 = FStar_Ident.path_of_lid mlid  in
                 uu____59505 = path) env.modules
         in
      match uu____59482 with
      | FStar_Pervasives_Native.Some (uu____59508,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___441_59548 =
        match uu___441_59548 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____59556,lbs),uu____59558);
             FStar_Syntax_Syntax.sigrng = uu____59559;
             FStar_Syntax_Syntax.sigquals = uu____59560;
             FStar_Syntax_Syntax.sigmeta = uu____59561;
             FStar_Syntax_Syntax.sigattrs = uu____59562;_},uu____59563)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____59581 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____59581
        | uu____59582 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____59589  -> FStar_Pervasives_Native.None)
        (fun uu____59591  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___442_59624 =
        match uu___442_59624 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____59635);
             FStar_Syntax_Syntax.sigrng = uu____59636;
             FStar_Syntax_Syntax.sigquals = uu____59637;
             FStar_Syntax_Syntax.sigmeta = uu____59638;
             FStar_Syntax_Syntax.sigattrs = uu____59639;_},uu____59640)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____59666 -> FStar_Pervasives_Native.None)
        | uu____59673 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____59684  -> FStar_Pervasives_Native.None)
        (fun uu____59688  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____59748 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____59748 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____59773 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____59811) ->
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
      let uu____59869 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____59869 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59901 = try_lookup_lid env l  in
      match uu____59901 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____59907 =
            let uu____59908 = FStar_Syntax_Subst.compress e  in
            uu____59908.FStar_Syntax_Syntax.n  in
          (match uu____59907 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____59914 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____59926 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____59926 with
      | (uu____59936,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____59957 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____59961 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____59961 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____59966 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___1304_59997 = env  in
        {
          curmodule = (uu___1304_59997.curmodule);
          curmonad = (uu___1304_59997.curmonad);
          modules = (uu___1304_59997.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___1304_59997.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___1304_59997.sigaccum);
          sigmap = (uu___1304_59997.sigmap);
          iface = (uu___1304_59997.iface);
          admitted_iface = (uu___1304_59997.admitted_iface);
          expect_typ = (uu___1304_59997.expect_typ);
          docs = (uu___1304_59997.docs);
          remaining_iface_decls = (uu___1304_59997.remaining_iface_decls);
          syntax_only = (uu___1304_59997.syntax_only);
          ds_hooks = (uu___1304_59997.ds_hooks);
          dep_graph = (uu___1304_59997.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____60013 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____60013 drop_attributes
  
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
               (uu____60083,uu____60084,uu____60085);
             FStar_Syntax_Syntax.sigrng = uu____60086;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____60088;
             FStar_Syntax_Syntax.sigattrs = uu____60089;_},uu____60090)
            ->
            let uu____60097 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___443_60103  ->
                      match uu___443_60103 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____60106 -> false))
               in
            if uu____60097
            then
              let uu____60111 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____60111
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____60114;
             FStar_Syntax_Syntax.sigrng = uu____60115;
             FStar_Syntax_Syntax.sigquals = uu____60116;
             FStar_Syntax_Syntax.sigmeta = uu____60117;
             FStar_Syntax_Syntax.sigattrs = uu____60118;_},uu____60119)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____60145 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____60145
        | uu____60146 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____60153  -> FStar_Pervasives_Native.None)
        (fun uu____60155  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___444_60190 =
        match uu___444_60190 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____60200,uu____60201,uu____60202,uu____60203,datas,uu____60205);
             FStar_Syntax_Syntax.sigrng = uu____60206;
             FStar_Syntax_Syntax.sigquals = uu____60207;
             FStar_Syntax_Syntax.sigmeta = uu____60208;
             FStar_Syntax_Syntax.sigattrs = uu____60209;_},uu____60210)
            -> FStar_Pervasives_Native.Some datas
        | uu____60227 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____60238  -> FStar_Pervasives_Native.None)
        (fun uu____60242  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____60321 =
    let uu____60322 =
      let uu____60327 =
        let uu____60330 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____60330  in
      let uu____60386 = FStar_ST.op_Bang record_cache  in uu____60327 ::
        uu____60386
       in
    FStar_ST.op_Colon_Equals record_cache uu____60322  in
  let pop1 uu____60496 =
    let uu____60497 =
      let uu____60502 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____60502  in
    FStar_ST.op_Colon_Equals record_cache uu____60497  in
  let snapshot1 uu____60617 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____60685 =
    let uu____60686 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____60686  in
  let insert r =
    let uu____60748 =
      let uu____60753 = let uu____60756 = peek1 ()  in r :: uu____60756  in
      let uu____60759 =
        let uu____60764 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____60764  in
      uu____60753 :: uu____60759  in
    FStar_ST.op_Colon_Equals record_cache uu____60748  in
  let filter1 uu____60876 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____60885 =
      let uu____60890 =
        let uu____60895 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____60895  in
      filtered :: uu____60890  in
    FStar_ST.op_Colon_Equals record_cache uu____60885  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____61887) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___445_61906  ->
                   match uu___445_61906 with
                   | FStar_Syntax_Syntax.RecordType uu____61908 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____61918 ->
                       true
                   | uu____61928 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___446_61953  ->
                      match uu___446_61953 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____61956,uu____61957,uu____61958,uu____61959,uu____61960);
                          FStar_Syntax_Syntax.sigrng = uu____61961;
                          FStar_Syntax_Syntax.sigquals = uu____61962;
                          FStar_Syntax_Syntax.sigmeta = uu____61963;
                          FStar_Syntax_Syntax.sigattrs = uu____61964;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____61975 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___447_62011  ->
                    match uu___447_62011 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____62015,uu____62016,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____62018;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____62020;
                        FStar_Syntax_Syntax.sigattrs = uu____62021;_} ->
                        let uu____62032 =
                          let uu____62033 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____62033  in
                        (match uu____62032 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____62039,t,uu____62041,uu____62042,uu____62043);
                             FStar_Syntax_Syntax.sigrng = uu____62044;
                             FStar_Syntax_Syntax.sigquals = uu____62045;
                             FStar_Syntax_Syntax.sigmeta = uu____62046;
                             FStar_Syntax_Syntax.sigattrs = uu____62047;_} ->
                             let uu____62058 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____62058 with
                              | (formals,uu____62074) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____62128  ->
                                            match uu____62128 with
                                            | (x,q) ->
                                                let uu____62141 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____62141
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____62196  ->
                                            match uu____62196 with
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
                                  ((let uu____62220 =
                                      let uu____62223 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____62223
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____62220);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____62326 =
                                            match uu____62326 with
                                            | (id1,uu____62332) ->
                                                let modul =
                                                  let uu____62335 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____62335.FStar_Ident.str
                                                   in
                                                let uu____62336 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____62336 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____62370 =
                                                         let uu____62371 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____62371
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____62370);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____62460
                                                               =
                                                               let uu____62461
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____62461.FStar_Ident.ident
                                                                in
                                                             uu____62460.FStar_Ident.idText
                                                              in
                                                           let uu____62463 =
                                                             let uu____62464
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____62464
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____62463))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____62560 -> ())
                    | uu____62561 -> ()))
        | uu____62562 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____62584 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____62584 with
        | (ns,id1) ->
            let uu____62601 = peek_record_cache ()  in
            FStar_Util.find_map uu____62601
              (fun record  ->
                 let uu____62607 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____62613  -> FStar_Pervasives_Native.None)
                   uu____62607)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____62615  -> Cont_ignore) (fun uu____62617  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____62623 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____62623)
        (fun k  -> fun uu____62629  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____62645 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____62645 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____62651 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____62671 = try_lookup_record_by_field_name env lid  in
        match uu____62671 with
        | FStar_Pervasives_Native.Some record' when
            let uu____62676 =
              let uu____62678 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____62678  in
            let uu____62679 =
              let uu____62681 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____62681  in
            uu____62676 = uu____62679 ->
            let uu____62683 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____62687  -> Cont_ok ())
               in
            (match uu____62683 with
             | Cont_ok uu____62689 -> true
             | uu____62691 -> false)
        | uu____62695 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____62717 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____62717 with
      | FStar_Pervasives_Native.Some r ->
          let uu____62728 =
            let uu____62734 =
              let uu____62735 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____62736 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____62735 uu____62736  in
            (uu____62734, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____62728
      | uu____62743 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____62772  ->
    let uu____62773 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____62773
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____62805  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___448_62818  ->
      match uu___448_62818 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___449_62878 =
            match uu___449_62878 with
            | Rec_binding uu____62880 -> true
            | uu____62882 -> false  in
          let this_env =
            let uu___1530_62885 = env  in
            let uu____62886 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1530_62885.curmodule);
              curmonad = (uu___1530_62885.curmonad);
              modules = (uu___1530_62885.modules);
              scope_mods = uu____62886;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1530_62885.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1530_62885.sigaccum);
              sigmap = (uu___1530_62885.sigmap);
              iface = (uu___1530_62885.iface);
              admitted_iface = (uu___1530_62885.admitted_iface);
              expect_typ = (uu___1530_62885.expect_typ);
              docs = (uu___1530_62885.docs);
              remaining_iface_decls = (uu___1530_62885.remaining_iface_decls);
              syntax_only = (uu___1530_62885.syntax_only);
              ds_hooks = (uu___1530_62885.ds_hooks);
              dep_graph = (uu___1530_62885.dep_graph)
            }  in
          let uu____62889 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____62889 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____62906 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1538_62931 = env  in
      {
        curmodule = (uu___1538_62931.curmodule);
        curmonad = (uu___1538_62931.curmonad);
        modules = (uu___1538_62931.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1538_62931.exported_ids);
        trans_exported_ids = (uu___1538_62931.trans_exported_ids);
        includes = (uu___1538_62931.includes);
        sigaccum = (uu___1538_62931.sigaccum);
        sigmap = (uu___1538_62931.sigmap);
        iface = (uu___1538_62931.iface);
        admitted_iface = (uu___1538_62931.admitted_iface);
        expect_typ = (uu___1538_62931.expect_typ);
        docs = (uu___1538_62931.docs);
        remaining_iface_decls = (uu___1538_62931.remaining_iface_decls);
        syntax_only = (uu___1538_62931.syntax_only);
        ds_hooks = (uu___1538_62931.ds_hooks);
        dep_graph = (uu___1538_62931.dep_graph)
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
        let uu____62965 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____62965
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____62972 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____62972)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____63016) ->
                let uu____63024 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____63024 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____63029 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____63029
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____63038 =
            let uu____63044 =
              let uu____63046 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____63046 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____63044)  in
          let uu____63050 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____63038 uu____63050  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____63059 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____63072 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____63083 -> (false, true)
            | uu____63096 -> (false, false)  in
          match uu____63059 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____63110 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____63116 =
                       let uu____63118 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____63118  in
                     if uu____63116
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____63110 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____63126 ->
                   (extract_record env globals s;
                    (let uu___1579_63152 = env  in
                     {
                       curmodule = (uu___1579_63152.curmodule);
                       curmonad = (uu___1579_63152.curmonad);
                       modules = (uu___1579_63152.modules);
                       scope_mods = (uu___1579_63152.scope_mods);
                       exported_ids = (uu___1579_63152.exported_ids);
                       trans_exported_ids =
                         (uu___1579_63152.trans_exported_ids);
                       includes = (uu___1579_63152.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1579_63152.sigmap);
                       iface = (uu___1579_63152.iface);
                       admitted_iface = (uu___1579_63152.admitted_iface);
                       expect_typ = (uu___1579_63152.expect_typ);
                       docs = (uu___1579_63152.docs);
                       remaining_iface_decls =
                         (uu___1579_63152.remaining_iface_decls);
                       syntax_only = (uu___1579_63152.syntax_only);
                       ds_hooks = (uu___1579_63152.ds_hooks);
                       dep_graph = (uu___1579_63152.dep_graph)
                     })))
           in
        let env2 =
          let uu___1582_63154 = env1  in
          let uu____63155 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1582_63154.curmodule);
            curmonad = (uu___1582_63154.curmonad);
            modules = (uu___1582_63154.modules);
            scope_mods = uu____63155;
            exported_ids = (uu___1582_63154.exported_ids);
            trans_exported_ids = (uu___1582_63154.trans_exported_ids);
            includes = (uu___1582_63154.includes);
            sigaccum = (uu___1582_63154.sigaccum);
            sigmap = (uu___1582_63154.sigmap);
            iface = (uu___1582_63154.iface);
            admitted_iface = (uu___1582_63154.admitted_iface);
            expect_typ = (uu___1582_63154.expect_typ);
            docs = (uu___1582_63154.docs);
            remaining_iface_decls = (uu___1582_63154.remaining_iface_decls);
            syntax_only = (uu___1582_63154.syntax_only);
            ds_hooks = (uu___1582_63154.ds_hooks);
            dep_graph = (uu___1582_63154.dep_graph)
          }  in
        let uu____63203 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____63229) ->
              let uu____63238 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____63238)
          | uu____63265 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____63203 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____63324  ->
                     match uu____63324 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____63346 =
                                    let uu____63349 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____63349
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____63346);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____63444 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____63444.FStar_Ident.str  in
                                      ((let uu____63446 =
                                          get_exported_id_set env3 modul  in
                                        match uu____63446 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____63479 =
                                              let uu____63480 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____63480
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____63479
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
                let uu___1607_63581 = env3  in
                let uu____63582 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1607_63581.curmodule);
                  curmonad = (uu___1607_63581.curmonad);
                  modules = (uu___1607_63581.modules);
                  scope_mods = uu____63582;
                  exported_ids = (uu___1607_63581.exported_ids);
                  trans_exported_ids = (uu___1607_63581.trans_exported_ids);
                  includes = (uu___1607_63581.includes);
                  sigaccum = (uu___1607_63581.sigaccum);
                  sigmap = (uu___1607_63581.sigmap);
                  iface = (uu___1607_63581.iface);
                  admitted_iface = (uu___1607_63581.admitted_iface);
                  expect_typ = (uu___1607_63581.expect_typ);
                  docs = (uu___1607_63581.docs);
                  remaining_iface_decls =
                    (uu___1607_63581.remaining_iface_decls);
                  syntax_only = (uu___1607_63581.syntax_only);
                  ds_hooks = (uu___1607_63581.ds_hooks);
                  dep_graph = (uu___1607_63581.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____63665 =
        let uu____63670 = resolve_module_name env ns false  in
        match uu____63670 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____63685 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____63703  ->
                      match uu____63703 with
                      | (m,uu____63710) ->
                          let uu____63711 =
                            let uu____63713 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____63713 "."  in
                          let uu____63716 =
                            let uu____63718 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____63718 "."  in
                          FStar_Util.starts_with uu____63711 uu____63716))
               in
            if uu____63685
            then (ns, Open_namespace)
            else
              (let uu____63728 =
                 let uu____63734 =
                   let uu____63736 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____63736
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____63734)  in
               let uu____63740 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____63728 uu____63740)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____63665 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____63762 = resolve_module_name env ns false  in
      match uu____63762 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____63772 = current_module env1  in
              uu____63772.FStar_Ident.str  in
            (let uu____63774 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____63774 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____63798 =
                   let uu____63801 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____63801
                    in
                 FStar_ST.op_Colon_Equals incl uu____63798);
            (match () with
             | () ->
                 let uu____63894 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____63894 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____63914 =
                          let uu____64011 = get_exported_id_set env1 curmod
                             in
                          let uu____64058 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____64011, uu____64058)  in
                        match uu____63914 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____64474 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____64474  in
                              let ex = cur_exports k  in
                              (let uu____64649 =
                                 let uu____64653 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____64653 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____64649);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____64850 =
                                     let uu____64854 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____64854 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____64850)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____64987 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____65089 =
                        let uu____65095 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____65095)
                         in
                      let uu____65099 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____65089 uu____65099))))
      | uu____65100 ->
          let uu____65103 =
            let uu____65109 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____65109)  in
          let uu____65113 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____65103 uu____65113
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____65130 = module_is_defined env l  in
        if uu____65130
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____65137 =
             let uu____65143 =
               let uu____65145 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____65145  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____65143)  in
           let uu____65149 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____65137 uu____65149)
  
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
            ((let uu____65172 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____65172 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____65176 = FStar_Ident.range_of_lid l  in
                  let uu____65177 =
                    let uu____65183 =
                      let uu____65185 = FStar_Ident.string_of_lid l  in
                      let uu____65187 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____65189 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____65185 uu____65187 uu____65189
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____65183)  in
                  FStar_Errors.log_issue uu____65176 uu____65177);
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
                      let uu____65235 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____65235 ->
                      let uu____65240 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____65240 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____65255;
                              FStar_Syntax_Syntax.sigrng = uu____65256;
                              FStar_Syntax_Syntax.sigquals = uu____65257;
                              FStar_Syntax_Syntax.sigmeta = uu____65258;
                              FStar_Syntax_Syntax.sigattrs = uu____65259;_},uu____65260)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____65278;
                              FStar_Syntax_Syntax.sigrng = uu____65279;
                              FStar_Syntax_Syntax.sigquals = uu____65280;
                              FStar_Syntax_Syntax.sigmeta = uu____65281;
                              FStar_Syntax_Syntax.sigattrs = uu____65282;_},uu____65283)
                           -> lids
                       | uu____65311 ->
                           ((let uu____65320 =
                               let uu____65322 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____65322  in
                             if uu____65320
                             then
                               let uu____65325 = FStar_Ident.range_of_lid l
                                  in
                               let uu____65326 =
                                 let uu____65332 =
                                   let uu____65334 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____65334
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____65332)
                                  in
                               FStar_Errors.log_issue uu____65325 uu____65326
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1710_65351 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1710_65351.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1710_65351.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1710_65351.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1710_65351.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____65353 -> lids) [])
         in
      let uu___1715_65354 = m  in
      let uu____65355 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____65365,uu____65366) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1724_65369 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1724_65369.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1724_65369.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1724_65369.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1724_65369.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____65370 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1715_65354.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____65355;
        FStar_Syntax_Syntax.exports =
          (uu___1715_65354.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1715_65354.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____65394) ->
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
                                (lid,uu____65415,uu____65416,uu____65417,uu____65418,uu____65419)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____65435,uu____65436)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____65453 =
                                        let uu____65460 =
                                          let uu____65461 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____65462 =
                                            let uu____65469 =
                                              let uu____65470 =
                                                let uu____65485 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____65485)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____65470
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____65469
                                             in
                                          uu____65462
                                            FStar_Pervasives_Native.None
                                            uu____65461
                                           in
                                        (lid, univ_names, uu____65460)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____65453
                                       in
                                    let se2 =
                                      let uu___1756_65502 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1756_65502.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1756_65502.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1756_65502.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____65512 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____65516,uu____65517) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____65526,lbs),uu____65528)
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
                             let uu____65546 =
                               let uu____65548 =
                                 let uu____65549 =
                                   let uu____65552 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____65552.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____65549.FStar_Syntax_Syntax.v  in
                               uu____65548.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____65546))
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
                               let uu____65569 =
                                 let uu____65572 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____65572.FStar_Syntax_Syntax.fv_name  in
                               uu____65569.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1779_65577 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1779_65577.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1779_65577.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1779_65577.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____65587 -> ()));
      (let curmod =
         let uu____65590 = current_module env  in uu____65590.FStar_Ident.str
          in
       (let uu____65592 =
          let uu____65689 = get_exported_id_set env curmod  in
          let uu____65736 = get_trans_exported_id_set env curmod  in
          (uu____65689, uu____65736)  in
        match uu____65592 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____66155 = cur_ex eikind  in
                FStar_ST.op_Bang uu____66155  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____66345 =
                let uu____66349 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____66349  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____66345  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____66482 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1797_66580 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1797_66580.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1797_66580.exported_ids);
                    trans_exported_ids = (uu___1797_66580.trans_exported_ids);
                    includes = (uu___1797_66580.includes);
                    sigaccum = [];
                    sigmap = (uu___1797_66580.sigmap);
                    iface = (uu___1797_66580.iface);
                    admitted_iface = (uu___1797_66580.admitted_iface);
                    expect_typ = (uu___1797_66580.expect_typ);
                    docs = (uu___1797_66580.docs);
                    remaining_iface_decls =
                      (uu___1797_66580.remaining_iface_decls);
                    syntax_only = (uu___1797_66580.syntax_only);
                    ds_hooks = (uu___1797_66580.ds_hooks);
                    dep_graph = (uu___1797_66580.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____66618  ->
         push_record_cache ();
         (let uu____66621 =
            let uu____66624 = FStar_ST.op_Bang stack  in env :: uu____66624
             in
          FStar_ST.op_Colon_Equals stack uu____66621);
         (let uu___1803_66673 = env  in
          let uu____66674 = FStar_Util.smap_copy env.exported_ids  in
          let uu____66679 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____66684 = FStar_Util.smap_copy env.includes  in
          let uu____66695 = FStar_Util.smap_copy env.sigmap  in
          let uu____66708 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1803_66673.curmodule);
            curmonad = (uu___1803_66673.curmonad);
            modules = (uu___1803_66673.modules);
            scope_mods = (uu___1803_66673.scope_mods);
            exported_ids = uu____66674;
            trans_exported_ids = uu____66679;
            includes = uu____66684;
            sigaccum = (uu___1803_66673.sigaccum);
            sigmap = uu____66695;
            iface = (uu___1803_66673.iface);
            admitted_iface = (uu___1803_66673.admitted_iface);
            expect_typ = (uu___1803_66673.expect_typ);
            docs = uu____66708;
            remaining_iface_decls = (uu___1803_66673.remaining_iface_decls);
            syntax_only = (uu___1803_66673.syntax_only);
            ds_hooks = (uu___1803_66673.ds_hooks);
            dep_graph = (uu___1803_66673.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____66716  ->
    FStar_Util.atomically
      (fun uu____66723  ->
         let uu____66724 = FStar_ST.op_Bang stack  in
         match uu____66724 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____66779 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____66826 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____66830 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____66872 = FStar_Util.smap_try_find sm' k  in
              match uu____66872 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1838_66903 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1838_66903.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1838_66903.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1838_66903.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1838_66903.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____66904 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____66912 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____66939 = finish env modul1  in (uu____66939, modul1)
  
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
      let uu____67041 =
        let uu____67045 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____67045  in
      FStar_Util.set_elements uu____67041  in
    let fields =
      let uu____67161 =
        let uu____67165 = e Exported_id_field  in
        FStar_ST.op_Bang uu____67165  in
      FStar_Util.set_elements uu____67161  in
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
          let uu____67321 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____67321  in
        let fields =
          let uu____67335 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____67335  in
        (fun uu___450_67343  ->
           match uu___450_67343 with
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
  'Auu____67480 .
    'Auu____67480 Prims.list FStar_Pervasives_Native.option ->
      'Auu____67480 Prims.list FStar_ST.ref
  =
  fun uu___451_67493  ->
    match uu___451_67493 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____67536 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____67536 as_exported_ids  in
      let uu____67542 = as_ids_opt env.exported_ids  in
      let uu____67545 = as_ids_opt env.trans_exported_ids  in
      let uu____67548 =
        let uu____67553 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____67553 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____67542;
        mii_trans_exported_ids = uu____67545;
        mii_includes = uu____67548
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
                let uu____67675 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____67675 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___452_67697 =
                  match uu___452_67697 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____67709  ->
                     match uu____67709 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____67735 =
                    let uu____67740 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____67740, Open_namespace)  in
                  [uu____67735]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____67771 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____67771);
              (match () with
               | () ->
                   ((let uu____67798 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____67798);
                    (match () with
                     | () ->
                         ((let uu____67825 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____67825);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1908_67857 = env1  in
                                 let uu____67858 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1908_67857.curmonad);
                                   modules = (uu___1908_67857.modules);
                                   scope_mods = uu____67858;
                                   exported_ids =
                                     (uu___1908_67857.exported_ids);
                                   trans_exported_ids =
                                     (uu___1908_67857.trans_exported_ids);
                                   includes = (uu___1908_67857.includes);
                                   sigaccum = (uu___1908_67857.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1908_67857.expect_typ);
                                   docs = (uu___1908_67857.docs);
                                   remaining_iface_decls =
                                     (uu___1908_67857.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1908_67857.syntax_only);
                                   ds_hooks = (uu___1908_67857.ds_hooks);
                                   dep_graph = (uu___1908_67857.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____67870 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____67896  ->
                      match uu____67896 with
                      | (l,uu____67903) -> FStar_Ident.lid_equals l mname))
               in
            match uu____67870 with
            | FStar_Pervasives_Native.None  ->
                let uu____67913 = prep env  in (uu____67913, false)
            | FStar_Pervasives_Native.Some (uu____67916,m) ->
                ((let uu____67923 =
                    (let uu____67927 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____67927) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____67923
                  then
                    let uu____67930 =
                      let uu____67936 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____67936)
                       in
                    let uu____67940 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____67930 uu____67940
                  else ());
                 (let uu____67943 =
                    let uu____67944 = push env  in prep uu____67944  in
                  (uu____67943, true)))
  
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
          let uu___1929_67962 = env  in
          {
            curmodule = (uu___1929_67962.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1929_67962.modules);
            scope_mods = (uu___1929_67962.scope_mods);
            exported_ids = (uu___1929_67962.exported_ids);
            trans_exported_ids = (uu___1929_67962.trans_exported_ids);
            includes = (uu___1929_67962.includes);
            sigaccum = (uu___1929_67962.sigaccum);
            sigmap = (uu___1929_67962.sigmap);
            iface = (uu___1929_67962.iface);
            admitted_iface = (uu___1929_67962.admitted_iface);
            expect_typ = (uu___1929_67962.expect_typ);
            docs = (uu___1929_67962.docs);
            remaining_iface_decls = (uu___1929_67962.remaining_iface_decls);
            syntax_only = (uu___1929_67962.syntax_only);
            ds_hooks = (uu___1929_67962.ds_hooks);
            dep_graph = (uu___1929_67962.dep_graph)
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
        let uu____67997 = lookup1 lid  in
        match uu____67997 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____68012  ->
                   match uu____68012 with
                   | (lid1,uu____68019) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____68022 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____68022  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____68034 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____68035 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____68034 uu____68035  in
                 let uu____68036 = resolve_module_name env modul true  in
                 match uu____68036 with
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
            let uu____68057 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____68057
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____68087 = lookup1 id1  in
      match uu____68087 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  