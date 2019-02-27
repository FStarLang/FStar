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
    match projectee with | Open_module  -> true | uu____53534 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____53545 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____53765 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____53785 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____53805 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____53825 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____53845 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____53865 -> false
  
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
    | uu____53887 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____53898 -> false
  
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
    ds_push_open_hook = (fun uu____55518  -> fun uu____55519  -> ());
    ds_push_include_hook = (fun uu____55522  -> fun uu____55523  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____55527  -> fun uu____55528  -> fun uu____55529  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____55566 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____55608 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___549_55643 = env  in
      {
        curmodule = (uu___549_55643.curmodule);
        curmonad = (uu___549_55643.curmonad);
        modules = (uu___549_55643.modules);
        scope_mods = (uu___549_55643.scope_mods);
        exported_ids = (uu___549_55643.exported_ids);
        trans_exported_ids = (uu___549_55643.trans_exported_ids);
        includes = (uu___549_55643.includes);
        sigaccum = (uu___549_55643.sigaccum);
        sigmap = (uu___549_55643.sigmap);
        iface = b;
        admitted_iface = (uu___549_55643.admitted_iface);
        expect_typ = (uu___549_55643.expect_typ);
        docs = (uu___549_55643.docs);
        remaining_iface_decls = (uu___549_55643.remaining_iface_decls);
        syntax_only = (uu___549_55643.syntax_only);
        ds_hooks = (uu___549_55643.ds_hooks);
        dep_graph = (uu___549_55643.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___554_55664 = e  in
      {
        curmodule = (uu___554_55664.curmodule);
        curmonad = (uu___554_55664.curmonad);
        modules = (uu___554_55664.modules);
        scope_mods = (uu___554_55664.scope_mods);
        exported_ids = (uu___554_55664.exported_ids);
        trans_exported_ids = (uu___554_55664.trans_exported_ids);
        includes = (uu___554_55664.includes);
        sigaccum = (uu___554_55664.sigaccum);
        sigmap = (uu___554_55664.sigmap);
        iface = (uu___554_55664.iface);
        admitted_iface = b;
        expect_typ = (uu___554_55664.expect_typ);
        docs = (uu___554_55664.docs);
        remaining_iface_decls = (uu___554_55664.remaining_iface_decls);
        syntax_only = (uu___554_55664.syntax_only);
        ds_hooks = (uu___554_55664.ds_hooks);
        dep_graph = (uu___554_55664.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___559_55685 = e  in
      {
        curmodule = (uu___559_55685.curmodule);
        curmonad = (uu___559_55685.curmonad);
        modules = (uu___559_55685.modules);
        scope_mods = (uu___559_55685.scope_mods);
        exported_ids = (uu___559_55685.exported_ids);
        trans_exported_ids = (uu___559_55685.trans_exported_ids);
        includes = (uu___559_55685.includes);
        sigaccum = (uu___559_55685.sigaccum);
        sigmap = (uu___559_55685.sigmap);
        iface = (uu___559_55685.iface);
        admitted_iface = (uu___559_55685.admitted_iface);
        expect_typ = b;
        docs = (uu___559_55685.docs);
        remaining_iface_decls = (uu___559_55685.remaining_iface_decls);
        syntax_only = (uu___559_55685.syntax_only);
        ds_hooks = (uu___559_55685.ds_hooks);
        dep_graph = (uu___559_55685.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____55712 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____55712 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____55725 =
            let uu____55729 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____55729  in
          FStar_All.pipe_right uu____55725 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___420_55870  ->
         match uu___420_55870 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____55875 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___578_55887 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___578_55887.curmonad);
        modules = (uu___578_55887.modules);
        scope_mods = (uu___578_55887.scope_mods);
        exported_ids = (uu___578_55887.exported_ids);
        trans_exported_ids = (uu___578_55887.trans_exported_ids);
        includes = (uu___578_55887.includes);
        sigaccum = (uu___578_55887.sigaccum);
        sigmap = (uu___578_55887.sigmap);
        iface = (uu___578_55887.iface);
        admitted_iface = (uu___578_55887.admitted_iface);
        expect_typ = (uu___578_55887.expect_typ);
        docs = (uu___578_55887.docs);
        remaining_iface_decls = (uu___578_55887.remaining_iface_decls);
        syntax_only = (uu___578_55887.syntax_only);
        ds_hooks = (uu___578_55887.ds_hooks);
        dep_graph = (uu___578_55887.dep_graph)
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
      let uu____55911 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____55945  ->
                match uu____55945 with
                | (m,uu____55954) -> FStar_Ident.lid_equals l m))
         in
      match uu____55911 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____55971,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____56005 =
          FStar_List.partition
            (fun uu____56035  ->
               match uu____56035 with
               | (m,uu____56044) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____56005 with
        | (uu____56049,rest) ->
            let uu___603_56083 = env  in
            {
              curmodule = (uu___603_56083.curmodule);
              curmonad = (uu___603_56083.curmonad);
              modules = (uu___603_56083.modules);
              scope_mods = (uu___603_56083.scope_mods);
              exported_ids = (uu___603_56083.exported_ids);
              trans_exported_ids = (uu___603_56083.trans_exported_ids);
              includes = (uu___603_56083.includes);
              sigaccum = (uu___603_56083.sigaccum);
              sigmap = (uu___603_56083.sigmap);
              iface = (uu___603_56083.iface);
              admitted_iface = (uu___603_56083.admitted_iface);
              expect_typ = (uu___603_56083.expect_typ);
              docs = (uu___603_56083.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___603_56083.syntax_only);
              ds_hooks = (uu___603_56083.ds_hooks);
              dep_graph = (uu___603_56083.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____56112 = current_module env  in qual uu____56112 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____56114 =
            let uu____56115 = current_module env  in qual uu____56115 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____56114
            id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___613_56136 = env  in
      {
        curmodule = (uu___613_56136.curmodule);
        curmonad = (uu___613_56136.curmonad);
        modules = (uu___613_56136.modules);
        scope_mods = (uu___613_56136.scope_mods);
        exported_ids = (uu___613_56136.exported_ids);
        trans_exported_ids = (uu___613_56136.trans_exported_ids);
        includes = (uu___613_56136.includes);
        sigaccum = (uu___613_56136.sigaccum);
        sigmap = (uu___613_56136.sigmap);
        iface = (uu___613_56136.iface);
        admitted_iface = (uu___613_56136.admitted_iface);
        expect_typ = (uu___613_56136.expect_typ);
        docs = (uu___613_56136.docs);
        remaining_iface_decls = (uu___613_56136.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___613_56136.ds_hooks);
        dep_graph = (uu___613_56136.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___618_56154 = env  in
      {
        curmodule = (uu___618_56154.curmodule);
        curmonad = (uu___618_56154.curmonad);
        modules = (uu___618_56154.modules);
        scope_mods = (uu___618_56154.scope_mods);
        exported_ids = (uu___618_56154.exported_ids);
        trans_exported_ids = (uu___618_56154.trans_exported_ids);
        includes = (uu___618_56154.includes);
        sigaccum = (uu___618_56154.sigaccum);
        sigmap = (uu___618_56154.sigmap);
        iface = (uu___618_56154.iface);
        admitted_iface = (uu___618_56154.admitted_iface);
        expect_typ = (uu___618_56154.expect_typ);
        docs = (uu___618_56154.docs);
        remaining_iface_decls = (uu___618_56154.remaining_iface_decls);
        syntax_only = (uu___618_56154.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___618_56154.dep_graph)
      }
  
let new_sigmap : 'Auu____56160 . unit -> 'Auu____56160 FStar_Util.smap =
  fun uu____56167  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____56175 = new_sigmap ()  in
    let uu____56180 = new_sigmap ()  in
    let uu____56185 = new_sigmap ()  in
    let uu____56196 = new_sigmap ()  in
    let uu____56209 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____56175;
      trans_exported_ids = uu____56180;
      includes = uu____56185;
      sigaccum = [];
      sigmap = uu____56196;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____56209;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___625_56243 = env  in
      {
        curmodule = (uu___625_56243.curmodule);
        curmonad = (uu___625_56243.curmonad);
        modules = (uu___625_56243.modules);
        scope_mods = (uu___625_56243.scope_mods);
        exported_ids = (uu___625_56243.exported_ids);
        trans_exported_ids = (uu___625_56243.trans_exported_ids);
        includes = (uu___625_56243.includes);
        sigaccum = (uu___625_56243.sigaccum);
        sigmap = (uu___625_56243.sigmap);
        iface = (uu___625_56243.iface);
        admitted_iface = (uu___625_56243.admitted_iface);
        expect_typ = (uu___625_56243.expect_typ);
        docs = (uu___625_56243.docs);
        remaining_iface_decls = (uu___625_56243.remaining_iface_decls);
        syntax_only = (uu___625_56243.syntax_only);
        ds_hooks = (uu___625_56243.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____56271  ->
         match uu____56271 with
         | (m,uu____56278) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___634_56291 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___634_56291.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___637_56292 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index =
          (uu___637_56292.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___637_56292.FStar_Syntax_Syntax.sort)
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
      (fun uu____56395  ->
         match uu____56395 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____56426 =
                 let uu____56427 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____56427 dd dq  in
               FStar_Pervasives_Native.Some uu____56426
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____56467 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____56505 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____56526 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___421_56556  ->
      match uu___421_56556 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____56575 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____56575 cont_t) -> 'Auu____56575 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____56612 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____56612
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____56628  ->
                   match uu____56628 with
                   | (f,uu____56636) ->
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
  fun uu___422_56710  ->
    match uu___422_56710 with
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
              let rec aux uu___423_56786 =
                match uu___423_56786 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____56799 = get_exported_id_set env mname  in
                      match uu____56799 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____56826 = mex eikind  in
                            FStar_ST.op_Bang uu____56826  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____56941 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____56941 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____57018 = qual modul id1  in
                        find_in_module uu____57018
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____57023 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___424_57032  ->
    match uu___424_57032 with
    | Exported_id_field  -> true
    | uu____57035 -> false
  
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
                  let check_local_binding_id uu___425_57159 =
                    match uu___425_57159 with
                    | (id',uu____57162) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___426_57170 =
                    match uu___426_57170 with
                    | (id',uu____57173,uu____57174) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____57179 = current_module env  in
                    FStar_Ident.ids_of_lid uu____57179  in
                  let proc uu___427_57187 =
                    match uu___427_57187 with
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
                        let uu____57196 = FStar_Ident.lid_of_ids curmod_ns
                           in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____57196 id1
                    | uu____57201 -> Cont_ignore  in
                  let rec aux uu___428_57211 =
                    match uu___428_57211 with
                    | a::q ->
                        let uu____57220 = proc a  in
                        option_of_cont (fun uu____57224  -> aux q)
                          uu____57220
                    | [] ->
                        let uu____57225 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____57229  -> FStar_Pervasives_Native.None)
                          uu____57225
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____57237 .
    FStar_Range.range ->
      ('Auu____57237 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____57251  -> match uu____57251 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____57269 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____57269)
          -> 'Auu____57269 -> 'Auu____57269
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____57310 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____57310 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____57354 = unmangleOpName id1  in
      match uu____57354 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____57360 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____57366 =
                 found_local_binding id1.FStar_Ident.idRange r  in
               Cont_ok uu____57366) (fun uu____57368  -> Cont_fail)
            (fun uu____57370  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____57377  -> fun uu____57378  -> Cont_fail)
                 Cont_ignore)
            (fun uu____57386  -> fun uu____57387  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____57461 ->
                let lid = qualify env id1  in
                let uu____57463 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____57463 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____57491 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____57491
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____57515 = current_module env  in qual uu____57515 id1
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
        let rec aux uu___429_57587 =
          match uu___429_57587 with
          | [] ->
              let uu____57592 = module_is_defined env lid  in
              if uu____57592
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____57604 =
                  let uu____57605 = FStar_Ident.path_of_lid ns  in
                  let uu____57609 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____57605 uu____57609  in
                let uu____57614 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____57604 uu____57614  in
              let uu____57615 = module_is_defined env new_lid  in
              if uu____57615
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____57624 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____57634::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____57654 =
          let uu____57656 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____57656  in
        if uu____57654
        then
          let uu____57658 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____57658
           then ()
           else
             (let uu____57663 =
                let uu____57669 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____57669)
                 in
              let uu____57673 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____57663 uu____57673))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____57687 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____57691 = resolve_module_name env modul_orig true  in
          (match uu____57691 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____57696 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___430_57719  ->
             match uu___430_57719 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____57723 -> false) env.scope_mods
  
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
                 let uu____57852 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____57852
                   (FStar_Util.map_option
                      (fun uu____57902  ->
                         match uu____57902 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____57972 = aux ns_rev_prefix ns_last_id  in
              (match uu____57972 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____58035 =
            let uu____58038 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____58038 true  in
          match uu____58035 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____58053 -> do_shorten env ids
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
                  | uu____58174::uu____58175 ->
                      let uu____58178 =
                        let uu____58181 =
                          let uu____58182 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____58183 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____58182 uu____58183
                           in
                        resolve_module_name env uu____58181 true  in
                      (match uu____58178 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____58188 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____58192  ->
                                FStar_Pervasives_Native.None) uu____58188)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___431_58216  ->
      match uu___431_58216 with
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
              let uu____58337 = k_global_def lid1 def  in
              cont_of_option k uu____58337  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____58373 = k_local_binding l  in
                 cont_of_option Cont_fail uu____58373)
              (fun r  ->
                 let uu____58379 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____58379)
              (fun uu____58383  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____58394,uu____58395,uu____58396,l,uu____58398,uu____58399) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___432_58412  ->
               match uu___432_58412 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____58415,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____58427 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____58433,uu____58434,uu____58435) -> FStar_Pervasives_Native.None
    | uu____58436 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____58452 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____58460 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____58460
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____58452 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____58483 =
         let uu____58484 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____58484  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____58483) &&
        (let uu____58492 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____58492 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____58509 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___433_58516  ->
                     match uu___433_58516 with
                     | FStar_Syntax_Syntax.Projector uu____58518 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____58524 -> true
                     | uu____58526 -> false)))
           in
        if uu____58509
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____58531 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___434_58537  ->
                 match uu___434_58537 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____58540 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___435_58546  ->
                    match uu___435_58546 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____58549 -> false)))
             &&
             (let uu____58552 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___436_58558  ->
                        match uu___436_58558 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____58561 -> false))
                 in
              Prims.op_Negation uu____58552))
         in
      if uu____58531 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___439_58613 =
            match uu___439_58613 with
            | (uu____58621,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____58625) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____58630 ->
                     let uu____58647 =
                       let uu____58648 =
                         let uu____58655 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____58655, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58648  in
                     FStar_Pervasives_Native.Some uu____58647
                 | FStar_Syntax_Syntax.Sig_datacon uu____58658 ->
                     let uu____58674 =
                       let uu____58675 =
                         let uu____58682 =
                           let uu____58683 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____58683
                            in
                         (uu____58682, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58675  in
                     FStar_Pervasives_Native.Some uu____58674
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____58688,lbs),uu____58690) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____58702 =
                       let uu____58703 =
                         let uu____58710 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____58710, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____58703  in
                     FStar_Pervasives_Native.Some uu____58702
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____58714,uu____58715) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____58719 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___437_58725  ->
                                  match uu___437_58725 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____58728 -> false)))
                        in
                     if uu____58719
                     then
                       let lid2 =
                         let uu____58734 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____58734  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____58736 =
                         FStar_Util.find_map quals
                           (fun uu___438_58741  ->
                              match uu___438_58741 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____58745 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____58736 with
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
                        | uu____58754 ->
                            let uu____58757 =
                              let uu____58758 =
                                let uu____58765 =
                                  let uu____58766 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____58766
                                   in
                                (uu____58765,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____58758  in
                            FStar_Pervasives_Native.Some uu____58757)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____58774 =
                       let uu____58775 =
                         let uu____58780 =
                           let uu____58781 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____58781
                            in
                         (se, uu____58780)  in
                       Eff_name uu____58775  in
                     FStar_Pervasives_Native.Some uu____58774
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____58783 =
                       let uu____58784 =
                         let uu____58789 =
                           let uu____58790 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____58790
                            in
                         (se, uu____58789)  in
                       Eff_name uu____58784  in
                     FStar_Pervasives_Native.Some uu____58783
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____58791 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____58810 =
                       let uu____58811 =
                         let uu____58818 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____58818, [])  in
                       Term_name uu____58811  in
                     FStar_Pervasives_Native.Some uu____58810
                 | uu____58822 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____58840 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____58840 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____58856 =
            match uu____58856 with
            | (id1,l,dd) ->
                let uu____58868 =
                  let uu____58869 =
                    let uu____58876 =
                      let uu____58877 =
                        let uu____58878 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____58878  in
                      FStar_Syntax_Syntax.fvar uu____58877 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____58876, [])  in
                  Term_name uu____58869  in
                FStar_Pervasives_Native.Some uu____58868
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____58886 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____58886 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____58894 -> FStar_Pervasives_Native.None)
            | uu____58897 -> FStar_Pervasives_Native.None  in
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
        let uu____58935 = try_lookup_name true exclude_interf env lid  in
        match uu____58935 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____58951 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____58971 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____58971 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____58986 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59012 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59012 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____59028;
             FStar_Syntax_Syntax.sigquals = uu____59029;
             FStar_Syntax_Syntax.sigmeta = uu____59030;
             FStar_Syntax_Syntax.sigattrs = uu____59031;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____59050;
             FStar_Syntax_Syntax.sigquals = uu____59051;
             FStar_Syntax_Syntax.sigmeta = uu____59052;
             FStar_Syntax_Syntax.sigattrs = uu____59053;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____59071,uu____59072,uu____59073,uu____59074,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____59076;
             FStar_Syntax_Syntax.sigquals = uu____59077;
             FStar_Syntax_Syntax.sigmeta = uu____59078;
             FStar_Syntax_Syntax.sigattrs = uu____59079;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____59101 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59127 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59127 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____59137;
             FStar_Syntax_Syntax.sigquals = uu____59138;
             FStar_Syntax_Syntax.sigmeta = uu____59139;
             FStar_Syntax_Syntax.sigattrs = uu____59140;_},uu____59141)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____59151;
             FStar_Syntax_Syntax.sigquals = uu____59152;
             FStar_Syntax_Syntax.sigmeta = uu____59153;
             FStar_Syntax_Syntax.sigattrs = uu____59154;_},uu____59155)
          -> FStar_Pervasives_Native.Some ne
      | uu____59164 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____59183 = try_lookup_effect_name env lid  in
      match uu____59183 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____59188 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59203 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____59203 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____59213,uu____59214,uu____59215,uu____59216);
             FStar_Syntax_Syntax.sigrng = uu____59217;
             FStar_Syntax_Syntax.sigquals = uu____59218;
             FStar_Syntax_Syntax.sigmeta = uu____59219;
             FStar_Syntax_Syntax.sigattrs = uu____59220;_},uu____59221)
          ->
          let rec aux new_name =
            let uu____59242 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____59242 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____59263) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____59274 =
                       let uu____59275 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____59275
                        in
                     FStar_Pervasives_Native.Some uu____59274
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____59277 =
                       let uu____59278 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____59278
                        in
                     FStar_Pervasives_Native.Some uu____59277
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____59279,uu____59280,uu____59281,cmp,uu____59283) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____59289 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____59290,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____59296 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___440_59335 =
        match uu___440_59335 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____59345,uu____59346,uu____59347);
             FStar_Syntax_Syntax.sigrng = uu____59348;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____59350;
             FStar_Syntax_Syntax.sigattrs = uu____59351;_},uu____59352)
            -> FStar_Pervasives_Native.Some quals
        | uu____59361 -> FStar_Pervasives_Native.None  in
      let uu____59369 =
        resolve_in_open_namespaces' env lid
          (fun uu____59377  -> FStar_Pervasives_Native.None)
          (fun uu____59381  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____59369 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____59391 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____59409 =
        FStar_List.tryFind
          (fun uu____59424  ->
             match uu____59424 with
             | (mlid,modul) ->
                 let uu____59432 = FStar_Ident.path_of_lid mlid  in
                 uu____59432 = path) env.modules
         in
      match uu____59409 with
      | FStar_Pervasives_Native.Some (uu____59435,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___441_59475 =
        match uu___441_59475 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____59483,lbs),uu____59485);
             FStar_Syntax_Syntax.sigrng = uu____59486;
             FStar_Syntax_Syntax.sigquals = uu____59487;
             FStar_Syntax_Syntax.sigmeta = uu____59488;
             FStar_Syntax_Syntax.sigattrs = uu____59489;_},uu____59490)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____59508 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____59508
        | uu____59509 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____59516  -> FStar_Pervasives_Native.None)
        (fun uu____59518  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___442_59551 =
        match uu___442_59551 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____59562);
             FStar_Syntax_Syntax.sigrng = uu____59563;
             FStar_Syntax_Syntax.sigquals = uu____59564;
             FStar_Syntax_Syntax.sigmeta = uu____59565;
             FStar_Syntax_Syntax.sigattrs = uu____59566;_},uu____59567)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____59593 -> FStar_Pervasives_Native.None)
        | uu____59600 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____59611  -> FStar_Pervasives_Native.None)
        (fun uu____59615  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____59675 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____59675 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____59700 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____59738) ->
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
      let uu____59796 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____59796 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59828 = try_lookup_lid env l  in
      match uu____59828 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____59834 =
            let uu____59835 = FStar_Syntax_Subst.compress e  in
            uu____59835.FStar_Syntax_Syntax.n  in
          (match uu____59834 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____59841 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____59853 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____59853 with
      | (uu____59863,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____59884 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____59888 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____59888 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____59893 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___1304_59924 = env  in
        {
          curmodule = (uu___1304_59924.curmodule);
          curmonad = (uu___1304_59924.curmonad);
          modules = (uu___1304_59924.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___1304_59924.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___1304_59924.sigaccum);
          sigmap = (uu___1304_59924.sigmap);
          iface = (uu___1304_59924.iface);
          admitted_iface = (uu___1304_59924.admitted_iface);
          expect_typ = (uu___1304_59924.expect_typ);
          docs = (uu___1304_59924.docs);
          remaining_iface_decls = (uu___1304_59924.remaining_iface_decls);
          syntax_only = (uu___1304_59924.syntax_only);
          ds_hooks = (uu___1304_59924.ds_hooks);
          dep_graph = (uu___1304_59924.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____59940 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____59940 drop_attributes
  
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
               (uu____60010,uu____60011,uu____60012);
             FStar_Syntax_Syntax.sigrng = uu____60013;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____60015;
             FStar_Syntax_Syntax.sigattrs = uu____60016;_},uu____60017)
            ->
            let uu____60024 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___443_60030  ->
                      match uu___443_60030 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____60033 -> false))
               in
            if uu____60024
            then
              let uu____60038 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____60038
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____60041;
             FStar_Syntax_Syntax.sigrng = uu____60042;
             FStar_Syntax_Syntax.sigquals = uu____60043;
             FStar_Syntax_Syntax.sigmeta = uu____60044;
             FStar_Syntax_Syntax.sigattrs = uu____60045;_},uu____60046)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____60072 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____60072
        | uu____60073 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____60080  -> FStar_Pervasives_Native.None)
        (fun uu____60082  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___444_60117 =
        match uu___444_60117 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____60127,uu____60128,uu____60129,uu____60130,datas,uu____60132);
             FStar_Syntax_Syntax.sigrng = uu____60133;
             FStar_Syntax_Syntax.sigquals = uu____60134;
             FStar_Syntax_Syntax.sigmeta = uu____60135;
             FStar_Syntax_Syntax.sigattrs = uu____60136;_},uu____60137)
            -> FStar_Pervasives_Native.Some datas
        | uu____60154 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____60165  -> FStar_Pervasives_Native.None)
        (fun uu____60169  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____60248 =
    let uu____60249 =
      let uu____60254 =
        let uu____60257 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____60257  in
      let uu____60313 = FStar_ST.op_Bang record_cache  in uu____60254 ::
        uu____60313
       in
    FStar_ST.op_Colon_Equals record_cache uu____60249  in
  let pop1 uu____60423 =
    let uu____60424 =
      let uu____60429 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____60429  in
    FStar_ST.op_Colon_Equals record_cache uu____60424  in
  let snapshot1 uu____60544 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____60612 =
    let uu____60613 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____60613  in
  let insert r =
    let uu____60675 =
      let uu____60680 = let uu____60683 = peek1 ()  in r :: uu____60683  in
      let uu____60686 =
        let uu____60691 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____60691  in
      uu____60680 :: uu____60686  in
    FStar_ST.op_Colon_Equals record_cache uu____60675  in
  let filter1 uu____60803 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____60812 =
      let uu____60817 =
        let uu____60822 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____60822  in
      filtered :: uu____60817  in
    FStar_ST.op_Colon_Equals record_cache uu____60812  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____61814) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___445_61833  ->
                   match uu___445_61833 with
                   | FStar_Syntax_Syntax.RecordType uu____61835 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____61845 ->
                       true
                   | uu____61855 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___446_61880  ->
                      match uu___446_61880 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____61883,uu____61884,uu____61885,uu____61886,uu____61887);
                          FStar_Syntax_Syntax.sigrng = uu____61888;
                          FStar_Syntax_Syntax.sigquals = uu____61889;
                          FStar_Syntax_Syntax.sigmeta = uu____61890;
                          FStar_Syntax_Syntax.sigattrs = uu____61891;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____61902 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___447_61938  ->
                    match uu___447_61938 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____61942,uu____61943,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____61945;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____61947;
                        FStar_Syntax_Syntax.sigattrs = uu____61948;_} ->
                        let uu____61959 =
                          let uu____61960 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____61960  in
                        (match uu____61959 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____61966,t,uu____61968,uu____61969,uu____61970);
                             FStar_Syntax_Syntax.sigrng = uu____61971;
                             FStar_Syntax_Syntax.sigquals = uu____61972;
                             FStar_Syntax_Syntax.sigmeta = uu____61973;
                             FStar_Syntax_Syntax.sigattrs = uu____61974;_} ->
                             let uu____61985 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____61985 with
                              | (formals,uu____62001) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____62055  ->
                                            match uu____62055 with
                                            | (x,q) ->
                                                let uu____62068 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____62068
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____62123  ->
                                            match uu____62123 with
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
                                  ((let uu____62147 =
                                      let uu____62150 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____62150
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____62147);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____62253 =
                                            match uu____62253 with
                                            | (id1,uu____62259) ->
                                                let modul =
                                                  let uu____62262 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____62262.FStar_Ident.str
                                                   in
                                                let uu____62263 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____62263 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____62297 =
                                                         let uu____62298 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____62298
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____62297);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____62387
                                                               =
                                                               let uu____62388
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____62388.FStar_Ident.ident
                                                                in
                                                             uu____62387.FStar_Ident.idText
                                                              in
                                                           let uu____62390 =
                                                             let uu____62391
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____62391
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____62390))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____62487 -> ())
                    | uu____62488 -> ()))
        | uu____62489 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____62511 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____62511 with
        | (ns,id1) ->
            let uu____62528 = peek_record_cache ()  in
            FStar_Util.find_map uu____62528
              (fun record  ->
                 let uu____62534 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____62540  -> FStar_Pervasives_Native.None)
                   uu____62534)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____62542  -> Cont_ignore) (fun uu____62544  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____62550 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____62550)
        (fun k  -> fun uu____62556  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____62572 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____62572 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____62578 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____62598 = try_lookup_record_by_field_name env lid  in
        match uu____62598 with
        | FStar_Pervasives_Native.Some record' when
            let uu____62603 =
              let uu____62605 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____62605  in
            let uu____62606 =
              let uu____62608 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____62608  in
            uu____62603 = uu____62606 ->
            let uu____62610 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____62614  -> Cont_ok ())
               in
            (match uu____62610 with
             | Cont_ok uu____62616 -> true
             | uu____62618 -> false)
        | uu____62622 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____62644 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____62644 with
      | FStar_Pervasives_Native.Some r ->
          let uu____62655 =
            let uu____62661 =
              let uu____62662 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____62663 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____62662 uu____62663  in
            (uu____62661, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____62655
      | uu____62670 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____62699  ->
    let uu____62700 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____62700
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____62732  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___448_62745  ->
      match uu___448_62745 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___449_62805 =
            match uu___449_62805 with
            | Rec_binding uu____62807 -> true
            | uu____62809 -> false  in
          let this_env =
            let uu___1530_62812 = env  in
            let uu____62813 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1530_62812.curmodule);
              curmonad = (uu___1530_62812.curmonad);
              modules = (uu___1530_62812.modules);
              scope_mods = uu____62813;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1530_62812.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1530_62812.sigaccum);
              sigmap = (uu___1530_62812.sigmap);
              iface = (uu___1530_62812.iface);
              admitted_iface = (uu___1530_62812.admitted_iface);
              expect_typ = (uu___1530_62812.expect_typ);
              docs = (uu___1530_62812.docs);
              remaining_iface_decls = (uu___1530_62812.remaining_iface_decls);
              syntax_only = (uu___1530_62812.syntax_only);
              ds_hooks = (uu___1530_62812.ds_hooks);
              dep_graph = (uu___1530_62812.dep_graph)
            }  in
          let uu____62816 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____62816 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____62833 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1538_62858 = env  in
      {
        curmodule = (uu___1538_62858.curmodule);
        curmonad = (uu___1538_62858.curmonad);
        modules = (uu___1538_62858.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1538_62858.exported_ids);
        trans_exported_ids = (uu___1538_62858.trans_exported_ids);
        includes = (uu___1538_62858.includes);
        sigaccum = (uu___1538_62858.sigaccum);
        sigmap = (uu___1538_62858.sigmap);
        iface = (uu___1538_62858.iface);
        admitted_iface = (uu___1538_62858.admitted_iface);
        expect_typ = (uu___1538_62858.expect_typ);
        docs = (uu___1538_62858.docs);
        remaining_iface_decls = (uu___1538_62858.remaining_iface_decls);
        syntax_only = (uu___1538_62858.syntax_only);
        ds_hooks = (uu___1538_62858.ds_hooks);
        dep_graph = (uu___1538_62858.dep_graph)
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
        let uu____62892 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____62892
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____62899 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____62899)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____62943) ->
                let uu____62951 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____62951 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____62956 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____62956
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____62965 =
            let uu____62971 =
              let uu____62973 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____62973 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____62971)  in
          let uu____62977 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____62965 uu____62977  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____62986 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____62999 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____63010 -> (false, true)
            | uu____63023 -> (false, false)  in
          match uu____62986 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____63037 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____63043 =
                       let uu____63045 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____63045  in
                     if uu____63043
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____63037 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____63053 ->
                   (extract_record env globals s;
                    (let uu___1579_63079 = env  in
                     {
                       curmodule = (uu___1579_63079.curmodule);
                       curmonad = (uu___1579_63079.curmonad);
                       modules = (uu___1579_63079.modules);
                       scope_mods = (uu___1579_63079.scope_mods);
                       exported_ids = (uu___1579_63079.exported_ids);
                       trans_exported_ids =
                         (uu___1579_63079.trans_exported_ids);
                       includes = (uu___1579_63079.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1579_63079.sigmap);
                       iface = (uu___1579_63079.iface);
                       admitted_iface = (uu___1579_63079.admitted_iface);
                       expect_typ = (uu___1579_63079.expect_typ);
                       docs = (uu___1579_63079.docs);
                       remaining_iface_decls =
                         (uu___1579_63079.remaining_iface_decls);
                       syntax_only = (uu___1579_63079.syntax_only);
                       ds_hooks = (uu___1579_63079.ds_hooks);
                       dep_graph = (uu___1579_63079.dep_graph)
                     })))
           in
        let env2 =
          let uu___1582_63081 = env1  in
          let uu____63082 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1582_63081.curmodule);
            curmonad = (uu___1582_63081.curmonad);
            modules = (uu___1582_63081.modules);
            scope_mods = uu____63082;
            exported_ids = (uu___1582_63081.exported_ids);
            trans_exported_ids = (uu___1582_63081.trans_exported_ids);
            includes = (uu___1582_63081.includes);
            sigaccum = (uu___1582_63081.sigaccum);
            sigmap = (uu___1582_63081.sigmap);
            iface = (uu___1582_63081.iface);
            admitted_iface = (uu___1582_63081.admitted_iface);
            expect_typ = (uu___1582_63081.expect_typ);
            docs = (uu___1582_63081.docs);
            remaining_iface_decls = (uu___1582_63081.remaining_iface_decls);
            syntax_only = (uu___1582_63081.syntax_only);
            ds_hooks = (uu___1582_63081.ds_hooks);
            dep_graph = (uu___1582_63081.dep_graph)
          }  in
        let uu____63130 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____63156) ->
              let uu____63165 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____63165)
          | uu____63192 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____63130 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____63251  ->
                     match uu____63251 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____63273 =
                                    let uu____63276 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____63276
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____63273);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____63371 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____63371.FStar_Ident.str  in
                                      ((let uu____63373 =
                                          get_exported_id_set env3 modul  in
                                        match uu____63373 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____63406 =
                                              let uu____63407 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____63407
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____63406
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
                let uu___1607_63508 = env3  in
                let uu____63509 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1607_63508.curmodule);
                  curmonad = (uu___1607_63508.curmonad);
                  modules = (uu___1607_63508.modules);
                  scope_mods = uu____63509;
                  exported_ids = (uu___1607_63508.exported_ids);
                  trans_exported_ids = (uu___1607_63508.trans_exported_ids);
                  includes = (uu___1607_63508.includes);
                  sigaccum = (uu___1607_63508.sigaccum);
                  sigmap = (uu___1607_63508.sigmap);
                  iface = (uu___1607_63508.iface);
                  admitted_iface = (uu___1607_63508.admitted_iface);
                  expect_typ = (uu___1607_63508.expect_typ);
                  docs = (uu___1607_63508.docs);
                  remaining_iface_decls =
                    (uu___1607_63508.remaining_iface_decls);
                  syntax_only = (uu___1607_63508.syntax_only);
                  ds_hooks = (uu___1607_63508.ds_hooks);
                  dep_graph = (uu___1607_63508.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____63592 =
        let uu____63597 = resolve_module_name env ns false  in
        match uu____63597 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____63612 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____63630  ->
                      match uu____63630 with
                      | (m,uu____63637) ->
                          let uu____63638 =
                            let uu____63640 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____63640 "."  in
                          let uu____63643 =
                            let uu____63645 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____63645 "."  in
                          FStar_Util.starts_with uu____63638 uu____63643))
               in
            if uu____63612
            then (ns, Open_namespace)
            else
              (let uu____63655 =
                 let uu____63661 =
                   let uu____63663 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____63663
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____63661)  in
               let uu____63667 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____63655 uu____63667)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____63592 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____63689 = resolve_module_name env ns false  in
      match uu____63689 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____63699 = current_module env1  in
              uu____63699.FStar_Ident.str  in
            (let uu____63701 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____63701 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____63725 =
                   let uu____63728 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____63728
                    in
                 FStar_ST.op_Colon_Equals incl uu____63725);
            (match () with
             | () ->
                 let uu____63821 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____63821 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____63841 =
                          let uu____63938 = get_exported_id_set env1 curmod
                             in
                          let uu____63985 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____63938, uu____63985)  in
                        match uu____63841 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____64401 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____64401  in
                              let ex = cur_exports k  in
                              (let uu____64576 =
                                 let uu____64580 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____64580 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____64576);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____64777 =
                                     let uu____64781 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____64781 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____64777)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____64914 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____65016 =
                        let uu____65022 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____65022)
                         in
                      let uu____65026 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____65016 uu____65026))))
      | uu____65027 ->
          let uu____65030 =
            let uu____65036 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____65036)  in
          let uu____65040 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____65030 uu____65040
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____65057 = module_is_defined env l  in
        if uu____65057
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____65064 =
             let uu____65070 =
               let uu____65072 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____65072  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____65070)  in
           let uu____65076 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____65064 uu____65076)
  
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
            ((let uu____65099 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____65099 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____65103 = FStar_Ident.range_of_lid l  in
                  let uu____65104 =
                    let uu____65110 =
                      let uu____65112 = FStar_Ident.string_of_lid l  in
                      let uu____65114 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____65116 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____65112 uu____65114 uu____65116
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____65110)  in
                  FStar_Errors.log_issue uu____65103 uu____65104);
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
                      let uu____65162 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____65162 ->
                      let uu____65167 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____65167 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____65182;
                              FStar_Syntax_Syntax.sigrng = uu____65183;
                              FStar_Syntax_Syntax.sigquals = uu____65184;
                              FStar_Syntax_Syntax.sigmeta = uu____65185;
                              FStar_Syntax_Syntax.sigattrs = uu____65186;_},uu____65187)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____65205;
                              FStar_Syntax_Syntax.sigrng = uu____65206;
                              FStar_Syntax_Syntax.sigquals = uu____65207;
                              FStar_Syntax_Syntax.sigmeta = uu____65208;
                              FStar_Syntax_Syntax.sigattrs = uu____65209;_},uu____65210)
                           -> lids
                       | uu____65238 ->
                           ((let uu____65247 =
                               let uu____65249 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____65249  in
                             if uu____65247
                             then
                               let uu____65252 = FStar_Ident.range_of_lid l
                                  in
                               let uu____65253 =
                                 let uu____65259 =
                                   let uu____65261 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____65261
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____65259)
                                  in
                               FStar_Errors.log_issue uu____65252 uu____65253
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1710_65278 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1710_65278.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1710_65278.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1710_65278.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1710_65278.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____65280 -> lids) [])
         in
      let uu___1715_65281 = m  in
      let uu____65282 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____65292,uu____65293) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1724_65296 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1724_65296.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1724_65296.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1724_65296.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1724_65296.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____65297 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1715_65281.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____65282;
        FStar_Syntax_Syntax.exports =
          (uu___1715_65281.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1715_65281.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____65321) ->
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
                                (lid,uu____65342,uu____65343,uu____65344,uu____65345,uu____65346)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____65362,uu____65363)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____65380 =
                                        let uu____65387 =
                                          let uu____65388 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____65389 =
                                            let uu____65396 =
                                              let uu____65397 =
                                                let uu____65412 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____65412)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____65397
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____65396
                                             in
                                          uu____65389
                                            FStar_Pervasives_Native.None
                                            uu____65388
                                           in
                                        (lid, univ_names, uu____65387)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____65380
                                       in
                                    let se2 =
                                      let uu___1756_65429 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1756_65429.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1756_65429.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1756_65429.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____65439 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____65443,uu____65444) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____65453,lbs),uu____65455)
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
                             let uu____65473 =
                               let uu____65475 =
                                 let uu____65476 =
                                   let uu____65479 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____65479.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____65476.FStar_Syntax_Syntax.v  in
                               uu____65475.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____65473))
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
                               let uu____65496 =
                                 let uu____65499 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____65499.FStar_Syntax_Syntax.fv_name  in
                               uu____65496.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1779_65504 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1779_65504.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1779_65504.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1779_65504.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____65514 -> ()));
      (let curmod =
         let uu____65517 = current_module env  in uu____65517.FStar_Ident.str
          in
       (let uu____65519 =
          let uu____65616 = get_exported_id_set env curmod  in
          let uu____65663 = get_trans_exported_id_set env curmod  in
          (uu____65616, uu____65663)  in
        match uu____65519 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____66082 = cur_ex eikind  in
                FStar_ST.op_Bang uu____66082  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____66272 =
                let uu____66276 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____66276  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____66272  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____66409 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1797_66507 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1797_66507.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1797_66507.exported_ids);
                    trans_exported_ids = (uu___1797_66507.trans_exported_ids);
                    includes = (uu___1797_66507.includes);
                    sigaccum = [];
                    sigmap = (uu___1797_66507.sigmap);
                    iface = (uu___1797_66507.iface);
                    admitted_iface = (uu___1797_66507.admitted_iface);
                    expect_typ = (uu___1797_66507.expect_typ);
                    docs = (uu___1797_66507.docs);
                    remaining_iface_decls =
                      (uu___1797_66507.remaining_iface_decls);
                    syntax_only = (uu___1797_66507.syntax_only);
                    ds_hooks = (uu___1797_66507.ds_hooks);
                    dep_graph = (uu___1797_66507.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____66545  ->
         push_record_cache ();
         (let uu____66548 =
            let uu____66551 = FStar_ST.op_Bang stack  in env :: uu____66551
             in
          FStar_ST.op_Colon_Equals stack uu____66548);
         (let uu___1803_66600 = env  in
          let uu____66601 = FStar_Util.smap_copy env.exported_ids  in
          let uu____66606 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____66611 = FStar_Util.smap_copy env.includes  in
          let uu____66622 = FStar_Util.smap_copy env.sigmap  in
          let uu____66635 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1803_66600.curmodule);
            curmonad = (uu___1803_66600.curmonad);
            modules = (uu___1803_66600.modules);
            scope_mods = (uu___1803_66600.scope_mods);
            exported_ids = uu____66601;
            trans_exported_ids = uu____66606;
            includes = uu____66611;
            sigaccum = (uu___1803_66600.sigaccum);
            sigmap = uu____66622;
            iface = (uu___1803_66600.iface);
            admitted_iface = (uu___1803_66600.admitted_iface);
            expect_typ = (uu___1803_66600.expect_typ);
            docs = uu____66635;
            remaining_iface_decls = (uu___1803_66600.remaining_iface_decls);
            syntax_only = (uu___1803_66600.syntax_only);
            ds_hooks = (uu___1803_66600.ds_hooks);
            dep_graph = (uu___1803_66600.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____66643  ->
    FStar_Util.atomically
      (fun uu____66650  ->
         let uu____66651 = FStar_ST.op_Bang stack  in
         match uu____66651 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____66706 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____66753 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____66757 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____66799 = FStar_Util.smap_try_find sm' k  in
              match uu____66799 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1838_66830 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1838_66830.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1838_66830.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1838_66830.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1838_66830.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____66831 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____66839 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____66866 = finish env modul1  in (uu____66866, modul1)
  
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
      let uu____66968 =
        let uu____66972 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____66972  in
      FStar_Util.set_elements uu____66968  in
    let fields =
      let uu____67088 =
        let uu____67092 = e Exported_id_field  in
        FStar_ST.op_Bang uu____67092  in
      FStar_Util.set_elements uu____67088  in
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
          let uu____67248 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____67248  in
        let fields =
          let uu____67262 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____67262  in
        (fun uu___450_67270  ->
           match uu___450_67270 with
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
  'Auu____67407 .
    'Auu____67407 Prims.list FStar_Pervasives_Native.option ->
      'Auu____67407 Prims.list FStar_ST.ref
  =
  fun uu___451_67420  ->
    match uu___451_67420 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____67463 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____67463 as_exported_ids  in
      let uu____67469 = as_ids_opt env.exported_ids  in
      let uu____67472 = as_ids_opt env.trans_exported_ids  in
      let uu____67475 =
        let uu____67480 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____67480 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____67469;
        mii_trans_exported_ids = uu____67472;
        mii_includes = uu____67475
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
                let uu____67602 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____67602 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___452_67624 =
                  match uu___452_67624 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____67636  ->
                     match uu____67636 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____67662 =
                    let uu____67667 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____67667, Open_namespace)  in
                  [uu____67662]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____67698 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____67698);
              (match () with
               | () ->
                   ((let uu____67725 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____67725);
                    (match () with
                     | () ->
                         ((let uu____67752 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____67752);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1908_67784 = env1  in
                                 let uu____67785 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1908_67784.curmonad);
                                   modules = (uu___1908_67784.modules);
                                   scope_mods = uu____67785;
                                   exported_ids =
                                     (uu___1908_67784.exported_ids);
                                   trans_exported_ids =
                                     (uu___1908_67784.trans_exported_ids);
                                   includes = (uu___1908_67784.includes);
                                   sigaccum = (uu___1908_67784.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1908_67784.expect_typ);
                                   docs = (uu___1908_67784.docs);
                                   remaining_iface_decls =
                                     (uu___1908_67784.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1908_67784.syntax_only);
                                   ds_hooks = (uu___1908_67784.ds_hooks);
                                   dep_graph = (uu___1908_67784.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____67797 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____67823  ->
                      match uu____67823 with
                      | (l,uu____67830) -> FStar_Ident.lid_equals l mname))
               in
            match uu____67797 with
            | FStar_Pervasives_Native.None  ->
                let uu____67840 = prep env  in (uu____67840, false)
            | FStar_Pervasives_Native.Some (uu____67843,m) ->
                ((let uu____67850 =
                    (let uu____67854 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____67854) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____67850
                  then
                    let uu____67857 =
                      let uu____67863 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____67863)
                       in
                    let uu____67867 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____67857 uu____67867
                  else ());
                 (let uu____67870 =
                    let uu____67871 = push env  in prep uu____67871  in
                  (uu____67870, true)))
  
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
          let uu___1929_67889 = env  in
          {
            curmodule = (uu___1929_67889.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1929_67889.modules);
            scope_mods = (uu___1929_67889.scope_mods);
            exported_ids = (uu___1929_67889.exported_ids);
            trans_exported_ids = (uu___1929_67889.trans_exported_ids);
            includes = (uu___1929_67889.includes);
            sigaccum = (uu___1929_67889.sigaccum);
            sigmap = (uu___1929_67889.sigmap);
            iface = (uu___1929_67889.iface);
            admitted_iface = (uu___1929_67889.admitted_iface);
            expect_typ = (uu___1929_67889.expect_typ);
            docs = (uu___1929_67889.docs);
            remaining_iface_decls = (uu___1929_67889.remaining_iface_decls);
            syntax_only = (uu___1929_67889.syntax_only);
            ds_hooks = (uu___1929_67889.ds_hooks);
            dep_graph = (uu___1929_67889.dep_graph)
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
        let uu____67924 = lookup1 lid  in
        match uu____67924 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____67939  ->
                   match uu____67939 with
                   | (lid1,uu____67946) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____67949 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____67949  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____67961 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____67962 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____67961 uu____67962  in
                 let uu____67963 = resolve_module_name env modul true  in
                 match uu____67963 with
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
            let uu____67984 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____67984
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____68014 = lookup1 id1  in
      match uu____68014 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  