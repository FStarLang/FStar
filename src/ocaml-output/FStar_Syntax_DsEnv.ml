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
    match projectee with | Open_module  -> true | uu____72 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____83 -> false
  
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
    match projectee with | Local_binding _0 -> true | uu____589 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____608 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____627 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____646 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____667 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____706 -> false
  
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
    | uu____777 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____788 -> false
  
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
    ds_push_open_hook = (fun uu____4322  -> fun uu____4323  -> ());
    ds_push_include_hook = (fun uu____4343  -> fun uu____4344  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____4369  -> fun uu____4370  -> fun uu____4371  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____4456 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____4530 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___129_4642 = env  in
      {
        curmodule = (uu___129_4642.curmodule);
        curmonad = (uu___129_4642.curmonad);
        modules = (uu___129_4642.modules);
        scope_mods = (uu___129_4642.scope_mods);
        exported_ids = (uu___129_4642.exported_ids);
        trans_exported_ids = (uu___129_4642.trans_exported_ids);
        includes = (uu___129_4642.includes);
        sigaccum = (uu___129_4642.sigaccum);
        sigmap = (uu___129_4642.sigmap);
        iface = b;
        admitted_iface = (uu___129_4642.admitted_iface);
        expect_typ = (uu___129_4642.expect_typ);
        docs = (uu___129_4642.docs);
        remaining_iface_decls = (uu___129_4642.remaining_iface_decls);
        syntax_only = (uu___129_4642.syntax_only);
        ds_hooks = (uu___129_4642.ds_hooks);
        dep_graph = (uu___129_4642.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___134_4782 = e  in
      {
        curmodule = (uu___134_4782.curmodule);
        curmonad = (uu___134_4782.curmonad);
        modules = (uu___134_4782.modules);
        scope_mods = (uu___134_4782.scope_mods);
        exported_ids = (uu___134_4782.exported_ids);
        trans_exported_ids = (uu___134_4782.trans_exported_ids);
        includes = (uu___134_4782.includes);
        sigaccum = (uu___134_4782.sigaccum);
        sigmap = (uu___134_4782.sigmap);
        iface = (uu___134_4782.iface);
        admitted_iface = b;
        expect_typ = (uu___134_4782.expect_typ);
        docs = (uu___134_4782.docs);
        remaining_iface_decls = (uu___134_4782.remaining_iface_decls);
        syntax_only = (uu___134_4782.syntax_only);
        ds_hooks = (uu___134_4782.ds_hooks);
        dep_graph = (uu___134_4782.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___139_4922 = e  in
      {
        curmodule = (uu___139_4922.curmodule);
        curmonad = (uu___139_4922.curmonad);
        modules = (uu___139_4922.modules);
        scope_mods = (uu___139_4922.scope_mods);
        exported_ids = (uu___139_4922.exported_ids);
        trans_exported_ids = (uu___139_4922.trans_exported_ids);
        includes = (uu___139_4922.includes);
        sigaccum = (uu___139_4922.sigaccum);
        sigmap = (uu___139_4922.sigmap);
        iface = (uu___139_4922.iface);
        admitted_iface = (uu___139_4922.admitted_iface);
        expect_typ = b;
        docs = (uu___139_4922.docs);
        remaining_iface_decls = (uu___139_4922.remaining_iface_decls);
        syntax_only = (uu___139_4922.syntax_only);
        ds_hooks = (uu___139_4922.ds_hooks);
        dep_graph = (uu___139_4922.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____5059 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____5059 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____5072 =
            let uu____5076 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____5076  in
          FStar_All.pipe_right uu____5072 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___0_5252  ->
         match uu___0_5252 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____5273 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___158_5348 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___158_5348.curmonad);
        modules = (uu___158_5348.modules);
        scope_mods = (uu___158_5348.scope_mods);
        exported_ids = (uu___158_5348.exported_ids);
        trans_exported_ids = (uu___158_5348.trans_exported_ids);
        includes = (uu___158_5348.includes);
        sigaccum = (uu___158_5348.sigaccum);
        sigmap = (uu___158_5348.sigmap);
        iface = (uu___158_5348.iface);
        admitted_iface = (uu___158_5348.admitted_iface);
        expect_typ = (uu___158_5348.expect_typ);
        docs = (uu___158_5348.docs);
        remaining_iface_decls = (uu___158_5348.remaining_iface_decls);
        syntax_only = (uu___158_5348.syntax_only);
        ds_hooks = (uu___158_5348.ds_hooks);
        dep_graph = (uu___158_5348.dep_graph)
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
      let uu____5515 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____5585  ->
                match uu____5585 with
                | (m,uu____5603) -> FStar_Ident.lid_equals l m))
         in
      match uu____5515 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____5657,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____5792 =
          FStar_List.partition
            (fun uu____5849  ->
               match uu____5849 with
               | (m,uu____5867) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____5792 with
        | (uu____5907,rest) ->
            let uu___183_5977 = env  in
            {
              curmodule = (uu___183_5977.curmodule);
              curmonad = (uu___183_5977.curmonad);
              modules = (uu___183_5977.modules);
              scope_mods = (uu___183_5977.scope_mods);
              exported_ids = (uu___183_5977.exported_ids);
              trans_exported_ids = (uu___183_5977.trans_exported_ids);
              includes = (uu___183_5977.includes);
              sigaccum = (uu___183_5977.sigaccum);
              sigmap = (uu___183_5977.sigmap);
              iface = (uu___183_5977.iface);
              admitted_iface = (uu___183_5977.admitted_iface);
              expect_typ = (uu___183_5977.expect_typ);
              docs = (uu___183_5977.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___183_5977.syntax_only);
              ds_hooks = (uu___183_5977.ds_hooks);
              dep_graph = (uu___183_5977.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____6116 = current_module env  in qual uu____6116 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____6130 =
            let uu____6139 = current_module env  in qual uu____6139 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____6130 id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___193_6253 = env  in
      {
        curmodule = (uu___193_6253.curmodule);
        curmonad = (uu___193_6253.curmonad);
        modules = (uu___193_6253.modules);
        scope_mods = (uu___193_6253.scope_mods);
        exported_ids = (uu___193_6253.exported_ids);
        trans_exported_ids = (uu___193_6253.trans_exported_ids);
        includes = (uu___193_6253.includes);
        sigaccum = (uu___193_6253.sigaccum);
        sigmap = (uu___193_6253.sigmap);
        iface = (uu___193_6253.iface);
        admitted_iface = (uu___193_6253.admitted_iface);
        expect_typ = (uu___193_6253.expect_typ);
        docs = (uu___193_6253.docs);
        remaining_iface_decls = (uu___193_6253.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___193_6253.ds_hooks);
        dep_graph = (uu___193_6253.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___198_6405 = env  in
      {
        curmodule = (uu___198_6405.curmodule);
        curmonad = (uu___198_6405.curmonad);
        modules = (uu___198_6405.modules);
        scope_mods = (uu___198_6405.scope_mods);
        exported_ids = (uu___198_6405.exported_ids);
        trans_exported_ids = (uu___198_6405.trans_exported_ids);
        includes = (uu___198_6405.includes);
        sigaccum = (uu___198_6405.sigaccum);
        sigmap = (uu___198_6405.sigmap);
        iface = (uu___198_6405.iface);
        admitted_iface = (uu___198_6405.admitted_iface);
        expect_typ = (uu___198_6405.expect_typ);
        docs = (uu___198_6405.docs);
        remaining_iface_decls = (uu___198_6405.remaining_iface_decls);
        syntax_only = (uu___198_6405.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___198_6405.dep_graph)
      }
  
let new_sigmap : 'Auu____6445 . unit -> 'Auu____6445 FStar_Util.smap =
  fun uu____6452  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____6477 = new_sigmap ()  in
    let uu____6482 = new_sigmap ()  in
    let uu____6487 = new_sigmap ()  in
    let uu____6506 = new_sigmap ()  in
    let uu____6529 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____6477;
      trans_exported_ids = uu____6482;
      includes = uu____6487;
      sigaccum = [];
      sigmap = uu____6506;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____6529;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___205_6680 = env  in
      {
        curmodule = (uu___205_6680.curmodule);
        curmonad = (uu___205_6680.curmonad);
        modules = (uu___205_6680.modules);
        scope_mods = (uu___205_6680.scope_mods);
        exported_ids = (uu___205_6680.exported_ids);
        trans_exported_ids = (uu___205_6680.trans_exported_ids);
        includes = (uu___205_6680.includes);
        sigaccum = (uu___205_6680.sigaccum);
        sigmap = (uu___205_6680.sigmap);
        iface = (uu___205_6680.iface);
        admitted_iface = (uu___205_6680.admitted_iface);
        expect_typ = (uu___205_6680.expect_typ);
        docs = (uu___205_6680.docs);
        remaining_iface_decls = (uu___205_6680.remaining_iface_decls);
        syntax_only = (uu___205_6680.syntax_only);
        ds_hooks = (uu___205_6680.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____6827  ->
         match uu____6827 with
         | (m,uu____6846) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___214_6912 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___214_6912.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___217_6917 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___217_6917.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___217_6917.FStar_Syntax_Syntax.sort)
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
      (fun uu____7060  ->
         match uu____7060 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____7099 =
                 let uu____7108 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____7108 dd dq  in
               FStar_Pervasives_Native.Some uu____7099
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____7164 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____7201 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____7222 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___1_7252  ->
      match uu___1_7252 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____7271 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____7271 cont_t) -> 'Auu____7271 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____7370 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____7370
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____7426  ->
                   match uu____7426 with
                   | (f,uu____7450) ->
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
  fun uu___2_7664  ->
    match uu___2_7664 with
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
              let rec aux uu___3_7798 =
                match uu___3_7798 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____7831 = get_exported_id_set env mname  in
                      match uu____7831 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____7858 = mex eikind  in
                            FStar_ST.op_Bang uu____7858  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____7924 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____7924 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____8015 = qual modul id1  in
                        find_in_module uu____8015
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____8032 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___4_8049  ->
    match uu___4_8049 with | Exported_id_field  -> true | uu____8052 -> false
  
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
                  let check_local_binding_id uu___5_8246 =
                    match uu___5_8246 with
                    | (id',uu____8249) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___6_8271 =
                    match uu___6_8271 with
                    | (id',uu____8274,uu____8275) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____8294 = current_module env  in
                    FStar_Ident.ids_of_lid uu____8294  in
                  let proc uu___7_8310 =
                    match uu___7_8310 with
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
                        let uu____8339 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____8339 id1
                    | uu____8360 -> Cont_ignore  in
                  let rec aux uu___8_8370 =
                    match uu___8_8370 with
                    | a::q ->
                        let uu____8379 = proc a  in
                        option_of_cont (fun uu____8383  -> aux q) uu____8379
                    | [] ->
                        let uu____8384 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____8388  -> FStar_Pervasives_Native.None)
                          uu____8384
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____8396 .
    FStar_Range.range ->
      ('Auu____8396 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____8419  -> match uu____8419 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____8452 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____8452)
          -> 'Auu____8452 -> 'Auu____8452
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____8553 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____8553 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____8668 = unmangleOpName id1  in
      match uu____8668 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____8694 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____8708 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____8708) (fun uu____8724  -> Cont_fail)
            (fun uu____8730  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____8759  -> fun uu____8760  -> Cont_fail)
                 Cont_ignore)
            (fun uu____8785  -> fun uu____8786  -> Cont_fail)
  
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
            | FStar_Pervasives_Native.Some uu____8926 ->
                let lid = qualify env id1  in
                let uu____8940 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____8940 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____8988 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____8988
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____9027 = current_module env  in qual uu____9027 id1
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
        let rec aux uu___9_9295 =
          match uu___9_9295 with
          | [] ->
              let uu____9304 = module_is_defined env lid  in
              if uu____9304
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____9344 =
                  let uu____9345 = FStar_Ident.path_of_lid ns  in
                  let uu____9349 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____9345 uu____9349  in
                let uu____9354 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____9344 uu____9354  in
              let uu____9355 = module_is_defined env new_lid  in
              if uu____9355
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____9372 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____9394::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____9464 =
          let uu____9466 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____9466  in
        if uu____9464
        then
          let uu____9476 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____9476
           then ()
           else
             (let uu____9481 =
                let uu____9487 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____9487)
                 in
              let uu____9491 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____9481 uu____9491))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____9549 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____9563 = resolve_module_name env modul_orig true  in
          (match uu____9563 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____9580 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___10_9649  ->
             match uu___10_9649 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____9661 -> false) env.scope_mods
  
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
                 let uu____9972 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____9972
                   (FStar_Util.map_option
                      (fun uu____10042  ->
                         match uu____10042 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____10198 = aux ns_rev_prefix ns_last_id  in
              (match uu____10198 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____10303 =
            let uu____10310 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____10310 true  in
          match uu____10303 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____10351 -> do_shorten env ids
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
                  | uu____10550::uu____10551 ->
                      let uu____10560 =
                        let uu____10567 =
                          let uu____10576 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____10585 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____10576 uu____10585
                           in
                        resolve_module_name env uu____10567 true  in
                      (match uu____10560 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____10602 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____10606  ->
                                FStar_Pervasives_Native.None) uu____10602)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___11_10632  ->
      match uu___11_10632 with
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
              let uu____10831 = k_global_def lid1 def  in
              cont_of_option k uu____10831  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____10879 = k_local_binding l  in
                 cont_of_option Cont_fail uu____10879)
              (fun r  ->
                 let uu____10885 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____10885)
              (fun uu____10889  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____10920,uu____10921,uu____10922,l,uu____10924,uu____10925) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___12_10970  ->
               match uu___12_10970 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____10973,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____10999 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____11005,uu____11006,uu____11007) -> FStar_Pervasives_Native.None
    | uu____11024 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____11065 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____11107 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____11107
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____11065 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____11164 =
         let uu____11165 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____11165  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____11164) &&
        (let uu____11175 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____11175 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____11208 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___13_11215  ->
                     match uu___13_11215 with
                     | FStar_Syntax_Syntax.Projector uu____11217 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____11229 -> true
                     | uu____11235 -> false)))
           in
        if uu____11208
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____11240 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___14_11246  ->
                 match uu___14_11246 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____11249 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___15_11255  ->
                    match uu___15_11255 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____11258 -> false)))
             &&
             (let uu____11261 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___16_11267  ->
                        match uu___16_11267 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____11270 -> false))
                 in
              Prims.op_Negation uu____11261))
         in
      if uu____11240 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
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
          let k_global_def source_lid uu___19_11373 =
            match uu___19_11373 with
            | (uu____11390,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____11404) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____11419 ->
                     let uu____11452 =
                       let uu____11453 =
                         let uu____11468 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____11468, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____11453  in
                     FStar_Pervasives_Native.Some uu____11452
                 | FStar_Syntax_Syntax.Sig_datacon uu____11487 ->
                     let uu____11519 =
                       let uu____11520 =
                         let uu____11535 =
                           let uu____11544 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____11544
                            in
                         (uu____11535, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____11520  in
                     FStar_Pervasives_Native.Some uu____11519
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____11557,lbs),uu____11559) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____11599 =
                       let uu____11600 =
                         let uu____11615 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____11615, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____11600  in
                     FStar_Pervasives_Native.Some uu____11599
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____11635,uu____11636) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____11656 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___17_11662  ->
                                  match uu___17_11662 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____11665 -> false)))
                        in
                     if uu____11656
                     then
                       let lid2 =
                         let uu____11679 =
                           FStar_Ident.range_of_lid source_lid  in
                         FStar_Ident.set_lid_range lid1 uu____11679  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____11681 =
                         FStar_Util.find_map quals
                           (fun uu___18_11694  ->
                              match uu___18_11694 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____11710 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____11681 with
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
                        | uu____11747 ->
                            let uu____11754 =
                              let uu____11755 =
                                let uu____11770 =
                                  let uu____11779 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd
                                    uu____11779
                                   in
                                (uu____11770,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____11755  in
                            FStar_Pervasives_Native.Some uu____11754)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____11815 =
                       let uu____11816 =
                         let uu____11830 =
                           let uu____11839 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____11839
                            in
                         (se, uu____11830)  in
                       Eff_name uu____11816  in
                     FStar_Pervasives_Native.Some uu____11815
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____11870 =
                       let uu____11871 =
                         let uu____11885 =
                           let uu____11894 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____11894
                            in
                         (se, uu____11885)  in
                       Eff_name uu____11871  in
                     FStar_Pervasives_Native.Some uu____11870
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11904 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____11956 =
                       let uu____11957 =
                         let uu____11972 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____11972, [])  in
                       Term_name uu____11957  in
                     FStar_Pervasives_Native.Some uu____11956
                 | uu____11996 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____12036 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____12036 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____12072 =
            match uu____12072 with
            | (id1,l,dd) ->
                let uu____12102 =
                  let uu____12103 =
                    let uu____12118 =
                      let uu____12127 =
                        let uu____12136 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____12136  in
                      FStar_Syntax_Syntax.fvar uu____12127 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____12118, [])  in
                  Term_name uu____12103  in
                FStar_Pervasives_Native.Some uu____12102
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____12158 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____12158 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____12190 -> FStar_Pervasives_Native.None)
            | uu____12197 -> FStar_Pervasives_Native.None  in
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
        let uu____12297 = try_lookup_name true exclude_interf env lid  in
        match uu____12297 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____12358 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12433 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____12433 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____12492 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12577 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____12577 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____12606;
             FStar_Syntax_Syntax.sigquals = uu____12607;
             FStar_Syntax_Syntax.sigmeta = uu____12608;
             FStar_Syntax_Syntax.sigattrs = uu____12609;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____12684;
             FStar_Syntax_Syntax.sigquals = uu____12685;
             FStar_Syntax_Syntax.sigmeta = uu____12686;
             FStar_Syntax_Syntax.sigattrs = uu____12687;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____12761,uu____12762,uu____12763,uu____12764,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____12766;
             FStar_Syntax_Syntax.sigquals = uu____12767;
             FStar_Syntax_Syntax.sigmeta = uu____12768;
             FStar_Syntax_Syntax.sigattrs = uu____12769;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____12843 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12944 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____12944 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____12983;
             FStar_Syntax_Syntax.sigquals = uu____12984;
             FStar_Syntax_Syntax.sigmeta = uu____12985;
             FStar_Syntax_Syntax.sigattrs = uu____12986;_},uu____12987)
          -> FStar_Pervasives_Native.Some ne
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____13065;
             FStar_Syntax_Syntax.sigquals = uu____13066;
             FStar_Syntax_Syntax.sigmeta = uu____13067;
             FStar_Syntax_Syntax.sigattrs = uu____13068;_},uu____13069)
          -> FStar_Pervasives_Native.Some ne
      | uu____13146 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____13236 = try_lookup_effect_name env lid  in
      match uu____13236 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____13249 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____13318 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____13318 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____13341,uu____13342,uu____13343,uu____13344);
             FStar_Syntax_Syntax.sigrng = uu____13345;
             FStar_Syntax_Syntax.sigquals = uu____13346;
             FStar_Syntax_Syntax.sigmeta = uu____13347;
             FStar_Syntax_Syntax.sigattrs = uu____13348;_},uu____13349)
          ->
          let rec aux new_name =
            let uu____13426 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____13426 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____13470) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     let uu____13520 =
                       let uu____13529 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____13529
                        in
                     FStar_Pervasives_Native.Some uu____13520
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____13555 =
                       let uu____13564 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____13564
                        in
                     FStar_Pervasives_Native.Some uu____13555
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____13569,uu____13570,uu____13571,cmp,uu____13573) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____13603 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____13608,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____13645 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___20_13748 =
        match uu___20_13748 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____13767,uu____13768,uu____13769);
             FStar_Syntax_Syntax.sigrng = uu____13770;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____13772;
             FStar_Syntax_Syntax.sigattrs = uu____13773;_},uu____13774)
            -> FStar_Pervasives_Native.Some quals
        | uu____13810 -> FStar_Pervasives_Native.None  in
      let uu____13823 =
        resolve_in_open_namespaces' env lid
          (fun uu____13831  -> FStar_Pervasives_Native.None)
          (fun uu____13835  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____13823 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____13845 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____13905 =
        FStar_List.tryFind
          (fun uu____13944  ->
             match uu____13944 with
             | (mlid,modul) ->
                 let uu____13988 = FStar_Ident.path_of_lid mlid  in
                 uu____13988 = path) env.modules
         in
      match uu____13905 with
      | FStar_Pervasives_Native.Some (uu____13999,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___21_14162 =
        match uu___21_14162 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____14183,lbs),uu____14185);
             FStar_Syntax_Syntax.sigrng = uu____14186;
             FStar_Syntax_Syntax.sigquals = uu____14187;
             FStar_Syntax_Syntax.sigmeta = uu____14188;
             FStar_Syntax_Syntax.sigattrs = uu____14189;_},uu____14190)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____14247 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____14247
        | uu____14260 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____14280  -> FStar_Pervasives_Native.None)
        (fun uu____14286  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___22_14382 =
        match uu___22_14382 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____14406);
             FStar_Syntax_Syntax.sigrng = uu____14407;
             FStar_Syntax_Syntax.sigquals = uu____14408;
             FStar_Syntax_Syntax.sigmeta = uu____14409;
             FStar_Syntax_Syntax.sigattrs = uu____14410;_},uu____14411)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____14500 -> FStar_Pervasives_Native.None)
        | uu____14519 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____14543  -> FStar_Pervasives_Native.None)
        (fun uu____14551  -> FStar_Pervasives_Native.None) k_global_def
  
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
          let uu____14681 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____14681 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____14746 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____14820) ->
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
      let uu____15022 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____15022 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____15120 = try_lookup_lid env l  in
      match uu____15120 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____15150 =
            let uu____15151 = FStar_Syntax_Subst.compress e  in
            uu____15151.FStar_Syntax_Syntax.n  in
          (match uu____15150 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____15180 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____15242 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____15242 with
      | (uu____15260,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____15343 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____15361 =
            resolve_to_fully_qualified_name env lid_without_ns  in
          (match uu____15361 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____15382 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___884_15509 = env  in
        {
          curmodule = (uu___884_15509.curmodule);
          curmonad = (uu___884_15509.curmonad);
          modules = (uu___884_15509.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___884_15509.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___884_15509.sigaccum);
          sigmap = (uu___884_15509.sigmap);
          iface = (uu___884_15509.iface);
          admitted_iface = (uu___884_15509.admitted_iface);
          expect_typ = (uu___884_15509.expect_typ);
          docs = (uu___884_15509.docs);
          remaining_iface_decls = (uu___884_15509.remaining_iface_decls);
          syntax_only = (uu___884_15509.syntax_only);
          ds_hooks = (uu___884_15509.ds_hooks);
          dep_graph = (uu___884_15509.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____15609 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____15609 drop_attributes
  
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
               (uu____15810,uu____15811,uu____15812);
             FStar_Syntax_Syntax.sigrng = uu____15813;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____15815;
             FStar_Syntax_Syntax.sigattrs = uu____15816;_},uu____15817)
            ->
            let uu____15851 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___23_15857  ->
                      match uu___23_15857 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____15860 -> false))
               in
            if uu____15851
            then
              let uu____15868 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____15868
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____15883;
             FStar_Syntax_Syntax.sigrng = uu____15884;
             FStar_Syntax_Syntax.sigquals = uu____15885;
             FStar_Syntax_Syntax.sigmeta = uu____15886;
             FStar_Syntax_Syntax.sigattrs = uu____15887;_},uu____15888)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____15946 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____15946
        | uu____15956 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____15974  -> FStar_Pervasives_Native.None)
        (fun uu____15979  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___24_16076 =
        match uu___24_16076 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____16099,uu____16100,uu____16101,uu____16102,datas,uu____16104);
             FStar_Syntax_Syntax.sigrng = uu____16105;
             FStar_Syntax_Syntax.sigquals = uu____16106;
             FStar_Syntax_Syntax.sigmeta = uu____16107;
             FStar_Syntax_Syntax.sigattrs = uu____16108;_},uu____16109)
            -> FStar_Pervasives_Native.Some datas
        | uu____16173 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____16197  -> FStar_Pervasives_Native.None)
        (fun uu____16205  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____16358 =
    let uu____16359 =
      let uu____16374 =
        let uu____16387 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____16387  in
      let uu____16461 = FStar_ST.op_Bang record_cache  in uu____16374 ::
        uu____16461
       in
    FStar_ST.op_Colon_Equals record_cache uu____16359  in
  let pop1 uu____16587 =
    let uu____16588 =
      let uu____16603 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____16603  in
    FStar_ST.op_Colon_Equals record_cache uu____16588  in
  let snapshot1 uu____16734 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____16788 =
    let uu____16789 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____16789  in
  let insert r =
    let uu____16889 =
      let uu____16904 = let uu____16917 = peek1 ()  in r :: uu____16917  in
      let uu____16940 =
        let uu____16955 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____16955  in
      uu____16904 :: uu____16940  in
    FStar_ST.op_Colon_Equals record_cache uu____16889  in
  let filter1 uu____17093 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____17142 =
      let uu____17157 =
        let uu____17172 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____17172  in
      filtered :: uu____17157  in
    FStar_ST.op_Colon_Equals record_cache uu____17142  in
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
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____18632) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___25_18669  ->
                   match uu___25_18669 with
                   | FStar_Syntax_Syntax.RecordType uu____18671 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____18685 ->
                       true
                   | uu____18699 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___26_18752  ->
                      match uu___26_18752 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____18760,uu____18761,uu____18762,uu____18763,uu____18764);
                          FStar_Syntax_Syntax.sigrng = uu____18765;
                          FStar_Syntax_Syntax.sigquals = uu____18766;
                          FStar_Syntax_Syntax.sigmeta = uu____18767;
                          FStar_Syntax_Syntax.sigattrs = uu____18768;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____18817 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___27_18868  ->
                    match uu___27_18868 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____18877,uu____18878,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____18880;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____18882;
                        FStar_Syntax_Syntax.sigattrs = uu____18883;_} ->
                        let uu____18940 =
                          let uu____18951 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____18951  in
                        (match uu____18940 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____18977,t,uu____18979,uu____18980,uu____18981);
                             FStar_Syntax_Syntax.sigrng = uu____18982;
                             FStar_Syntax_Syntax.sigquals = uu____18983;
                             FStar_Syntax_Syntax.sigmeta = uu____18984;
                             FStar_Syntax_Syntax.sigattrs = uu____18985;_} ->
                             let uu____19034 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____19034 with
                              | (formals,uu____19059) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____19156  ->
                                            match uu____19156 with
                                            | (x,q) ->
                                                let uu____19189 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____19189
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____19297  ->
                                            match uu____19297 with
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
                                  ((let uu____19374 =
                                      let uu____19377 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____19377
                                       in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____19374);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____19442 =
                                            match uu____19442 with
                                            | (id1,uu____19454) ->
                                                let modul =
                                                  let uu____19469 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____19469.FStar_Ident.str
                                                   in
                                                let uu____19478 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____19478 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____19501 =
                                                         let uu____19502 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____19502
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____19501);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____19547
                                                               =
                                                               let uu____19552
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____19552.FStar_Ident.ident
                                                                in
                                                             uu____19547.FStar_Ident.idText
                                                              in
                                                           let uu____19562 =
                                                             let uu____19563
                                                               =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____19563
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____19562))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____19621 -> ())
                    | uu____19627 -> ()))
        | uu____19633 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____19725 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____19725 with
        | (ns,id1) ->
            let uu____19768 = peek_record_cache ()  in
            FStar_Util.find_map uu____19768
              (fun record  ->
                 let uu____19814 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____19870  -> FStar_Pervasives_Native.None)
                   uu____19814)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____19892  -> Cont_ignore) (fun uu____19904  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____19944 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____19944)
        (fun k  -> fun uu____19980  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____20060 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____20060 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____20116 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____20218 = try_lookup_record_by_field_name env lid  in
        match uu____20218 with
        | FStar_Pervasives_Native.Some record' when
            let uu____20253 =
              let uu____20255 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____20255  in
            let uu____20256 =
              let uu____20258 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____20258  in
            uu____20253 = uu____20256 ->
            let uu____20260 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____20264  -> Cont_ok ())
               in
            (match uu____20260 with
             | Cont_ok uu____20276 -> true
             | uu____20278 -> false)
        | uu____20282 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____20360 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____20360 with
      | FStar_Pervasives_Native.Some r ->
          let uu____20405 =
            let uu____20415 =
              let uu____20424 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____20439 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____20424 uu____20439  in
            (uu____20415, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____20405
      | uu____20454 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____20486  ->
    let uu____20487 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____20487
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____20508  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___28_20521  ->
      match uu___28_20521 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___29_20601 =
            match uu___29_20601 with
            | Rec_binding uu____20603 -> true
            | uu____20605 -> false  in
          let this_env =
            let uu___1110_20642 = env  in
            let uu____20677 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___1110_20642.curmodule);
              curmonad = (uu___1110_20642.curmonad);
              modules = (uu___1110_20642.modules);
              scope_mods = uu____20677;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___1110_20642.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___1110_20642.sigaccum);
              sigmap = (uu___1110_20642.sigmap);
              iface = (uu___1110_20642.iface);
              admitted_iface = (uu___1110_20642.admitted_iface);
              expect_typ = (uu___1110_20642.expect_typ);
              docs = (uu___1110_20642.docs);
              remaining_iface_decls = (uu___1110_20642.remaining_iface_decls);
              syntax_only = (uu___1110_20642.syntax_only);
              ds_hooks = (uu___1110_20642.ds_hooks);
              dep_graph = (uu___1110_20642.dep_graph)
            }  in
          let uu____20680 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____20680 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____20713 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___1118_20839 = env  in
      {
        curmodule = (uu___1118_20839.curmodule);
        curmonad = (uu___1118_20839.curmonad);
        modules = (uu___1118_20839.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___1118_20839.exported_ids);
        trans_exported_ids = (uu___1118_20839.trans_exported_ids);
        includes = (uu___1118_20839.includes);
        sigaccum = (uu___1118_20839.sigaccum);
        sigmap = (uu___1118_20839.sigmap);
        iface = (uu___1118_20839.iface);
        admitted_iface = (uu___1118_20839.admitted_iface);
        expect_typ = (uu___1118_20839.expect_typ);
        docs = (uu___1118_20839.docs);
        remaining_iface_decls = (uu___1118_20839.remaining_iface_decls);
        syntax_only = (uu___1118_20839.syntax_only);
        ds_hooks = (uu___1118_20839.ds_hooks);
        dep_graph = (uu___1118_20839.dep_graph)
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
        let uu____21069 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____21069
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____21099 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.op_Hat "Duplicate top-level names " l.FStar_Ident.str))
             uu____21099)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____21256) ->
                let uu____21279 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____21279 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____21300 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____21300
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____21318 =
            let uu____21324 =
              let uu____21326 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____21326 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____21324)  in
          let uu____21330 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21318 uu____21330  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____21390 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____21403 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____21418 -> (false, true)
            | uu____21440 -> (false, false)  in
          match uu____21390 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____21475 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____21497 =
                       let uu____21499 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____21499  in
                     if uu____21497
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____21475 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____21544 ->
                   (extract_record env globals s;
                    (let uu___1159_21552 = env  in
                     {
                       curmodule = (uu___1159_21552.curmodule);
                       curmonad = (uu___1159_21552.curmonad);
                       modules = (uu___1159_21552.modules);
                       scope_mods = (uu___1159_21552.scope_mods);
                       exported_ids = (uu___1159_21552.exported_ids);
                       trans_exported_ids =
                         (uu___1159_21552.trans_exported_ids);
                       includes = (uu___1159_21552.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___1159_21552.sigmap);
                       iface = (uu___1159_21552.iface);
                       admitted_iface = (uu___1159_21552.admitted_iface);
                       expect_typ = (uu___1159_21552.expect_typ);
                       docs = (uu___1159_21552.docs);
                       remaining_iface_decls =
                         (uu___1159_21552.remaining_iface_decls);
                       syntax_only = (uu___1159_21552.syntax_only);
                       ds_hooks = (uu___1159_21552.ds_hooks);
                       dep_graph = (uu___1159_21552.dep_graph)
                     })))
           in
        let env2 =
          let uu___1162_21627 = env1  in
          let uu____21662 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___1162_21627.curmodule);
            curmonad = (uu___1162_21627.curmonad);
            modules = (uu___1162_21627.modules);
            scope_mods = uu____21662;
            exported_ids = (uu___1162_21627.exported_ids);
            trans_exported_ids = (uu___1162_21627.trans_exported_ids);
            includes = (uu___1162_21627.includes);
            sigaccum = (uu___1162_21627.sigaccum);
            sigmap = (uu___1162_21627.sigmap);
            iface = (uu___1162_21627.iface);
            admitted_iface = (uu___1162_21627.admitted_iface);
            expect_typ = (uu___1162_21627.expect_typ);
            docs = (uu___1162_21627.docs);
            remaining_iface_decls = (uu___1162_21627.remaining_iface_decls);
            syntax_only = (uu___1162_21627.syntax_only);
            ds_hooks = (uu___1162_21627.ds_hooks);
            dep_graph = (uu___1162_21627.dep_graph)
          }  in
        let uu____21688 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____21766) ->
              let uu____21793 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____21793)
          | uu____21883 ->
              (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____21688 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____22082  ->
                     match uu____22082 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____22143 =
                                    let uu____22146 =
                                      FStar_ST.op_Bang globals  in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____22146
                                     in
                                  FStar_ST.op_Colon_Equals globals
                                    uu____22143);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____22197 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____22197.FStar_Ident.str  in
                                      ((let uu____22207 =
                                          get_exported_id_set env3 modul  in
                                        match uu____22207 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____22229 =
                                              let uu____22230 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____22230
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____22229
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
                let uu___1187_22331 = env3  in
                let uu____22366 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___1187_22331.curmodule);
                  curmonad = (uu___1187_22331.curmonad);
                  modules = (uu___1187_22331.modules);
                  scope_mods = uu____22366;
                  exported_ids = (uu___1187_22331.exported_ids);
                  trans_exported_ids = (uu___1187_22331.trans_exported_ids);
                  includes = (uu___1187_22331.includes);
                  sigaccum = (uu___1187_22331.sigaccum);
                  sigmap = (uu___1187_22331.sigmap);
                  iface = (uu___1187_22331.iface);
                  admitted_iface = (uu___1187_22331.admitted_iface);
                  expect_typ = (uu___1187_22331.expect_typ);
                  docs = (uu___1187_22331.docs);
                  remaining_iface_decls =
                    (uu___1187_22331.remaining_iface_decls);
                  syntax_only = (uu___1187_22331.syntax_only);
                  ds_hooks = (uu___1187_22331.ds_hooks);
                  dep_graph = (uu___1187_22331.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____22608 =
        let uu____22617 = resolve_module_name env ns false  in
        match uu____22617 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____22656 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____22698  ->
                      match uu____22698 with
                      | (m,uu____22717) ->
                          let uu____22742 =
                            let uu____22744 = FStar_Ident.text_of_lid m  in
                            Prims.op_Hat uu____22744 "."  in
                          let uu____22747 =
                            let uu____22749 = FStar_Ident.text_of_lid ns  in
                            Prims.op_Hat uu____22749 "."  in
                          FStar_Util.starts_with uu____22742 uu____22747))
               in
            if uu____22656
            then (ns, Open_namespace)
            else
              (let uu____22767 =
                 let uu____22773 =
                   let uu____22775 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____22775
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____22773)  in
               let uu____22779 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____22767 uu____22779)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____22608 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____22917 = resolve_module_name env ns false  in
      match uu____22917 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____22994 = current_module env1  in
              uu____22994.FStar_Ident.str  in
            (let uu____23004 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____23004 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____23048 =
                   let uu____23055 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____23055
                    in
                 FStar_ST.op_Colon_Equals incl uu____23048);
            (match () with
             | () ->
                 let uu____23145 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____23145 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____23182 =
                          let uu____23279 = get_exported_id_set env1 curmod
                             in
                          let uu____23326 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____23279, uu____23326)  in
                        match uu____23182 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____23742 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____23742  in
                              let ex = cur_exports k  in
                              (let uu____23843 =
                                 let uu____23847 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____23847 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____23843);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____23939 =
                                     let uu____23943 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____23943 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____23939)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____23992 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____24111 =
                        let uu____24117 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____24117)
                         in
                      let uu____24121 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____24111 uu____24121))))
      | uu____24139 ->
          let uu____24146 =
            let uu____24152 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____24152)  in
          let uu____24156 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____24146 uu____24156
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____24253 = module_is_defined env l  in
        if uu____24253
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____24283 =
             let uu____24289 =
               let uu____24291 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____24291  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____24289)  in
           let uu____24295 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____24283 uu____24295)
  
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
            ((let uu____24411 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____24411 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____24415 = FStar_Ident.range_of_lid l  in
                  let uu____24416 =
                    let uu____24422 =
                      let uu____24424 = FStar_Ident.string_of_lid l  in
                      let uu____24426 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____24428 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____24424 uu____24426 uu____24428
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____24422)  in
                  FStar_Errors.log_issue uu____24415 uu____24416);
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
                      let uu____24583 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____24583 ->
                      let uu____24588 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____24588 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____24617;
                              FStar_Syntax_Syntax.sigrng = uu____24618;
                              FStar_Syntax_Syntax.sigquals = uu____24619;
                              FStar_Syntax_Syntax.sigmeta = uu____24620;
                              FStar_Syntax_Syntax.sigattrs = uu____24621;_},uu____24622)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____24660;
                              FStar_Syntax_Syntax.sigrng = uu____24661;
                              FStar_Syntax_Syntax.sigquals = uu____24662;
                              FStar_Syntax_Syntax.sigmeta = uu____24663;
                              FStar_Syntax_Syntax.sigattrs = uu____24664;_},uu____24665)
                           -> lids
                       | uu____24725 ->
                           ((let uu____24739 =
                               let uu____24741 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____24741  in
                             if uu____24739
                             then
                               let uu____24744 = FStar_Ident.range_of_lid l
                                  in
                               let uu____24745 =
                                 let uu____24751 =
                                   let uu____24753 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____24753
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____24751)
                                  in
                               FStar_Errors.log_issue uu____24744 uu____24745
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___1290_24780 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___1290_24780.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___1290_24780.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___1290_24780.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___1290_24780.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____24796 -> lids) [])
         in
      let uu___1295_24801 = m  in
      let uu____24818 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____24853,uu____24854) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___1304_24881 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1304_24881.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1304_24881.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1304_24881.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1304_24881.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____24892 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___1295_24801.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____24818;
        FStar_Syntax_Syntax.exports =
          (uu___1295_24801.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___1295_24801.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____24998) ->
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
                                (lid,uu____25052,uu____25053,uu____25054,uu____25055,uu____25056)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____25109,uu____25110)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____25164 =
                                        let uu____25179 =
                                          let uu____25188 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____25189 =
                                            let uu____25196 =
                                              let uu____25197 =
                                                let uu____25221 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____25221)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____25197
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____25196
                                             in
                                          uu____25189
                                            FStar_Pervasives_Native.None
                                            uu____25188
                                           in
                                        (lid, univ_names, uu____25179)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____25164
                                       in
                                    let se2 =
                                      let uu___1336_25270 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___1336_25270.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___1336_25270.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___1336_25270.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____25300 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____25304,uu____25305) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____25335,lbs),uu____25337)
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
                             let uu____25398 =
                               let uu____25400 =
                                 let uu____25409 =
                                   let uu____25419 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____25419.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____25409.FStar_Syntax_Syntax.v  in
                               uu____25400.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____25398))
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
                               let uu____25488 =
                                 let uu____25498 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____25498.FStar_Syntax_Syntax.fv_name  in
                               uu____25488.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___1359_25531 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___1359_25531.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___1359_25531.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___1359_25531.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____25569 -> ()));
      (let curmod =
         let uu____25572 = current_module env  in uu____25572.FStar_Ident.str
          in
       (let uu____25582 =
          let uu____25679 = get_exported_id_set env curmod  in
          let uu____25726 = get_trans_exported_id_set env curmod  in
          (uu____25679, uu____25726)  in
        match uu____25582 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____26145 = cur_ex eikind  in
                FStar_ST.op_Bang uu____26145  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____26251 =
                let uu____26255 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____26255  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____26251  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____26304 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___1377_26436 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___1377_26436.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___1377_26436.exported_ids);
                    trans_exported_ids = (uu___1377_26436.trans_exported_ids);
                    includes = (uu___1377_26436.includes);
                    sigaccum = [];
                    sigmap = (uu___1377_26436.sigmap);
                    iface = (uu___1377_26436.iface);
                    admitted_iface = (uu___1377_26436.admitted_iface);
                    expect_typ = (uu___1377_26436.expect_typ);
                    docs = (uu___1377_26436.docs);
                    remaining_iface_decls =
                      (uu___1377_26436.remaining_iface_decls);
                    syntax_only = (uu___1377_26436.syntax_only);
                    ds_hooks = (uu___1377_26436.ds_hooks);
                    dep_graph = (uu___1377_26436.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____26649  ->
         push_record_cache ();
         (let uu____26652 =
            let uu____26672 = FStar_ST.op_Bang stack  in env :: uu____26672
             in
          FStar_ST.op_Colon_Equals stack uu____26652);
         (let uu___1383_26823 = env  in
          let uu____26858 = FStar_Util.smap_copy env.exported_ids  in
          let uu____26863 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____26868 = FStar_Util.smap_copy env.includes  in
          let uu____26887 = FStar_Util.smap_copy env.sigmap  in
          let uu____26910 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___1383_26823.curmodule);
            curmonad = (uu___1383_26823.curmonad);
            modules = (uu___1383_26823.modules);
            scope_mods = (uu___1383_26823.scope_mods);
            exported_ids = uu____26858;
            trans_exported_ids = uu____26863;
            includes = uu____26868;
            sigaccum = (uu___1383_26823.sigaccum);
            sigmap = uu____26887;
            iface = (uu___1383_26823.iface);
            admitted_iface = (uu___1383_26823.admitted_iface);
            expect_typ = (uu___1383_26823.expect_typ);
            docs = uu____26910;
            remaining_iface_decls = (uu___1383_26823.remaining_iface_decls);
            syntax_only = (uu___1383_26823.syntax_only);
            ds_hooks = (uu___1383_26823.ds_hooks);
            dep_graph = (uu___1383_26823.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____26935  ->
    FStar_Util.atomically
      (fun uu____26959  ->
         let uu____26960 = FStar_ST.op_Bang stack  in
         match uu____26960 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____27168 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____27471 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____27487 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____27582 = FStar_Util.smap_try_find sm' k  in
              match uu____27582 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___1418_27674 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___1418_27674.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1418_27674.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1418_27674.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1418_27674.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____27685 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____27703 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____27834 = finish env modul1  in (uu____27834, modul1)
  
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
      let uu____27978 =
        let uu____27982 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____27982  in
      FStar_Util.set_elements uu____27978  in
    let fields =
      let uu____28045 =
        let uu____28049 = e Exported_id_field  in
        FStar_ST.op_Bang uu____28049  in
      FStar_Util.set_elements uu____28045  in
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
          let uu____28151 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____28151  in
        let fields =
          let uu____28165 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____28165  in
        (fun uu___30_28173  ->
           match uu___30_28173 with
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
  'Auu____28366 .
    'Auu____28366 Prims.list FStar_Pervasives_Native.option ->
      'Auu____28366 Prims.list FStar_ST.ref
  =
  fun uu___31_28379  ->
    match uu___31_28379 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____28469 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____28469 as_exported_ids  in
      let uu____28477 = as_ids_opt env.exported_ids  in
      let uu____28482 = as_ids_opt env.trans_exported_ids  in
      let uu____28487 =
        let uu____28496 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____28496 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____28477;
        mii_trans_exported_ids = uu____28482;
        mii_includes = uu____28487
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
                let uu____28729 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____28729 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___32_28759 =
                  match uu___32_28759 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____28779  ->
                     match uu____28779 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____28835 =
                    let uu____28844 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____28844, Open_namespace)  in
                  [uu____28835]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____28911 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____28911);
              (match () with
               | () ->
                   ((let uu____28933 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____28933);
                    (match () with
                     | () ->
                         ((let uu____28955 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____28955);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___1488_29028 = env1  in
                                 let uu____29063 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___1488_29028.curmonad);
                                   modules = (uu___1488_29028.modules);
                                   scope_mods = uu____29063;
                                   exported_ids =
                                     (uu___1488_29028.exported_ids);
                                   trans_exported_ids =
                                     (uu___1488_29028.trans_exported_ids);
                                   includes = (uu___1488_29028.includes);
                                   sigaccum = (uu___1488_29028.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___1488_29028.expect_typ);
                                   docs = (uu___1488_29028.docs);
                                   remaining_iface_decls =
                                     (uu___1488_29028.remaining_iface_decls);
                                   syntax_only =
                                     (uu___1488_29028.syntax_only);
                                   ds_hooks = (uu___1488_29028.ds_hooks);
                                   dep_graph = (uu___1488_29028.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____29083 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____29157  ->
                      match uu____29157 with
                      | (l,uu____29176) -> FStar_Ident.lid_equals l mname))
               in
            match uu____29083 with
            | FStar_Pervasives_Native.None  ->
                let uu____29239 = prep env  in (uu____29239, false)
            | FStar_Pervasives_Native.Some (uu____29293,m) ->
                ((let uu____29336 =
                    (let uu____29340 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____29340) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____29336
                  then
                    let uu____29343 =
                      let uu____29349 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____29349)
                       in
                    let uu____29353 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____29343 uu____29353
                  else ());
                 (let uu____29356 =
                    let uu____29391 = push env  in prep uu____29391  in
                  (uu____29356, true)))
  
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
          let uu___1509_29555 = env  in
          {
            curmodule = (uu___1509_29555.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___1509_29555.modules);
            scope_mods = (uu___1509_29555.scope_mods);
            exported_ids = (uu___1509_29555.exported_ids);
            trans_exported_ids = (uu___1509_29555.trans_exported_ids);
            includes = (uu___1509_29555.includes);
            sigaccum = (uu___1509_29555.sigaccum);
            sigmap = (uu___1509_29555.sigmap);
            iface = (uu___1509_29555.iface);
            admitted_iface = (uu___1509_29555.admitted_iface);
            expect_typ = (uu___1509_29555.expect_typ);
            docs = (uu___1509_29555.docs);
            remaining_iface_decls = (uu___1509_29555.remaining_iface_decls);
            syntax_only = (uu___1509_29555.syntax_only);
            ds_hooks = (uu___1509_29555.ds_hooks);
            dep_graph = (uu___1509_29555.dep_graph)
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
        let uu____29676 = lookup1 lid  in
        match uu____29676 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____29703  ->
                   match uu____29703 with
                   | (lid1,uu____29722) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____29749 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____29749  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____29771 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____29780 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____29771 uu____29780  in
                 let uu____29781 = resolve_module_name env modul true  in
                 match uu____29781 with
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
            let uu____29826 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____29826
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____29864 = lookup1 id1  in
      match uu____29864 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.op_Hat "Identifier not found ["
                 (Prims.op_Hat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  