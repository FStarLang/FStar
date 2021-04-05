open Prims
type used_marker = Prims.bool FStar_ST.ref
type local_binding =
  (FStar_Ident.ident * FStar_Syntax_Syntax.bv * used_marker)
type rec_binding =
  (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth *
    used_marker)
type module_abbrev = (FStar_Ident.ident * FStar_Ident.lident)
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_module -> true | uu___ -> false
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Open_namespace -> true | uu___ -> false
type open_module_or_namespace = (FStar_Ident.lident * open_kind)
type record_or_dc =
  {
  typename: FStar_Ident.lident ;
  constrname: FStar_Ident.ident ;
  parms: FStar_Syntax_Syntax.binders ;
  fields: (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list ;
  is_private: Prims.bool ;
  is_record: Prims.bool }
let (__proj__Mkrecord_or_dc__item__typename :
  record_or_dc -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        typename
let (__proj__Mkrecord_or_dc__item__constrname :
  record_or_dc -> FStar_Ident.ident) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        constrname
let (__proj__Mkrecord_or_dc__item__parms :
  record_or_dc -> FStar_Syntax_Syntax.binders) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        parms
let (__proj__Mkrecord_or_dc__item__fields :
  record_or_dc -> (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        fields
let (__proj__Mkrecord_or_dc__item__is_private : record_or_dc -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        is_private
let (__proj__Mkrecord_or_dc__item__is_record : record_or_dc -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        is_record
type scope_mod =
  | Local_binding of local_binding 
  | Rec_binding of rec_binding 
  | Module_abbrev of module_abbrev 
  | Open_module_or_namespace of open_module_or_namespace 
  | Top_level_def of FStar_Ident.ident 
  | Record_or_dc of record_or_dc 
let (uu___is_Local_binding : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Local_binding _0 -> true | uu___ -> false
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee -> match projectee with | Local_binding _0 -> _0
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Rec_binding _0 -> true | uu___ -> false
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee -> match projectee with | Rec_binding _0 -> _0
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Module_abbrev _0 -> true | uu___ -> false
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee -> match projectee with | Module_abbrev _0 -> _0
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu___ -> false
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee -> match projectee with | Open_module_or_namespace _0 -> _0
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Top_level_def _0 -> true | uu___ -> false
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee -> match projectee with | Top_level_def _0 -> _0
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_or_dc _0 -> true | uu___ -> false
let (__proj__Record_or_dc__item___0 : scope_mod -> record_or_dc) =
  fun projectee -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStar_Util.set
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field 
let (uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_term_type -> true | uu___ -> false
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_field -> true | uu___ -> false
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
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmodule
let (__proj__Mkenv__item__curmonad :
  env -> FStar_Ident.ident FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmonad
let (__proj__Mkenv__item__modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> modules
let (__proj__Mkenv__item__scope_mods : env -> scope_mod Prims.list) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> scope_mods
let (__proj__Mkenv__item__exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> exported_ids
let (__proj__Mkenv__item__trans_exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> trans_exported_ids
let (__proj__Mkenv__item__includes :
  env -> FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> includes
let (__proj__Mkenv__item__sigaccum : env -> FStar_Syntax_Syntax.sigelts) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> sigaccum
let (__proj__Mkenv__item__sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> sigmap
let (__proj__Mkenv__item__iface : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> iface
let (__proj__Mkenv__item__admitted_iface : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> admitted_iface
let (__proj__Mkenv__item__expect_typ : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> expect_typ
let (__proj__Mkenv__item__remaining_iface_decls :
  env -> (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> remaining_iface_decls
let (__proj__Mkenv__item__syntax_only : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> syntax_only
let (__proj__Mkenv__item__ds_hooks : env -> dsenv_hooks) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> ds_hooks
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> dep_graph
let (__proj__Mkdsenv_hooks__item__ds_push_open_hook :
  dsenv_hooks -> env -> open_module_or_namespace -> unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_open_hook
let (__proj__Mkdsenv_hooks__item__ds_push_include_hook :
  dsenv_hooks -> env -> FStar_Ident.lident -> unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_include_hook
let (__proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook :
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_module_abbrev_hook
type 'a withenv = env -> ('a * env)
let (default_ds_hooks : dsenv_hooks) =
  {
    ds_push_open_hook = (fun uu___ -> fun uu___1 -> ());
    ds_push_include_hook = (fun uu___ -> fun uu___1 -> ());
    ds_push_module_abbrev_hook =
      (fun uu___ -> fun uu___1 -> fun uu___2 -> ())
  }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Term_name _0 -> true | uu___ -> false
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee -> match projectee with | Term_name _0 -> _0
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Eff_name _0 -> true | uu___ -> false
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee -> match projectee with | Eff_name _0 -> _0
let (set_iface : env -> Prims.bool -> env) =
  fun env1 ->
    fun b ->
      let uu___ = env1 in
      {
        curmodule = (uu___.curmodule);
        curmonad = (uu___.curmonad);
        modules = (uu___.modules);
        scope_mods = (uu___.scope_mods);
        exported_ids = (uu___.exported_ids);
        trans_exported_ids = (uu___.trans_exported_ids);
        includes = (uu___.includes);
        sigaccum = (uu___.sigaccum);
        sigmap = (uu___.sigmap);
        iface = b;
        admitted_iface = (uu___.admitted_iface);
        expect_typ = (uu___.expect_typ);
        remaining_iface_decls = (uu___.remaining_iface_decls);
        syntax_only = (uu___.syntax_only);
        ds_hooks = (uu___.ds_hooks);
        dep_graph = (uu___.dep_graph)
      }
let (iface : env -> Prims.bool) = fun e -> e.iface
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___ = e in
      {
        curmodule = (uu___.curmodule);
        curmonad = (uu___.curmonad);
        modules = (uu___.modules);
        scope_mods = (uu___.scope_mods);
        exported_ids = (uu___.exported_ids);
        trans_exported_ids = (uu___.trans_exported_ids);
        includes = (uu___.includes);
        sigaccum = (uu___.sigaccum);
        sigmap = (uu___.sigmap);
        iface = (uu___.iface);
        admitted_iface = b;
        expect_typ = (uu___.expect_typ);
        remaining_iface_decls = (uu___.remaining_iface_decls);
        syntax_only = (uu___.syntax_only);
        ds_hooks = (uu___.ds_hooks);
        dep_graph = (uu___.dep_graph)
      }
let (admitted_iface : env -> Prims.bool) = fun e -> e.admitted_iface
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      let uu___ = e in
      {
        curmodule = (uu___.curmodule);
        curmonad = (uu___.curmonad);
        modules = (uu___.modules);
        scope_mods = (uu___.scope_mods);
        exported_ids = (uu___.exported_ids);
        trans_exported_ids = (uu___.trans_exported_ids);
        includes = (uu___.includes);
        sigaccum = (uu___.sigaccum);
        sigmap = (uu___.sigmap);
        iface = (uu___.iface);
        admitted_iface = (uu___.admitted_iface);
        expect_typ = b;
        remaining_iface_decls = (uu___.remaining_iface_decls);
        syntax_only = (uu___.syntax_only);
        ds_hooks = (uu___.ds_hooks);
        dep_graph = (uu___.dep_graph)
      }
let (expect_typ : env -> Prims.bool) = fun e -> e.expect_typ
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type]
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env1 ->
    fun lid ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu___ =
        FStar_Util.smap_try_find env1.trans_exported_ids module_name in
      match uu___ with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some exported_id_set1 ->
          let uu___1 =
            let uu___2 = exported_id_set1 Exported_id_term_type in
            FStar_ST.op_Bang uu___2 in
          FStar_All.pipe_right uu___1 FStar_Util.set_elements
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e -> e.modules
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env1 ->
    FStar_List.filter_map
      (fun uu___ ->
         match uu___ with
         | Open_module_or_namespace (lid, _info) ->
             FStar_Pervasives_Native.Some lid
         | uu___1 -> FStar_Pervasives_Native.None) env1.scope_mods
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e ->
    fun l ->
      let uu___ = e in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___.curmonad);
        modules = (uu___.modules);
        scope_mods = (uu___.scope_mods);
        exported_ids = (uu___.exported_ids);
        trans_exported_ids = (uu___.trans_exported_ids);
        includes = (uu___.includes);
        sigaccum = (uu___.sigaccum);
        sigmap = (uu___.sigmap);
        iface = (uu___.iface);
        admitted_iface = (uu___.admitted_iface);
        expect_typ = (uu___.expect_typ);
        remaining_iface_decls = (uu___.remaining_iface_decls);
        syntax_only = (uu___.syntax_only);
        ds_hooks = (uu___.ds_hooks);
        dep_graph = (uu___.dep_graph)
      }
let (current_module : env -> FStar_Ident.lident) =
  fun env1 ->
    match env1.curmodule with
    | FStar_Pervasives_Native.None -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
let (iface_decls :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ =
        FStar_All.pipe_right env1.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu___1 ->
                match uu___1 with | (m, uu___2) -> FStar_Ident.lid_equals l m)) in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu___1, decls) ->
          FStar_Pervasives_Native.Some decls
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env1 ->
    fun l ->
      fun ds ->
        let uu___ =
          FStar_List.partition
            (fun uu___1 ->
               match uu___1 with | (m, uu___2) -> FStar_Ident.lid_equals l m)
            env1.remaining_iface_decls in
        match uu___ with
        | (uu___1, rest) ->
            let uu___2 = env1 in
            {
              curmodule = (uu___2.curmodule);
              curmonad = (uu___2.curmonad);
              modules = (uu___2.modules);
              scope_mods = (uu___2.scope_mods);
              exported_ids = (uu___2.exported_ids);
              trans_exported_ids = (uu___2.trans_exported_ids);
              includes = (uu___2.includes);
              sigaccum = (uu___2.sigaccum);
              sigmap = (uu___2.sigmap);
              iface = (uu___2.iface);
              admitted_iface = (uu___2.admitted_iface);
              expect_typ = (uu___2.expect_typ);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___2.syntax_only);
              ds_hooks = (uu___2.ds_hooks);
              dep_graph = (uu___2.dep_graph)
            }
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Ident.qual_id
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env1 ->
    fun id ->
      match env1.curmonad with
      | FStar_Pervasives_Native.None ->
          let uu___ = current_module env1 in qual uu___ id
      | FStar_Pervasives_Native.Some monad ->
          let uu___ = let uu___1 = current_module env1 in qual uu___1 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu___ id
let (syntax_only : env -> Prims.bool) = fun env1 -> env1.syntax_only
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env1 ->
    fun b ->
      let uu___ = env1 in
      {
        curmodule = (uu___.curmodule);
        curmonad = (uu___.curmonad);
        modules = (uu___.modules);
        scope_mods = (uu___.scope_mods);
        exported_ids = (uu___.exported_ids);
        trans_exported_ids = (uu___.trans_exported_ids);
        includes = (uu___.includes);
        sigaccum = (uu___.sigaccum);
        sigmap = (uu___.sigmap);
        iface = (uu___.iface);
        admitted_iface = (uu___.admitted_iface);
        expect_typ = (uu___.expect_typ);
        remaining_iface_decls = (uu___.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___.ds_hooks);
        dep_graph = (uu___.dep_graph)
      }
let (ds_hooks : env -> dsenv_hooks) = fun env1 -> env1.ds_hooks
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env1 ->
    fun hooks ->
      let uu___ = env1 in
      {
        curmodule = (uu___.curmodule);
        curmonad = (uu___.curmonad);
        modules = (uu___.modules);
        scope_mods = (uu___.scope_mods);
        exported_ids = (uu___.exported_ids);
        trans_exported_ids = (uu___.trans_exported_ids);
        includes = (uu___.includes);
        sigaccum = (uu___.sigaccum);
        sigmap = (uu___.sigmap);
        iface = (uu___.iface);
        admitted_iface = (uu___.admitted_iface);
        expect_typ = (uu___.expect_typ);
        remaining_iface_decls = (uu___.remaining_iface_decls);
        syntax_only = (uu___.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___.dep_graph)
      }
let new_sigmap : 'uuuuu . unit -> 'uuuuu FStar_Util.smap =
  fun uu___ -> FStar_Util.smap_create (Prims.of_int (100))
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps ->
    let uu___ = new_sigmap () in
    let uu___1 = new_sigmap () in
    let uu___2 = new_sigmap () in
    let uu___3 = new_sigmap () in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu___;
      trans_exported_ids = uu___1;
      includes = uu___2;
      sigaccum = [];
      sigmap = uu___3;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env1 -> env1.dep_graph
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env1 ->
    fun ds ->
      let uu___ = env1 in
      {
        curmodule = (uu___.curmodule);
        curmonad = (uu___.curmonad);
        modules = (uu___.modules);
        scope_mods = (uu___.scope_mods);
        exported_ids = (uu___.exported_ids);
        trans_exported_ids = (uu___.trans_exported_ids);
        includes = (uu___.includes);
        sigaccum = (uu___.sigaccum);
        sigmap = (uu___.sigmap);
        iface = (uu___.iface);
        admitted_iface = (uu___.admitted_iface);
        expect_typ = (uu___.expect_typ);
        remaining_iface_decls = (uu___.remaining_iface_decls);
        syntax_only = (uu___.syntax_only);
        ds_hooks = (uu___.ds_hooks);
        dep_graph = ds
      }
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env1 -> env1.sigmap
let (has_all_in_scope : env -> Prims.bool) =
  fun env1 ->
    FStar_List.existsb
      (fun uu___ ->
         match uu___ with
         | (m, uu___1) -> FStar_Ident.lid_equals m FStar_Parser_Const.all_lid)
      env1.modules
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv ->
    fun r ->
      let id = FStar_Ident.set_id_range r bv.FStar_Syntax_Syntax.ppname in
      let uu___ = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___.FStar_Syntax_Syntax.sort)
      }
let (bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun bv ->
    fun r ->
      let uu___ = set_bv_range bv r in FStar_Syntax_Syntax.bv_to_name uu___
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
  fun id ->
    FStar_Util.find_map unmangleMap
      (fun uu___ ->
         match uu___ with
         | (x, y, dd, dq) ->
             let uu___1 =
               let uu___2 = FStar_Ident.string_of_id id in uu___2 = x in
             if uu___1
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_Ident.range_of_id id in
                   FStar_Ident.lid_of_path ["Prims"; y] uu___4 in
                 FStar_Syntax_Syntax.fvar uu___3 dd dq in
               FStar_Pervasives_Native.Some uu___2
             else FStar_Pervasives_Native.None)
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee -> match projectee with | Cont_ok _0 -> true | uu___ -> false
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee -> match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee -> match projectee with | Cont_fail -> true | uu___ -> false
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee ->
    match projectee with | Cont_ignore -> true | uu___ -> false
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore ->
    fun uu___ ->
      match uu___ with
      | Cont_ok a1 -> FStar_Pervasives_Native.Some a1
      | Cont_fail -> FStar_Pervasives_Native.None
      | Cont_ignore -> k_ignore ()
let find_in_record :
  'uuuuu .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc -> (record_or_dc -> 'uuuuu cont_t) -> 'uuuuu cont_t
  =
  fun ns ->
    fun id ->
      fun record ->
        fun cont ->
          let typename' =
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_Ident.ident_of_lid record.typename in
                [uu___2] in
              FStar_List.append ns uu___1 in
            FStar_Ident.lid_of_ids uu___ in
          let uu___ = FStar_Ident.lid_equals typename' record.typename in
          if uu___
          then
            let fname =
              let uu___1 =
                let uu___2 = FStar_Ident.ns_of_lid record.typename in
                FStar_List.append uu___2 [id] in
              FStar_Ident.lid_of_ids uu___1 in
            let find =
              FStar_Util.find_map record.fields
                (fun uu___1 ->
                   match uu___1 with
                   | (f, uu___2) ->
                       let uu___3 =
                         let uu___4 = FStar_Ident.string_of_id id in
                         let uu___5 = FStar_Ident.string_of_id f in
                         uu___4 = uu___5 in
                       if uu___3
                       then FStar_Pervasives_Native.Some record
                       else FStar_Pervasives_Native.None) in
            match find with
            | FStar_Pervasives_Native.Some r -> cont r
            | FStar_Pervasives_Native.None -> Cont_ignore
          else Cont_ignore
let (get_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option)
  = fun e -> fun mname -> FStar_Util.smap_try_find e.exported_ids mname
let (get_trans_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option)
  = fun e -> fun mname -> FStar_Util.smap_try_find e.trans_exported_ids mname
let (string_of_exported_id_kind : exported_id_kind -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Exported_id_field -> "field"
    | Exported_id_term_type -> "term/type"
let find_in_module_with_includes :
  'a .
    exported_id_kind ->
      (FStar_Ident.lident -> 'a cont_t) ->
        'a cont_t ->
          env -> FStar_Ident.lident -> FStar_Ident.ident -> 'a cont_t
  =
  fun eikind ->
    fun find_in_module ->
      fun find_in_module_default ->
        fun env1 ->
          fun ns ->
            fun id ->
              let idstr = FStar_Ident.string_of_id id in
              let rec aux uu___ =
                match uu___ with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = FStar_Ident.string_of_lid modul in
                    let not_shadowed =
                      let uu___1 = get_exported_id_set env1 mname in
                      match uu___1 with
                      | FStar_Pervasives_Native.None -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu___2 = mex eikind in
                            FStar_ST.op_Bang uu___2 in
                          FStar_Util.set_mem idstr mexports in
                    let mincludes =
                      let uu___1 =
                        FStar_Util.smap_try_find env1.includes mname in
                      match uu___1 with
                      | FStar_Pervasives_Native.None -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc in
                    let look_into =
                      if not_shadowed
                      then
                        let uu___1 = qual modul id in find_in_module uu___1
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore -> aux (FStar_List.append mincludes q)
                     | uu___1 -> look_into) in
              aux [ns]
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___ -> match uu___ with | Exported_id_field -> true | uu___1 -> false
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
  fun env1 ->
    fun id ->
      fun eikind ->
        fun k_local_binding ->
          fun k_rec_binding ->
            fun k_record ->
              fun find_in_module ->
                fun lookup_default_id ->
                  let check_local_binding_id uu___ =
                    match uu___ with
                    | (id', uu___1, uu___2) ->
                        let uu___3 = FStar_Ident.string_of_id id' in
                        let uu___4 = FStar_Ident.string_of_id id in
                        uu___3 = uu___4 in
                  let check_rec_binding_id uu___ =
                    match uu___ with
                    | (id', uu___1, uu___2, uu___3) ->
                        let uu___4 = FStar_Ident.string_of_id id' in
                        let uu___5 = FStar_Ident.string_of_id id in
                        uu___4 = uu___5 in
                  let curmod_ns =
                    let uu___ = current_module env1 in
                    FStar_Ident.ids_of_lid uu___ in
                  let proc uu___ =
                    match uu___ with
                    | Local_binding l when check_local_binding_id l ->
                        let uu___1 = l in
                        (match uu___1 with
                         | (uu___2, uu___3, used_marker1) ->
                             (FStar_ST.op_Colon_Equals used_marker1 true;
                              k_local_binding l))
                    | Rec_binding r when check_rec_binding_id r ->
                        let uu___1 = r in
                        (match uu___1 with
                         | (uu___2, uu___3, uu___4, used_marker1) ->
                             (FStar_ST.op_Colon_Equals used_marker1 true;
                              k_rec_binding r))
                    | Open_module_or_namespace (ns, Open_module) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env1 ns id
                    | Top_level_def id' when
                        let uu___1 = FStar_Ident.string_of_id id' in
                        let uu___2 = FStar_Ident.string_of_id id in
                        uu___1 = uu___2 -> lookup_default_id Cont_ignore id
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu___1 = FStar_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid ->
                             let id1 = FStar_Ident.ident_of_lid lid in
                             let uu___2 = FStar_Ident.ns_of_lid lid in
                             find_in_record uu___2 id1 r k_record)
                          Cont_ignore env1 uu___1 id
                    | uu___1 -> Cont_ignore in
                  let rec aux uu___ =
                    match uu___ with
                    | a1::q ->
                        let uu___1 = proc a1 in
                        option_of_cont (fun uu___2 -> aux q) uu___1
                    | [] ->
                        let uu___1 = lookup_default_id Cont_fail id in
                        option_of_cont
                          (fun uu___2 -> FStar_Pervasives_Native.None) uu___1 in
                  aux env1.scope_mods
let found_local_binding :
  'uuuuu 'uuuuu1 .
    FStar_Range.range ->
      ('uuuuu * FStar_Syntax_Syntax.bv * 'uuuuu1) -> FStar_Syntax_Syntax.term
  =
  fun r -> fun uu___ -> match uu___ with | (id', x, uu___1) -> bv_to_name x r
let find_in_module :
  'uuuuu .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'uuuuu)
          -> 'uuuuu -> 'uuuuu
  =
  fun env1 ->
    fun lid ->
      fun k_global_def ->
        fun k_not_found ->
          let uu___ =
            let uu___1 = FStar_Ident.string_of_lid lid in
            FStar_Util.smap_try_find (sigmap env1) uu___1 in
          match uu___ with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None -> k_not_found
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun id ->
      let uu___ = unmangleOpName id in
      match uu___ with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu___1 ->
          try_lookup_id'' env1 id Exported_id_term_type
            (fun r ->
               let uu___2 =
                 let uu___3 = FStar_Ident.range_of_id id in
                 found_local_binding uu___3 r in
               Cont_ok uu___2) (fun uu___2 -> Cont_fail)
            (fun uu___2 -> Cont_ignore)
            (fun i ->
               find_in_module env1 i (fun uu___2 -> fun uu___3 -> Cont_fail)
                 Cont_ignore) (fun uu___2 -> fun uu___3 -> Cont_fail)
let lookup_default_id :
  'a .
    env ->
      FStar_Ident.ident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'a cont_t)
          -> 'a cont_t -> 'a cont_t
  =
  fun env1 ->
    fun id ->
      fun k_global_def ->
        fun k_not_found ->
          let find_in_monad =
            match env1.curmonad with
            | FStar_Pervasives_Native.Some uu___ ->
                let lid = qualify env1 id in
                let uu___1 =
                  let uu___2 = FStar_Ident.string_of_lid lid in
                  FStar_Util.smap_try_find (sigmap env1) uu___2 in
                (match uu___1 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu___2 = k_global_def lid r in
                     FStar_Pervasives_Native.Some uu___2
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v -> v
          | FStar_Pervasives_Native.None ->
              let lid = let uu___ = current_module env1 in qual uu___ id in
              find_in_module env1 lid k_global_def k_not_found
let (lid_is_curmod : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      match env1.curmodule with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some m -> FStar_Ident.lid_equals lid m
let (module_is_defined : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      (lid_is_curmod env1 lid) ||
        (FStar_List.existsb
           (fun x ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env1.modules)
let (resolve_module_name :
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      fun honor_ns ->
        let nslen =
          let uu___ = FStar_Ident.ns_of_lid lid in FStar_List.length uu___ in
        let rec aux uu___ =
          match uu___ with
          | [] ->
              let uu___1 = module_is_defined env1 lid in
              if uu___1
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns, Open_namespace))::q when honor_ns
              ->
              let new_lid =
                let uu___1 =
                  let uu___2 = FStar_Ident.path_of_lid ns in
                  let uu___3 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu___2 uu___3 in
                let uu___2 = FStar_Ident.range_of_lid lid in
                FStar_Ident.lid_of_path uu___1 uu___2 in
              let uu___1 = module_is_defined env1 new_lid in
              if uu___1 then FStar_Pervasives_Native.Some new_lid else aux q
          | (Module_abbrev (name, modul))::uu___1 when
              (nslen = Prims.int_zero) &&
                (let uu___2 = FStar_Ident.string_of_id name in
                 let uu___3 =
                   let uu___4 = FStar_Ident.ident_of_lid lid in
                   FStar_Ident.string_of_id uu___4 in
                 uu___2 = uu___3)
              -> FStar_Pervasives_Native.Some modul
          | uu___1::q -> aux q in
        aux env1.scope_mods
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env1 ->
    fun lid ->
      fun open_kind1 ->
        FStar_List.existsb
          (fun uu___ ->
             match uu___ with
             | Open_module_or_namespace (ns, k) ->
                 (k = open_kind1) && (FStar_Ident.lid_equals lid ns)
             | uu___1 -> false) env1.scope_mods
let (namespace_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 -> fun lid -> is_open env1 lid Open_namespace
let (module_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid -> (lid_is_curmod env1 lid) || (is_open env1 lid Open_module)
let (shorten_module_path :
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  =
  fun env1 ->
    fun ids ->
      fun is_full_path ->
        let rec aux revns id =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id in
          if namespace_is_open env1 lid
          then
            FStar_Pervasives_Native.Some ((FStar_List.rev (id :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu___1 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu___1
                   (FStar_Util.map_option
                      (fun uu___2 ->
                         match uu___2 with
                         | (stripped_ids, rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let do_shorten env2 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu___ = aux ns_rev_prefix ns_last_id in
              (match uu___ with
               | FStar_Pervasives_Native.None -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids))) in
        if is_full_path && ((FStar_List.length ids) > Prims.int_zero)
        then
          let uu___ =
            let uu___1 = FStar_Ident.lid_of_ids ids in
            resolve_module_name env1 uu___1 true in
          match uu___ with
          | FStar_Pervasives_Native.Some m when module_is_open env1 m ->
              (ids, [])
          | uu___1 -> do_shorten env1 ids
        else do_shorten env1 ids
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
  fun env1 ->
    fun lid ->
      fun eikind ->
        fun k_local_binding ->
          fun k_rec_binding ->
            fun k_record ->
              fun f_module ->
                fun l_default ->
                  let uu___ = FStar_Ident.ns_of_lid lid in
                  match uu___ with
                  | uu___1::uu___2 ->
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 = FStar_Ident.ns_of_lid lid in
                            FStar_Ident.lid_of_ids uu___6 in
                          let uu___6 = FStar_Ident.range_of_lid lid in
                          FStar_Ident.set_lid_range uu___5 uu___6 in
                        resolve_module_name env1 uu___4 true in
                      (match uu___3 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu___4 =
                             let uu___5 = FStar_Ident.ident_of_lid lid in
                             find_in_module_with_includes eikind f_module
                               Cont_fail env1 modul uu___5 in
                           option_of_cont
                             (fun uu___5 -> FStar_Pervasives_Native.None)
                             uu___4)
                  | [] ->
                      let uu___1 = FStar_Ident.ident_of_lid lid in
                      try_lookup_id'' env1 uu___1 eikind k_local_binding
                        k_rec_binding k_record f_module l_default
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.Some v -> Cont_ok v
      | FStar_Pervasives_Native.None -> k_none
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
  fun env1 ->
    fun lid ->
      fun k_local_binding ->
        fun k_rec_binding ->
          fun k_global_def ->
            let k_global_def' k lid1 def =
              let uu___ = k_global_def lid1 def in cont_of_option k uu___ in
            let f_module lid' =
              let k = Cont_ignore in
              find_in_module env1 lid' (k_global_def' k) k in
            let l_default k i = lookup_default_id env1 i (k_global_def' k) k in
            resolve_in_open_namespaces'' env1 lid Exported_id_term_type
              (fun l ->
                 let uu___ = k_local_binding l in
                 cont_of_option Cont_fail uu___)
              (fun r ->
                 let uu___ = k_rec_binding r in
                 cont_of_option Cont_fail uu___) (fun uu___ -> Cont_ignore)
              f_module l_default
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu___, uu___1, uu___2, l, uu___3, uu___4) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___5 ->
               match uu___5 with
               | FStar_Syntax_Syntax.RecordConstructor (uu___6, fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu___6 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu___, uu___1, uu___2) ->
        FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs ->
    fun lid ->
      let uu___ =
        FStar_Util.find_map lbs
          (fun lb ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu___1 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu___1
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu___ FStar_Util.must
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    fun ns ->
      (let uu___ =
         let uu___1 = FStar_Ident.ns_of_lid lid in FStar_List.length uu___1 in
       let uu___1 =
         let uu___2 = FStar_Ident.ids_of_lid ns in FStar_List.length uu___2 in
       uu___ = uu___1) &&
        (let uu___ =
           let uu___1 = FStar_Ident.ns_of_lid lid in
           FStar_Ident.lid_of_ids uu___1 in
         FStar_Ident.lid_equals uu___ ns)
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid ->
    fun quals ->
      let dd =
        let uu___ =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___1 ->
                     match uu___1 with
                     | FStar_Syntax_Syntax.Projector uu___2 -> true
                     | FStar_Syntax_Syntax.Discriminator uu___2 -> true
                     | uu___2 -> false))) in
        if uu___
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant in
      let uu___ =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___1 ->
                 match uu___1 with
                 | FStar_Syntax_Syntax.Assumption -> true
                 | uu___2 -> false)))
          &&
          (let uu___1 =
             FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___2 ->
                     match uu___2 with
                     | FStar_Syntax_Syntax.New -> true
                     | uu___3 -> false)) in
           Prims.op_Negation uu___1) in
      if uu___ then FStar_Syntax_Syntax.Delta_abstract dd else dd
let (try_lookup_name :
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option)
  =
  fun any_val ->
    fun exclude_interf ->
      fun env1 ->
        fun lid ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___ =
            match uu___ with
            | (uu___1, true) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se, uu___1) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu___2 ->
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         (uu___5, (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu___4 in
                     FStar_Pervasives_Native.Some uu___3
                 | FStar_Syntax_Syntax.Sig_datacon uu___2 ->
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu___6 in
                         (uu___5, (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu___4 in
                     FStar_Pervasives_Native.Some uu___3
                 | FStar_Syntax_Syntax.Sig_let ((uu___2, lbs), uu___3) ->
                     let fv = lb_fv lbs source_lid in
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu___6, (se.FStar_Syntax_Syntax.sigattrs)) in
                       Term_name uu___5 in
                     FStar_Pervasives_Native.Some uu___4
                 | FStar_Syntax_Syntax.Sig_declare_typ (lid1, uu___2, uu___3)
                     ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu___4 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___5 ->
                                  match uu___5 with
                                  | FStar_Syntax_Syntax.Assumption -> true
                                  | uu___6 -> false))) in
                     if uu___4
                     then
                       let lid2 =
                         let uu___5 = FStar_Ident.range_of_lid source_lid in
                         FStar_Ident.set_lid_range lid1 uu___5 in
                       let dd = delta_depth_of_declaration lid2 quals in
                       let uu___5 =
                         FStar_Util.find_map quals
                           (fun uu___6 ->
                              match uu___6 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu___7 -> FStar_Pervasives_Native.None) in
                       (match uu___5 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name
                                 (refl_const,
                                   (se.FStar_Syntax_Syntax.sigattrs)))
                        | uu___6 ->
                            let uu___7 =
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu___10 in
                                (uu___9, (se.FStar_Syntax_Syntax.sigattrs)) in
                              Term_name uu___8 in
                            FStar_Pervasives_Native.Some uu___7)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 = FStar_Ident.range_of_lid source_lid in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu___5 in
                         (se, uu___4) in
                       Eff_name uu___3 in
                     FStar_Pervasives_Native.Some uu___2
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu___2 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                Prims.int_one) FStar_Pervasives_Native.None in
                         (uu___4, []) in
                       Term_name uu___3 in
                     FStar_Pervasives_Native.Some uu___2
                 | uu___2 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let t =
              let uu___ = FStar_Ident.range_of_lid lid in
              found_local_binding uu___ r in
            FStar_Pervasives_Native.Some (Term_name (t, [])) in
          let k_rec_binding uu___ =
            match uu___ with
            | (id, l, dd, used_marker1) ->
                (FStar_ST.op_Colon_Equals used_marker1 true;
                 (let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = FStar_Ident.range_of_lid lid in
                          FStar_Ident.set_lid_range l uu___6 in
                        FStar_Syntax_Syntax.fvar uu___5 dd
                          FStar_Pervasives_Native.None in
                      (uu___4, []) in
                    Term_name uu___3 in
                  FStar_Pervasives_Native.Some uu___2)) in
          let found_unmangled =
            let uu___ = FStar_Ident.ns_of_lid lid in
            match uu___ with
            | [] ->
                let uu___1 =
                  let uu___2 = FStar_Ident.ident_of_lid lid in
                  unmangleOpName uu___2 in
                (match uu___1 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu___2 -> FStar_Pervasives_Native.None)
            | uu___1 -> FStar_Pervasives_Native.None in
          match found_unmangled with
          | FStar_Pervasives_Native.None ->
              resolve_in_open_namespaces' env1 lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
let (try_lookup_effect_name' :
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)
          FStar_Pervasives_Native.option)
  =
  fun exclude_interf ->
    fun env1 ->
      fun lid ->
        let uu___ = try_lookup_name true exclude_interf env1 lid in
        match uu___ with
        | FStar_Pervasives_Native.Some (Eff_name (o, l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu___1 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu___ with
      | FStar_Pervasives_Native.Some (o, l1) ->
          FStar_Pervasives_Native.Some l1
      | uu___1 -> FStar_Pervasives_Native.None
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu___ with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu___1;
             FStar_Syntax_Syntax.sigquals = uu___2;
             FStar_Syntax_Syntax.sigmeta = uu___3;
             FStar_Syntax_Syntax.sigattrs = uu___4;
             FStar_Syntax_Syntax.sigopts = uu___5;_},
           l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu___1, uu___2, uu___3, uu___4, cattributes);
             FStar_Syntax_Syntax.sigrng = uu___5;
             FStar_Syntax_Syntax.sigquals = uu___6;
             FStar_Syntax_Syntax.sigmeta = uu___7;
             FStar_Syntax_Syntax.sigattrs = uu___8;
             FStar_Syntax_Syntax.sigopts = uu___9;_},
           l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu___1 -> FStar_Pervasives_Native.None
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu___ with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu___1;
             FStar_Syntax_Syntax.sigquals = uu___2;
             FStar_Syntax_Syntax.sigmeta = uu___3;
             FStar_Syntax_Syntax.sigattrs = uu___4;
             FStar_Syntax_Syntax.sigopts = uu___5;_},
           uu___6)
          -> FStar_Pervasives_Native.Some ne
      | uu___1 -> FStar_Pervasives_Native.None
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu___ = try_lookup_effect_name env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu___1 -> true
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu___ with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l', uu___1, uu___2, uu___3, uu___4);
             FStar_Syntax_Syntax.sigrng = uu___5;
             FStar_Syntax_Syntax.sigquals = uu___6;
             FStar_Syntax_Syntax.sigmeta = uu___7;
             FStar_Syntax_Syntax.sigattrs = uu___8;
             FStar_Syntax_Syntax.sigopts = uu___9;_},
           uu___10)
          ->
          let rec aux new_name =
            let uu___11 =
              let uu___12 = FStar_Ident.string_of_lid new_name in
              FStar_Util.smap_try_find (sigmap env1) uu___12 in
            match uu___11 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s, uu___12) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu___13 =
                       let uu___14 = FStar_Ident.range_of_lid l in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu___14 in
                     FStar_Pervasives_Native.Some uu___13
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu___13, uu___14, uu___15, cmp, uu___16) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu___13 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu___1, l') ->
          FStar_Pervasives_Native.Some l'
      | uu___1 -> FStar_Pervasives_Native.None
let (lookup_letbinding_quals_and_attrs :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.qualifier Prims.list *
        FStar_Syntax_Syntax.attribute Prims.list))
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___ =
        match uu___ with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu___1, uu___2, uu___3);
             FStar_Syntax_Syntax.sigrng = uu___4;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu___5;
             FStar_Syntax_Syntax.sigattrs = attrs;
             FStar_Syntax_Syntax.sigopts = uu___6;_},
           uu___7) -> FStar_Pervasives_Native.Some (quals, attrs)
        | uu___1 -> FStar_Pervasives_Native.None in
      let uu___ =
        resolve_in_open_namespaces' env1 lid
          (fun uu___1 -> FStar_Pervasives_Native.None)
          (fun uu___1 -> FStar_Pervasives_Native.None) k_global_def in
      match uu___ with
      | FStar_Pervasives_Native.Some qa -> qa
      | uu___1 -> ([], [])
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun path ->
      let uu___ =
        FStar_List.tryFind
          (fun uu___1 ->
             match uu___1 with
             | (mlid, modul) ->
                 let uu___2 = FStar_Ident.path_of_lid mlid in uu___2 = path)
          env1.modules in
      match uu___ with
      | FStar_Pervasives_Native.Some (uu___1, modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___ =
        match uu___ with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu___1, lbs), uu___2);
             FStar_Syntax_Syntax.sigrng = uu___3;
             FStar_Syntax_Syntax.sigquals = uu___4;
             FStar_Syntax_Syntax.sigmeta = uu___5;
             FStar_Syntax_Syntax.sigattrs = uu___6;
             FStar_Syntax_Syntax.sigopts = uu___7;_},
           uu___8) ->
            let fv = lb_fv lbs lid1 in
            let uu___9 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu___9
        | uu___1 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu___ -> FStar_Pervasives_Native.None)
        (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___ =
        match uu___ with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs, uu___1);
             FStar_Syntax_Syntax.sigrng = uu___2;
             FStar_Syntax_Syntax.sigquals = uu___3;
             FStar_Syntax_Syntax.sigmeta = uu___4;
             FStar_Syntax_Syntax.sigattrs = uu___5;
             FStar_Syntax_Syntax.sigopts = uu___6;_},
           uu___7) ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Pervasives.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu___8 -> FStar_Pervasives_Native.None)
        | uu___1 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu___ -> FStar_Pervasives_Native.None)
        (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
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
  fun any_val ->
    fun exclude_interface ->
      fun env1 ->
        fun lid ->
          let uu___ = try_lookup_name any_val exclude_interface env1 lid in
          match uu___ with
          | FStar_Pervasives_Native.Some (Term_name (e, attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu___1 -> FStar_Pervasives_Native.None
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x ->
    match x with
    | FStar_Pervasives_Native.Some (t, uu___) ->
        FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (try_lookup_lid_with_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  = fun env1 -> fun l -> try_lookup_lid' env1.iface false env1 l
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ = try_lookup_lid_with_attributes env1 l in
      FStar_All.pipe_right uu___ drop_attributes
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ = try_lookup_lid env1 l in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Subst.compress e in
            uu___2.FStar_Syntax_Syntax.n in
          (match uu___1 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu___2 -> FStar_Pervasives_Native.None)
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1 ->
    fun lid ->
      let uu___ =
        let uu___1 = FStar_Ident.ns_of_lid lid in
        shorten_module_path env1 uu___1 true in
      match uu___ with
      | (uu___1, short) ->
          let uu___2 = FStar_Ident.ident_of_lid lid in
          FStar_Ident.lid_of_ns_and_id short uu___2
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env1 ->
    fun lid ->
      match env1.curmodule with
      | FStar_Pervasives_Native.None -> shorten_lid' env1 lid
      | uu___ ->
          let lid_without_ns =
            let uu___1 = FStar_Ident.ident_of_lid lid in
            FStar_Ident.lid_of_ns_and_id [] uu___1 in
          let uu___1 = resolve_to_fully_qualified_name env1 lid_without_ns in
          (match uu___1 with
           | FStar_Pervasives_Native.Some lid' when
               let uu___2 = FStar_Ident.string_of_lid lid' in
               let uu___3 = FStar_Ident.string_of_lid lid in uu___2 = uu___3
               -> lid_without_ns
           | uu___2 -> shorten_lid' env1 lid)
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let env' =
        let uu___ = env1 in
        {
          curmodule = (uu___.curmodule);
          curmonad = (uu___.curmonad);
          modules = (uu___.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___.sigaccum);
          sigmap = (uu___.sigmap);
          iface = (uu___.iface);
          admitted_iface = (uu___.admitted_iface);
          expect_typ = (uu___.expect_typ);
          remaining_iface_decls = (uu___.remaining_iface_decls);
          syntax_only = (uu___.syntax_only);
          ds_hooks = (uu___.ds_hooks);
          dep_graph = (uu___.dep_graph)
        } in
      try_lookup_lid_with_attributes env' l
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ = try_lookup_lid_with_attributes_no_resolve env1 l in
      FStar_All.pipe_right uu___ drop_attributes
let (try_lookup_datacon :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 se =
        match se with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu___, uu___1, uu___2);
             FStar_Syntax_Syntax.sigrng = uu___3;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu___4;
             FStar_Syntax_Syntax.sigattrs = uu___5;
             FStar_Syntax_Syntax.sigopts = uu___6;_},
           uu___7) ->
            let uu___8 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___9 ->
                      match uu___9 with
                      | FStar_Syntax_Syntax.Assumption -> true
                      | uu___10 -> false)) in
            if uu___8
            then
              let uu___9 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu___9
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_splice uu___;
             FStar_Syntax_Syntax.sigrng = uu___1;
             FStar_Syntax_Syntax.sigquals = uu___2;
             FStar_Syntax_Syntax.sigmeta = uu___3;
             FStar_Syntax_Syntax.sigattrs = uu___4;
             FStar_Syntax_Syntax.sigopts = uu___5;_},
           uu___6) ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se) in
            let uu___7 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1 in
            FStar_Pervasives_Native.Some uu___7
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu___;
             FStar_Syntax_Syntax.sigrng = uu___1;
             FStar_Syntax_Syntax.sigquals = uu___2;
             FStar_Syntax_Syntax.sigmeta = uu___3;
             FStar_Syntax_Syntax.sigattrs = uu___4;
             FStar_Syntax_Syntax.sigopts = uu___5;_},
           uu___6) ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se) in
            let uu___7 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1 in
            FStar_Pervasives_Native.Some uu___7
        | uu___ -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu___ -> FStar_Pervasives_Native.None)
        (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___ =
        match uu___ with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu___1, uu___2, uu___3, uu___4, datas, uu___5);
             FStar_Syntax_Syntax.sigrng = uu___6;
             FStar_Syntax_Syntax.sigquals = uu___7;
             FStar_Syntax_Syntax.sigmeta = uu___8;
             FStar_Syntax_Syntax.sigattrs = uu___9;
             FStar_Syntax_Syntax.sigopts = uu___10;_},
           uu___11) -> FStar_Pervasives_Native.Some datas
        | uu___1 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu___ -> FStar_Pervasives_Native.None)
        (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = FStar_ST.op_Bang record_cache in FStar_List.hd uu___3 in
      let uu___3 = FStar_ST.op_Bang record_cache in uu___2 :: uu___3 in
    FStar_ST.op_Colon_Equals record_cache uu___1 in
  let pop uu___ =
    let uu___1 =
      let uu___2 = FStar_ST.op_Bang record_cache in FStar_List.tl uu___2 in
    FStar_ST.op_Colon_Equals record_cache uu___1 in
  let snapshot uu___ = FStar_Common.snapshot push record_cache () in
  let rollback depth = FStar_Common.rollback pop record_cache depth in
  let peek uu___ =
    let uu___1 = FStar_ST.op_Bang record_cache in FStar_List.hd uu___1 in
  let insert r =
    let uu___ =
      let uu___1 = let uu___2 = peek () in r :: uu___2 in
      let uu___2 =
        let uu___3 = FStar_ST.op_Bang record_cache in FStar_List.tl uu___3 in
      uu___1 :: uu___2 in
    FStar_ST.op_Colon_Equals record_cache uu___ in
  let filter uu___ =
    let rc = peek () in
    let filtered =
      FStar_List.filter (fun r -> Prims.op_Negation r.is_private) rc in
    let uu___1 =
      let uu___2 =
        let uu___3 = FStar_ST.op_Bang record_cache in FStar_List.tl uu___3 in
      filtered :: uu___2 in
    FStar_ST.op_Colon_Equals record_cache uu___1 in
  let aux = ((push, pop), ((snapshot, rollback), (peek, insert))) in
  (aux, filter)
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
  fun e ->
    fun new_globs ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs, uu___) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___1 ->
                   match uu___1 with
                   | FStar_Syntax_Syntax.RecordType uu___2 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu___2 -> true
                   | uu___2 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___1 ->
                      match uu___1 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid, uu___2, uu___3, uu___4, uu___5, uu___6);
                          FStar_Syntax_Syntax.sigrng = uu___7;
                          FStar_Syntax_Syntax.sigquals = uu___8;
                          FStar_Syntax_Syntax.sigmeta = uu___9;
                          FStar_Syntax_Syntax.sigattrs = uu___10;
                          FStar_Syntax_Syntax.sigopts = uu___11;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu___2 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___1 ->
                    match uu___1 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename, univs, parms, uu___2, uu___3, dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu___4;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu___5;
                        FStar_Syntax_Syntax.sigattrs = uu___6;
                        FStar_Syntax_Syntax.sigopts = uu___7;_} ->
                        let uu___8 =
                          let uu___9 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu___9 in
                        (match uu___8 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname, uu___9, t, uu___10, n, uu___11);
                             FStar_Syntax_Syntax.sigrng = uu___12;
                             FStar_Syntax_Syntax.sigquals = uu___13;
                             FStar_Syntax_Syntax.sigmeta = uu___14;
                             FStar_Syntax_Syntax.sigattrs = uu___15;
                             FStar_Syntax_Syntax.sigopts = uu___16;_} ->
                             let uu___17 = FStar_Syntax_Util.arrow_formals t in
                             (match uu___17 with
                              | (all_formals, uu___18) ->
                                  let uu___19 =
                                    FStar_Util.first_N n all_formals in
                                  (match uu___19 with
                                   | (_params, formals) ->
                                       let is_rec = is_record typename_quals in
                                       let formals' =
                                         FStar_All.pipe_right formals
                                           (FStar_List.collect
                                              (fun f ->
                                                 let uu___20 =
                                                   (FStar_Syntax_Syntax.is_null_bv
                                                      f.FStar_Syntax_Syntax.binder_bv)
                                                     ||
                                                     (is_rec &&
                                                        (FStar_Syntax_Syntax.is_implicit
                                                           f.FStar_Syntax_Syntax.binder_qual)) in
                                                 if uu___20 then [] else [f])) in
                                       let fields' =
                                         FStar_All.pipe_right formals'
                                           (FStar_List.map
                                              (fun f ->
                                                 (((f.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.ppname),
                                                   ((f.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort)))) in
                                       let fields = fields' in
                                       let record =
                                         let uu___20 =
                                           FStar_Ident.ident_of_lid
                                             constrname in
                                         {
                                           typename;
                                           constrname = uu___20;
                                           parms;
                                           fields;
                                           is_private =
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Private
                                                typename_quals);
                                           is_record = is_rec
                                         } in
                                       ((let uu___21 =
                                           let uu___22 =
                                             FStar_ST.op_Bang new_globs in
                                           (Record_or_dc record) :: uu___22 in
                                         FStar_ST.op_Colon_Equals new_globs
                                           uu___21);
                                        (match () with
                                         | () ->
                                             ((let add_field uu___22 =
                                                 match uu___22 with
                                                 | (id, uu___23) ->
                                                     let modul =
                                                       let uu___24 =
                                                         let uu___25 =
                                                           FStar_Ident.ns_of_lid
                                                             constrname in
                                                         FStar_Ident.lid_of_ids
                                                           uu___25 in
                                                       FStar_Ident.string_of_lid
                                                         uu___24 in
                                                     let uu___24 =
                                                       get_exported_id_set e
                                                         modul in
                                                     (match uu___24 with
                                                      | FStar_Pervasives_Native.Some
                                                          my_ex ->
                                                          let my_exported_ids
                                                            =
                                                            my_ex
                                                              Exported_id_field in
                                                          ((let uu___26 =
                                                              let uu___27 =
                                                                FStar_Ident.string_of_id
                                                                  id in
                                                              let uu___28 =
                                                                FStar_ST.op_Bang
                                                                  my_exported_ids in
                                                              FStar_Util.set_add
                                                                uu___27
                                                                uu___28 in
                                                            FStar_ST.op_Colon_Equals
                                                              my_exported_ids
                                                              uu___26);
                                                           (match () with
                                                            | () ->
                                                                let projname
                                                                  =
                                                                  let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                    constrname
                                                                    id in
                                                                    FStar_All.pipe_right
                                                                    uu___27
                                                                    FStar_Ident.ident_of_lid in
                                                                  FStar_All.pipe_right
                                                                    uu___26
                                                                    FStar_Ident.string_of_id in
                                                                let uu___27 =
                                                                  let uu___28
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    my_exported_ids in
                                                                  FStar_Util.set_add
                                                                    projname
                                                                    uu___28 in
                                                                FStar_ST.op_Colon_Equals
                                                                  my_exported_ids
                                                                  uu___27))
                                                      | FStar_Pervasives_Native.None
                                                          -> ()) in
                                               FStar_List.iter add_field
                                                 fields');
                                              (match () with
                                               | () ->
                                                   insert_record_cache record))))))
                         | uu___9 -> ())
                    | uu___2 -> ()))
        | uu___ -> ()
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env1 ->
    fun fieldname ->
      let find_in_cache fieldname1 =
        let uu___ =
          let uu___1 = FStar_Ident.ns_of_lid fieldname1 in
          let uu___2 = FStar_Ident.ident_of_lid fieldname1 in
          (uu___1, uu___2) in
        match uu___ with
        | (ns, id) ->
            let uu___1 = peek_record_cache () in
            FStar_Util.find_map uu___1
              (fun record ->
                 let uu___2 =
                   find_in_record ns id record (fun r -> Cont_ok r) in
                 option_of_cont (fun uu___3 -> FStar_Pervasives_Native.None)
                   uu___2) in
      resolve_in_open_namespaces'' env1 fieldname Exported_id_field
        (fun uu___ -> Cont_ignore) (fun uu___ -> Cont_ignore)
        (fun r -> Cont_ok r)
        (fun fn ->
           let uu___ = find_in_cache fn in cont_of_option Cont_ignore uu___)
        (fun k -> fun uu___ -> k)
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env1 ->
    fun fieldname ->
      let uu___ = try_lookup_record_or_dc_by_field_name env1 fieldname in
      match uu___ with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu___1 -> FStar_Pervasives_Native.None
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env1 ->
    fun lid ->
      fun record ->
        let uu___ = try_lookup_record_by_field_name env1 lid in
        match uu___ with
        | FStar_Pervasives_Native.Some record' when
            let uu___1 = FStar_Ident.nsstr record.typename in
            let uu___2 = FStar_Ident.nsstr record'.typename in
            uu___1 = uu___2 ->
            let uu___1 =
              let uu___2 = FStar_Ident.ns_of_lid record.typename in
              let uu___3 = FStar_Ident.ident_of_lid lid in
              find_in_record uu___2 uu___3 record (fun uu___4 -> Cont_ok ()) in
            (match uu___1 with | Cont_ok uu___2 -> true | uu___2 -> false)
        | uu___1 -> false
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun fieldname ->
      let uu___ = try_lookup_record_or_dc_by_field_name env1 fieldname in
      match uu___ with
      | FStar_Pervasives_Native.Some r ->
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStar_Ident.ns_of_lid r.typename in
                  FStar_List.append uu___5 [r.constrname] in
                FStar_Ident.lid_of_ids uu___4 in
              let uu___4 = FStar_Ident.range_of_lid fieldname in
              FStar_Ident.set_lid_range uu___3 uu___4 in
            (uu___2, (r.is_record)) in
          FStar_Pervasives_Native.Some uu___1
      | uu___1 -> FStar_Pervasives_Native.None
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu___ ->
    let uu___1 = FStar_Util.new_set FStar_Util.compare in
    FStar_Util.mk_ref uu___1
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu___ ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___1 ->
      match uu___1 with
      | Exported_id_term_type -> term_type_set
      | Exported_id_field -> field_set
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val ->
    fun exclude_interface ->
      fun env1 ->
        fun lid ->
          let filter_scope_mods uu___ =
            match uu___ with | Rec_binding uu___1 -> true | uu___1 -> false in
          let this_env =
            let uu___ = env1 in
            let uu___1 = FStar_List.filter filter_scope_mods env1.scope_mods in
            {
              curmodule = (uu___.curmodule);
              curmonad = (uu___.curmonad);
              modules = (uu___.modules);
              scope_mods = uu___1;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___.sigaccum);
              sigmap = (uu___.sigmap);
              iface = (uu___.iface);
              admitted_iface = (uu___.admitted_iface);
              expect_typ = (uu___.expect_typ);
              remaining_iface_decls = (uu___.remaining_iface_decls);
              syntax_only = (uu___.syntax_only);
              ds_hooks = (uu___.ds_hooks);
              dep_graph = (uu___.dep_graph)
            } in
          let uu___ = try_lookup_lid' any_val exclude_interface this_env lid in
          match uu___ with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some uu___1 -> false
let (push_scope_mod : env -> scope_mod -> env) =
  fun env1 ->
    fun scope_mod1 ->
      let uu___ = env1 in
      {
        curmodule = (uu___.curmodule);
        curmonad = (uu___.curmonad);
        modules = (uu___.modules);
        scope_mods = (scope_mod1 :: (env1.scope_mods));
        exported_ids = (uu___.exported_ids);
        trans_exported_ids = (uu___.trans_exported_ids);
        includes = (uu___.includes);
        sigaccum = (uu___.sigaccum);
        sigmap = (uu___.sigmap);
        iface = (uu___.iface);
        admitted_iface = (uu___.admitted_iface);
        expect_typ = (uu___.expect_typ);
        remaining_iface_decls = (uu___.remaining_iface_decls);
        syntax_only = (uu___.syntax_only);
        ds_hooks = (uu___.ds_hooks);
        dep_graph = (uu___.dep_graph)
      }
let (push_bv' :
  env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv * used_marker)) =
  fun env1 ->
    fun x ->
      let r = FStar_Ident.range_of_id x in
      let bv =
        let uu___ = FStar_Ident.string_of_id x in
        FStar_Syntax_Syntax.gen_bv uu___ (FStar_Pervasives_Native.Some r)
          (let uu___1 = FStar_Syntax_Syntax.tun in
           {
             FStar_Syntax_Syntax.n = (uu___1.FStar_Syntax_Syntax.n);
             FStar_Syntax_Syntax.pos = r;
             FStar_Syntax_Syntax.vars = (uu___1.FStar_Syntax_Syntax.vars)
           }) in
      let used_marker1 = FStar_Util.mk_ref false in
      ((push_scope_mod env1 (Local_binding (x, bv, used_marker1))), bv,
        used_marker1)
let (push_bv : env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv)) =
  fun env1 ->
    fun x ->
      let uu___ = push_bv' env1 x in
      match uu___ with | (env2, bv, uu___1) -> (env2, bv)
let (push_top_level_rec_binding :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.delta_depth -> (env * Prims.bool FStar_ST.ref))
  =
  fun env0 ->
    fun x ->
      fun dd ->
        let l = qualify env0 x in
        let uu___ =
          (unique false true env0 l) || (FStar_Options.interactive ()) in
        if uu___
        then
          let used_marker1 = FStar_Util.mk_ref false in
          ((push_scope_mod env0 (Rec_binding (x, l, dd, used_marker1))),
            used_marker1)
        else
          (let uu___2 =
             let uu___3 =
               let uu___4 = FStar_Ident.string_of_lid l in
               Prims.op_Hat "Duplicate top-level names " uu___4 in
             (FStar_Errors.Fatal_DuplicateTopLevelNames, uu___3) in
           let uu___3 = FStar_Ident.range_of_lid l in
           FStar_Errors.raise_error uu___2 uu___3)
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup ->
    fun env1 ->
      fun s ->
        let err l =
          let sopt =
            let uu___ = FStar_Ident.string_of_lid l in
            FStar_Util.smap_try_find (sigmap env1) uu___ in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se, uu___) ->
                let uu___1 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se) in
                (match uu___1 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu___2 = FStar_Ident.range_of_lid l1 in
                     FStar_All.pipe_left FStar_Range.string_of_range uu___2
                 | FStar_Pervasives_Native.None -> "<unknown>")
            | FStar_Pervasives_Native.None -> "<unknown>" in
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Ident.string_of_lid l in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu___2 r in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu___1) in
          let uu___1 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu___ uu___1 in
        let globals = FStar_Util.mk_ref env1.scope_mods in
        let env2 =
          let uu___ =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu___1 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu___1 -> (false, true)
            | uu___1 -> (false, false) in
          match uu___ with
          | (any_val, exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s in
              let uu___1 =
                FStar_Util.find_map lids
                  (fun l ->
                     let uu___2 =
                       let uu___3 = unique any_val exclude_interface env1 l in
                       Prims.op_Negation uu___3 in
                     if uu___2
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None) in
              (match uu___1 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu___2 ->
                   (extract_record env1 globals s;
                    (let uu___4 = env1 in
                     {
                       curmodule = (uu___4.curmodule);
                       curmonad = (uu___4.curmonad);
                       modules = (uu___4.modules);
                       scope_mods = (uu___4.scope_mods);
                       exported_ids = (uu___4.exported_ids);
                       trans_exported_ids = (uu___4.trans_exported_ids);
                       includes = (uu___4.includes);
                       sigaccum = (s :: (env1.sigaccum));
                       sigmap = (uu___4.sigmap);
                       iface = (uu___4.iface);
                       admitted_iface = (uu___4.admitted_iface);
                       expect_typ = (uu___4.expect_typ);
                       remaining_iface_decls = (uu___4.remaining_iface_decls);
                       syntax_only = (uu___4.syntax_only);
                       ds_hooks = (uu___4.ds_hooks);
                       dep_graph = (uu___4.dep_graph)
                     }))) in
        let env3 =
          let uu___ = env2 in
          let uu___1 = FStar_ST.op_Bang globals in
          {
            curmodule = (uu___.curmodule);
            curmonad = (uu___.curmonad);
            modules = (uu___.modules);
            scope_mods = uu___1;
            exported_ids = (uu___.exported_ids);
            trans_exported_ids = (uu___.trans_exported_ids);
            includes = (uu___.includes);
            sigaccum = (uu___.sigaccum);
            sigmap = (uu___.sigmap);
            iface = (uu___.iface);
            admitted_iface = (uu___.admitted_iface);
            expect_typ = (uu___.expect_typ);
            remaining_iface_decls = (uu___.remaining_iface_decls);
            syntax_only = (uu___.syntax_only);
            ds_hooks = (uu___.ds_hooks);
            dep_graph = (uu___.dep_graph)
          } in
        let uu___ =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses, uu___1) ->
              let uu___2 =
                FStar_List.map
                  (fun se -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
              (env3, uu___2)
          | uu___1 -> (env3, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
        match uu___ with
        | (env4, lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu___2 ->
                     match uu___2 with
                     | (lids, se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid ->
                                 (let uu___4 =
                                    let uu___5 =
                                      let uu___6 =
                                        FStar_Ident.ident_of_lid lid in
                                      Top_level_def uu___6 in
                                    let uu___6 = FStar_ST.op_Bang globals in
                                    uu___5 :: uu___6 in
                                  FStar_ST.op_Colon_Equals globals uu___4);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu___4 =
                                          let uu___5 =
                                            FStar_Ident.ns_of_lid lid in
                                          FStar_Ident.lid_of_ids uu___5 in
                                        FStar_Ident.string_of_lid uu___4 in
                                      ((let uu___5 =
                                          get_exported_id_set env4 modul in
                                        match uu___5 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type in
                                            let uu___6 =
                                              let uu___7 =
                                                let uu___8 =
                                                  FStar_Ident.ident_of_lid
                                                    lid in
                                                FStar_Ident.string_of_id
                                                  uu___8 in
                                              let uu___8 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids in
                                              FStar_Util.set_add uu___7
                                                uu___8 in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu___6
                                        | FStar_Pervasives_Native.None -> ());
                                       (match () with
                                        | () ->
                                            let is_iface =
                                              env4.iface &&
                                                (Prims.op_Negation
                                                   env4.admitted_iface) in
                                            let uu___5 =
                                              FStar_Ident.string_of_lid lid in
                                            FStar_Util.smap_add (sigmap env4)
                                              uu___5
                                              (se,
                                                (env4.iface &&
                                                   (Prims.op_Negation
                                                      env4.admitted_iface))))))))));
             (let env5 =
                let uu___2 = env4 in
                let uu___3 = FStar_ST.op_Bang globals in
                {
                  curmodule = (uu___2.curmodule);
                  curmonad = (uu___2.curmonad);
                  modules = (uu___2.modules);
                  scope_mods = uu___3;
                  exported_ids = (uu___2.exported_ids);
                  trans_exported_ids = (uu___2.trans_exported_ids);
                  includes = (uu___2.includes);
                  sigaccum = (uu___2.sigaccum);
                  sigmap = (uu___2.sigmap);
                  iface = (uu___2.iface);
                  admitted_iface = (uu___2.admitted_iface);
                  expect_typ = (uu___2.expect_typ);
                  remaining_iface_decls = (uu___2.remaining_iface_decls);
                  syntax_only = (uu___2.syntax_only);
                  ds_hooks = (uu___2.ds_hooks);
                  dep_graph = (uu___2.dep_graph)
                } in
              env5))
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1 -> fun se -> push_sigelt' true env1 se
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1 -> fun se -> push_sigelt' false env1 se
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun ns ->
      let uu___ =
        let uu___1 = resolve_module_name env1 ns false in
        match uu___1 with
        | FStar_Pervasives_Native.None ->
            let modules = env1.modules in
            let uu___2 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu___3 ->
                      match uu___3 with
                      | (m, uu___4) ->
                          let uu___5 =
                            let uu___6 = FStar_Ident.string_of_lid m in
                            Prims.op_Hat uu___6 "." in
                          let uu___6 =
                            let uu___7 = FStar_Ident.string_of_lid ns in
                            Prims.op_Hat uu___7 "." in
                          FStar_Util.starts_with uu___5 uu___6)) in
            if uu___2
            then (ns, Open_namespace)
            else
              (let uu___4 =
                 let uu___5 =
                   let uu___6 = FStar_Ident.string_of_lid ns in
                   FStar_Util.format1 "Namespace %s cannot be found" uu___6 in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu___5) in
               let uu___5 = FStar_Ident.range_of_lid ns in
               FStar_Errors.raise_error uu___4 uu___5)
        | FStar_Pervasives_Native.Some ns' -> (ns', Open_module) in
      match uu___ with
      | (ns', kd) ->
          ((env1.ds_hooks).ds_push_open_hook env1 (ns', kd);
           push_scope_mod env1 (Open_module_or_namespace (ns', kd)))
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun ns ->
      let ns0 = ns in
      let uu___ = resolve_module_name env1 ns false in
      match uu___ with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env1.ds_hooks).ds_push_include_hook env1 ns1;
           (let env2 =
              push_scope_mod env1
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu___2 = current_module env2 in
              FStar_Ident.string_of_lid uu___2 in
            (let uu___3 = FStar_Util.smap_try_find env2.includes curmod in
             match uu___3 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu___4 =
                   let uu___5 = FStar_ST.op_Bang incl in ns1 :: uu___5 in
                 FStar_ST.op_Colon_Equals incl uu___4);
            (match () with
             | () ->
                 let uu___3 =
                   let uu___4 = FStar_Ident.string_of_lid ns1 in
                   get_trans_exported_id_set env2 uu___4 in
                 (match uu___3 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu___5 =
                          let uu___6 = get_exported_id_set env2 curmod in
                          let uu___7 = get_trans_exported_id_set env2 curmod in
                          (uu___6, uu___7) in
                        match uu___5 with
                        | (FStar_Pervasives_Native.Some cur_exports,
                           FStar_Pervasives_Native.Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu___6 = ns_trans_exports k in
                                FStar_ST.op_Bang uu___6 in
                              let ex = cur_exports k in
                              (let uu___7 =
                                 let uu___8 = FStar_ST.op_Bang ex in
                                 FStar_Util.set_difference uu___8 ns_ex in
                               FStar_ST.op_Colon_Equals ex uu___7);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu___8 =
                                     let uu___9 = FStar_ST.op_Bang trans_ex in
                                     FStar_Util.set_union uu___9 ns_ex in
                                   FStar_ST.op_Colon_Equals trans_ex uu___8) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu___6 -> ());
                       (match () with | () -> env2))
                  | FStar_Pervasives_Native.None ->
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = FStar_Ident.string_of_lid ns1 in
                          FStar_Util.format1
                            "include: Module %s was not prepared" uu___6 in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared, uu___5) in
                      let uu___5 = FStar_Ident.range_of_lid ns1 in
                      FStar_Errors.raise_error uu___4 uu___5))))
      | uu___1 ->
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Ident.string_of_lid ns in
              FStar_Util.format1 "include: Module %s cannot be found" uu___4 in
            (FStar_Errors.Fatal_ModuleNotFound, uu___3) in
          let uu___3 = FStar_Ident.range_of_lid ns in
          FStar_Errors.raise_error uu___2 uu___3
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env1 ->
    fun x ->
      fun l ->
        let uu___ = module_is_defined env1 l in
        if uu___
        then
          ((env1.ds_hooks).ds_push_module_abbrev_hook env1 x l;
           push_scope_mod env1 (Module_abbrev (x, l)))
        else
          (let uu___2 =
             let uu___3 =
               let uu___4 = FStar_Ident.string_of_lid l in
               FStar_Util.format1 "Module %s cannot be found" uu___4 in
             (FStar_Errors.Fatal_ModuleNotFound, uu___3) in
           let uu___3 = FStar_Ident.range_of_lid l in
           FStar_Errors.raise_error uu___2 uu___3)
let (check_admits :
  env -> FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul) =
  fun env1 ->
    fun m ->
      let admitted_sig_lids =
        FStar_All.pipe_right env1.sigaccum
          (FStar_List.fold_left
             (fun lids ->
                fun se ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) when
                      let uu___ =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
                      Prims.op_Negation uu___ ->
                      let uu___ =
                        let uu___1 = FStar_Ident.string_of_lid l in
                        FStar_Util.smap_try_find (sigmap env1) uu___1 in
                      (match uu___ with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu___1;
                              FStar_Syntax_Syntax.sigrng = uu___2;
                              FStar_Syntax_Syntax.sigquals = uu___3;
                              FStar_Syntax_Syntax.sigmeta = uu___4;
                              FStar_Syntax_Syntax.sigattrs = uu___5;
                              FStar_Syntax_Syntax.sigopts = uu___6;_},
                            uu___7)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ uu___1;
                              FStar_Syntax_Syntax.sigrng = uu___2;
                              FStar_Syntax_Syntax.sigquals = uu___3;
                              FStar_Syntax_Syntax.sigmeta = uu___4;
                              FStar_Syntax_Syntax.sigattrs = uu___5;
                              FStar_Syntax_Syntax.sigopts = uu___6;_},
                            uu___7)
                           -> lids
                       | uu___1 ->
                           ((let uu___3 =
                               let uu___4 = FStar_Options.interactive () in
                               Prims.op_Negation uu___4 in
                             if uu___3
                             then
                               let uu___4 = FStar_Ident.range_of_lid l in
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 = FStar_Ident.string_of_lid l in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu___7 in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu___6) in
                               FStar_Errors.log_issue uu___4 uu___5
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals) in
                             (let uu___4 = FStar_Ident.string_of_lid l in
                              FStar_Util.smap_add (sigmap env1) uu___4
                                ((let uu___5 = se in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (uu___5.FStar_Syntax_Syntax.sigel);
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___5.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals = quals;
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___5.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___5.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___5.FStar_Syntax_Syntax.sigopts)
                                  }), false));
                             l
                             ::
                             lids)))
                  | uu___ -> lids) []) in
      let uu___ = m in
      let uu___1 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu___2, uu___3)
                    when
                    FStar_List.existsb
                      (fun l -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___4 = s in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___4.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___4.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___4.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___4.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___4.FStar_Syntax_Syntax.sigopts)
                    }
                | uu___2 -> s)) in
      {
        FStar_Syntax_Syntax.name = (uu___.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu___1;
        FStar_Syntax_Syntax.is_interface =
          (uu___.FStar_Syntax_Syntax.is_interface)
      }
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env1 ->
    fun modul ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses, uu___1) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun se1 ->
                            match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid, uu___2, uu___3, uu___4, uu___5, uu___6)
                                ->
                                let uu___7 = FStar_Ident.string_of_lid lid in
                                FStar_Util.smap_remove (sigmap env1) uu___7
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid, univ_names, binders, typ, uu___2,
                                 uu___3)
                                ->
                                ((let uu___5 = FStar_Ident.string_of_lid lid in
                                  FStar_Util.smap_remove (sigmap env1) uu___5);
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu___5 =
                                        let uu___6 =
                                          let uu___7 =
                                            let uu___8 =
                                              let uu___9 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  typ in
                                              (binders, uu___9) in
                                            FStar_Syntax_Syntax.Tm_arrow
                                              uu___8 in
                                          let uu___8 =
                                            FStar_Ident.range_of_lid lid in
                                          FStar_Syntax_Syntax.mk uu___7
                                            uu___8 in
                                        (lid, univ_names, uu___6) in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu___5 in
                                    let se2 =
                                      let uu___5 = se1 in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___5.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___5.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___5.FStar_Syntax_Syntax.sigattrs);
                                        FStar_Syntax_Syntax.sigopts =
                                          (uu___5.FStar_Syntax_Syntax.sigopts)
                                      } in
                                    let uu___5 =
                                      FStar_Ident.string_of_lid lid in
                                    FStar_Util.smap_add (sigmap env1) uu___5
                                      (se2, false))
                                 else ())
                            | uu___2 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu___1, uu___2) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    let uu___3 = FStar_Ident.string_of_lid lid in
                    FStar_Util.smap_remove (sigmap env1) uu___3
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu___1, lbs), uu___2) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_All.pipe_right lbs
                      (FStar_List.iter
                         (fun lb ->
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 =
                                    FStar_Util.right
                                      lb.FStar_Syntax_Syntax.lbname in
                                  uu___6.FStar_Syntax_Syntax.fv_name in
                                uu___5.FStar_Syntax_Syntax.v in
                              FStar_Ident.string_of_lid uu___4 in
                            FStar_Util.smap_remove (sigmap env1) uu___3))
                  else ()
              | uu___1 -> ()));
      (let curmod =
         let uu___1 = current_module env1 in FStar_Ident.string_of_lid uu___1 in
       (let uu___2 =
          let uu___3 = get_exported_id_set env1 curmod in
          let uu___4 = get_trans_exported_id_set env1 curmod in
          (uu___3, uu___4) in
        match uu___2 with
        | (FStar_Pervasives_Native.Some cur_ex, FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu___3 = cur_ex eikind in FStar_ST.op_Bang uu___3 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu___3 =
                let uu___4 = FStar_ST.op_Bang cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu___4 in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu___3 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu___3 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___3 = env1 in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___3.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env1.modules));
                    scope_mods = [];
                    exported_ids = (uu___3.exported_ids);
                    trans_exported_ids = (uu___3.trans_exported_ids);
                    includes = (uu___3.includes);
                    sigaccum = [];
                    sigmap = (uu___3.sigmap);
                    iface = (uu___3.iface);
                    admitted_iface = (uu___3.admitted_iface);
                    expect_typ = (uu___3.expect_typ);
                    remaining_iface_decls = (uu___3.remaining_iface_decls);
                    syntax_only = (uu___3.syntax_only);
                    ds_hooks = (uu___3.ds_hooks);
                    dep_graph = (uu___3.dep_graph)
                  }))))
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push : env -> env) =
  fun env1 ->
    FStar_Util.atomically
      (fun uu___ ->
         push_record_cache ();
         (let uu___3 = let uu___4 = FStar_ST.op_Bang stack in env1 :: uu___4 in
          FStar_ST.op_Colon_Equals stack uu___3);
         (let uu___3 = env1 in
          let uu___4 = FStar_Util.smap_copy env1.exported_ids in
          let uu___5 = FStar_Util.smap_copy env1.trans_exported_ids in
          let uu___6 = FStar_Util.smap_copy env1.includes in
          let uu___7 = FStar_Util.smap_copy env1.sigmap in
          {
            curmodule = (uu___3.curmodule);
            curmonad = (uu___3.curmonad);
            modules = (uu___3.modules);
            scope_mods = (uu___3.scope_mods);
            exported_ids = uu___4;
            trans_exported_ids = uu___5;
            includes = uu___6;
            sigaccum = (uu___3.sigaccum);
            sigmap = uu___7;
            iface = (uu___3.iface);
            admitted_iface = (uu___3.admitted_iface);
            expect_typ = (uu___3.expect_typ);
            remaining_iface_decls = (uu___3.remaining_iface_decls);
            syntax_only = (uu___3.syntax_only);
            ds_hooks = (uu___3.ds_hooks);
            dep_graph = (uu___3.dep_graph)
          }))
let (pop : unit -> env) =
  fun uu___ ->
    FStar_Util.atomically
      (fun uu___1 ->
         let uu___2 = FStar_ST.op_Bang stack in
         match uu___2 with
         | env1::tl ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl; env1)
         | uu___3 -> failwith "Impossible: Too many pops")
let (snapshot : env -> (Prims.int * env)) =
  fun env1 -> FStar_Common.snapshot push stack env1
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth -> FStar_Common.rollback pop stack depth
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m ->
    fun env1 ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu___ ->
            let uu___1 = FStar_Ident.nsstr l in
            let uu___2 = FStar_Ident.string_of_lid m in uu___1 = uu___2
        | uu___ -> false in
      let sm = sigmap env1 in
      let env2 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env2 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k ->
              let uu___1 = FStar_Util.smap_try_find sm' k in
              match uu___1 with
              | FStar_Pervasives_Native.Some (se, true) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l, u, t) ->
                          let uu___3 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___3.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___3.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___3.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___3.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___3.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu___3 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu___2 -> ()));
      env2
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env1 ->
    fun modul ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env1 modul
        else modul in
      let uu___ = finish env1 modul1 in (uu___, modul1)
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list ;
  exported_id_fields: Prims.string Prims.list }
let (__proj__Mkexported_ids__item__exported_id_terms :
  exported_ids -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { exported_id_terms; exported_id_fields;_} -> exported_id_terms
let (__proj__Mkexported_ids__item__exported_id_fields :
  exported_ids -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { exported_id_terms; exported_id_fields;_} -> exported_id_fields
let (as_exported_ids : exported_id_set -> exported_ids) =
  fun e ->
    let terms =
      let uu___ =
        let uu___1 = e Exported_id_term_type in FStar_ST.op_Bang uu___1 in
      FStar_Util.set_elements uu___ in
    let fields =
      let uu___ = let uu___1 = e Exported_id_field in FStar_ST.op_Bang uu___1 in
      FStar_Util.set_elements uu___ in
    { exported_id_terms = terms; exported_id_fields = fields }
let (as_exported_id_set :
  exported_ids FStar_Pervasives_Native.option ->
    exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref)
  =
  fun e ->
    match e with
    | FStar_Pervasives_Native.None -> exported_id_set_new ()
    | FStar_Pervasives_Native.Some e1 ->
        let terms =
          let uu___ =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare in
          FStar_Util.mk_ref uu___ in
        let fields =
          let uu___ =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare in
          FStar_Util.mk_ref uu___ in
        (fun uu___ ->
           match uu___ with
           | Exported_id_term_type -> terms
           | Exported_id_field -> fields)
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option }
let (__proj__Mkmodule_inclusion_info__item__mii_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { mii_exported_ids; mii_trans_exported_ids; mii_includes;_} ->
        mii_exported_ids
let (__proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { mii_exported_ids; mii_trans_exported_ids; mii_includes;_} ->
        mii_trans_exported_ids
let (__proj__Mkmodule_inclusion_info__item__mii_includes :
  module_inclusion_info ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee ->
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
  'uuuuu .
    'uuuuu Prims.list FStar_Pervasives_Native.option ->
      'uuuuu Prims.list FStar_ST.ref
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env1 ->
    fun l ->
      let mname = FStar_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu___ = FStar_Util.smap_try_find m mname in
        FStar_Util.map_opt uu___ as_exported_ids in
      let uu___ = as_ids_opt env1.exported_ids in
      let uu___1 = as_ids_opt env1.trans_exported_ids in
      let uu___2 =
        let uu___3 = FStar_Util.smap_try_find env1.includes mname in
        FStar_Util.map_opt uu___3 (fun r -> FStar_ST.op_Bang r) in
      {
        mii_exported_ids = uu___;
        mii_trans_exported_ids = uu___1;
        mii_includes = uu___2
      }
let (prepare_module_or_interface :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident -> module_inclusion_info -> (env * Prims.bool))
  =
  fun intf ->
    fun admitted ->
      fun env1 ->
        fun mname ->
          fun mii ->
            let prep env2 =
              let filename =
                let uu___ = FStar_Ident.string_of_lid mname in
                FStar_Util.strcat uu___ ".fst" in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename in
              let auto_open1 =
                let convert_kind uu___ =
                  match uu___ with
                  | FStar_Parser_Dep.Open_namespace -> Open_namespace
                  | FStar_Parser_Dep.Open_module -> Open_module in
                FStar_List.map
                  (fun uu___ ->
                     match uu___ with
                     | (lid, kind) -> (lid, (convert_kind kind))) auto_open in
              let namespace_of_module =
                let uu___ =
                  let uu___1 =
                    let uu___2 = FStar_Ident.ns_of_lid mname in
                    FStar_List.length uu___2 in
                  uu___1 > Prims.int_zero in
                if uu___
                then
                  let uu___1 =
                    let uu___2 =
                      let uu___3 = FStar_Ident.ns_of_lid mname in
                      FStar_Ident.lid_of_ids uu___3 in
                    (uu___2, Open_namespace) in
                  [uu___1]
                else [] in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1) in
              (let uu___1 = FStar_Ident.string_of_lid mname in
               let uu___2 = as_exported_id_set mii.mii_exported_ids in
               FStar_Util.smap_add env2.exported_ids uu___1 uu___2);
              (match () with
               | () ->
                   ((let uu___2 = FStar_Ident.string_of_lid mname in
                     let uu___3 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStar_Util.smap_add env2.trans_exported_ids uu___2
                       uu___3);
                    (match () with
                     | () ->
                         ((let uu___3 = FStar_Ident.string_of_lid mname in
                           let uu___4 = as_includes mii.mii_includes in
                           FStar_Util.smap_add env2.includes uu___3 uu___4);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___3 = env2 in
                                 let uu___4 =
                                   FStar_List.map
                                     (fun x -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___3.curmonad);
                                   modules = (uu___3.modules);
                                   scope_mods = uu___4;
                                   exported_ids = (uu___3.exported_ids);
                                   trans_exported_ids =
                                     (uu___3.trans_exported_ids);
                                   includes = (uu___3.includes);
                                   sigaccum = (uu___3.sigaccum);
                                   sigmap = (env2.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___3.expect_typ);
                                   remaining_iface_decls =
                                     (uu___3.remaining_iface_decls);
                                   syntax_only = (uu___3.syntax_only);
                                   ds_hooks = (uu___3.ds_hooks);
                                   dep_graph = (uu___3.dep_graph)
                                 } in
                               (FStar_List.iter
                                  (fun op ->
                                     (env2.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env')))))) in
            let uu___ =
              FStar_All.pipe_right env1.modules
                (FStar_Util.find_opt
                   (fun uu___1 ->
                      match uu___1 with
                      | (l, uu___2) -> FStar_Ident.lid_equals l mname)) in
            match uu___ with
            | FStar_Pervasives_Native.None ->
                let uu___1 = prep env1 in (uu___1, false)
            | FStar_Pervasives_Native.Some (uu___1, m) ->
                ((let uu___3 =
                    (let uu___4 = FStar_Options.interactive () in
                     Prims.op_Negation uu___4) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu___3
                  then
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStar_Ident.string_of_lid mname in
                        FStar_Util.format1
                          "Duplicate module or interface name: %s" uu___6 in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface, uu___5) in
                    let uu___5 = FStar_Ident.range_of_lid mname in
                    FStar_Errors.raise_error uu___4 uu___5
                  else ());
                 (let uu___3 = let uu___4 = push env1 in prep uu___4 in
                  (uu___3, true)))
let (enter_monad_scope : env -> FStar_Ident.ident -> env) =
  fun env1 ->
    fun mname ->
      match env1.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Ident.string_of_id mname in
                let uu___4 =
                  let uu___5 = FStar_Ident.string_of_id mname' in
                  Prims.op_Hat ", but already in monad scope " uu___5 in
                Prims.op_Hat uu___3 uu___4 in
              Prims.op_Hat "Trying to define monad " uu___2 in
            (FStar_Errors.Fatal_MonadAlreadyDefined, uu___1) in
          let uu___1 = FStar_Ident.range_of_id mname in
          FStar_Errors.raise_error uu___ uu___1
      | FStar_Pervasives_Native.None ->
          let uu___ = env1 in
          {
            curmodule = (uu___.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___.modules);
            scope_mods = (uu___.scope_mods);
            exported_ids = (uu___.exported_ids);
            trans_exported_ids = (uu___.trans_exported_ids);
            includes = (uu___.includes);
            sigaccum = (uu___.sigaccum);
            sigmap = (uu___.sigmap);
            iface = (uu___.iface);
            admitted_iface = (uu___.admitted_iface);
            expect_typ = (uu___.expect_typ);
            remaining_iface_decls = (uu___.remaining_iface_decls);
            syntax_only = (uu___.syntax_only);
            ds_hooks = (uu___.ds_hooks);
            dep_graph = (uu___.dep_graph)
          }
let fail_or :
  'a .
    env ->
      (FStar_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStar_Ident.lident -> 'a
  =
  fun env1 ->
    fun lookup ->
      fun lid ->
        let uu___ = lookup lid in
        match uu___ with
        | FStar_Pervasives_Native.None ->
            let opened_modules =
              FStar_List.map
                (fun uu___1 ->
                   match uu___1 with
                   | (lid1, uu___2) -> FStar_Ident.string_of_lid lid1)
                env1.modules in
            let msg =
              let uu___1 = FStar_Ident.string_of_lid lid in
              FStar_Util.format1 "Identifier not found: [%s]" uu___1 in
            let msg1 =
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStar_Ident.ns_of_lid lid in
                  FStar_List.length uu___3 in
                uu___2 = Prims.int_zero in
              if uu___1
              then msg
              else
                (let modul =
                   let uu___3 =
                     let uu___4 = FStar_Ident.ns_of_lid lid in
                     FStar_Ident.lid_of_ids uu___4 in
                   let uu___4 = FStar_Ident.range_of_lid lid in
                   FStar_Ident.set_lid_range uu___3 uu___4 in
                 let uu___3 = resolve_module_name env1 modul true in
                 match uu___3 with
                 | FStar_Pervasives_Native.None ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     let uu___4 = FStar_Ident.string_of_lid modul in
                     FStar_Util.format3
                       "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                       msg uu___4 opened_modules1
                 | FStar_Pervasives_Native.Some modul' when
                     Prims.op_Negation
                       (FStar_List.existsb
                          (fun m ->
                             let uu___4 = FStar_Ident.string_of_lid modul' in
                             m = uu___4) opened_modules)
                     ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules in
                     let uu___4 = FStar_Ident.string_of_lid modul in
                     let uu___5 = FStar_Ident.string_of_lid modul' in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                       msg uu___4 uu___5 opened_modules1
                 | FStar_Pervasives_Native.Some modul' ->
                     let uu___4 = FStar_Ident.string_of_lid modul in
                     let uu___5 = FStar_Ident.string_of_lid modul' in
                     let uu___6 =
                       let uu___7 = FStar_Ident.ident_of_lid lid in
                       FStar_Ident.string_of_id uu___7 in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, definition %s not found"
                       msg uu___4 uu___5 uu___6) in
            let uu___1 = FStar_Ident.range_of_lid lid in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu___1
        | FStar_Pervasives_Native.Some r -> r
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup ->
    fun id ->
      let uu___ = lookup id in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Ident.string_of_id id in
                Prims.op_Hat uu___4 "]" in
              Prims.op_Hat "Identifier not found [" uu___3 in
            (FStar_Errors.Fatal_IdentifierNotFound, uu___2) in
          let uu___2 = FStar_Ident.range_of_id id in
          FStar_Errors.raise_error uu___1 uu___2
      | FStar_Pervasives_Native.Some r -> r