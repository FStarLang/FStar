open Prims
let (ugly_sigelt_to_string_hook :
  (FStarC_Syntax_Syntax.sigelt -> Prims.string) FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref (fun uu___ -> "")
type used_marker = Prims.bool FStarC_Compiler_Effect.ref
type record_or_dc =
  {
  typename: FStarC_Ident.lident ;
  constrname: FStarC_Ident.ident ;
  parms: FStarC_Syntax_Syntax.binders ;
  fields: (FStarC_Ident.ident * FStarC_Syntax_Syntax.typ) Prims.list ;
  is_private: Prims.bool ;
  is_record: Prims.bool }
let (__proj__Mkrecord_or_dc__item__typename :
  record_or_dc -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        typename
let (__proj__Mkrecord_or_dc__item__constrname :
  record_or_dc -> FStarC_Ident.ident) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        constrname
let (__proj__Mkrecord_or_dc__item__parms :
  record_or_dc -> FStarC_Syntax_Syntax.binders) =
  fun projectee ->
    match projectee with
    | { typename; constrname; parms; fields; is_private; is_record;_} ->
        parms
let (__proj__Mkrecord_or_dc__item__fields :
  record_or_dc -> (FStarC_Ident.ident * FStarC_Syntax_Syntax.typ) Prims.list)
  =
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
let (ugly_sigelt_to_string : FStarC_Syntax_Syntax.sigelt -> Prims.string) =
  fun se ->
    let uu___ = FStarC_Compiler_Effect.op_Bang ugly_sigelt_to_string_hook in
    uu___ se
type local_binding =
  (FStarC_Ident.ident * FStarC_Syntax_Syntax.bv * used_marker)
type rec_binding = (FStarC_Ident.ident * FStarC_Ident.lid * used_marker)
type scope_mod =
  | Local_binding of local_binding 
  | Rec_binding of rec_binding 
  | Module_abbrev of FStarC_Syntax_Syntax.module_abbrev 
  | Open_module_or_namespace of FStarC_Syntax_Syntax.open_module_or_namespace
  
  | Top_level_def of FStarC_Ident.ident 
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
let (__proj__Module_abbrev__item___0 :
  scope_mod -> FStarC_Syntax_Syntax.module_abbrev) =
  fun projectee -> match projectee with | Module_abbrev _0 -> _0
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu___ -> false
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> FStarC_Syntax_Syntax.open_module_or_namespace) =
  fun projectee -> match projectee with | Open_module_or_namespace _0 -> _0
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Top_level_def _0 -> true | uu___ -> false
let (__proj__Top_level_def__item___0 : scope_mod -> FStarC_Ident.ident) =
  fun projectee -> match projectee with | Top_level_def _0 -> _0
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee ->
    match projectee with | Record_or_dc _0 -> true | uu___ -> false
let (__proj__Record_or_dc__item___0 : scope_mod -> record_or_dc) =
  fun projectee -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStarC_Compiler_RBSet.t
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field 
let (uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_term_type -> true | uu___ -> false
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Exported_id_field -> true | uu___ -> false
let (uu___0 : exported_id_kind FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Exported_id_field -> "Exported_id_field"
         | Exported_id_term_type -> "Exported_id_term_type")
  }
type exported_id_set =
  exported_id_kind -> string_set FStarC_Compiler_Effect.ref
type env =
  {
  curmodule: FStarC_Ident.lident FStar_Pervasives_Native.option ;
  curmonad: FStarC_Ident.ident FStar_Pervasives_Native.option ;
  modules: (FStarC_Ident.lident * FStarC_Syntax_Syntax.modul) Prims.list ;
  scope_mods: scope_mod Prims.list ;
  exported_ids: exported_id_set FStarC_Compiler_Util.smap ;
  trans_exported_ids: exported_id_set FStarC_Compiler_Util.smap ;
  includes:
    (FStarC_Ident.lident * FStarC_Syntax_Syntax.restriction) Prims.list
      FStarC_Compiler_Effect.ref FStarC_Compiler_Util.smap
    ;
  sigaccum: FStarC_Syntax_Syntax.sigelts ;
  sigmap:
    (FStarC_Syntax_Syntax.sigelt * Prims.bool) FStarC_Compiler_Util.smap ;
  iface: Prims.bool ;
  admitted_iface: Prims.bool ;
  expect_typ: Prims.bool ;
  remaining_iface_decls:
    (FStarC_Ident.lident * FStarC_Parser_AST.decl Prims.list) Prims.list ;
  syntax_only: Prims.bool ;
  ds_hooks: dsenv_hooks ;
  dep_graph: FStarC_Parser_Dep.deps }
and dsenv_hooks =
  {
  ds_push_open_hook:
    env -> FStarC_Syntax_Syntax.open_module_or_namespace -> unit ;
  ds_push_include_hook: env -> FStarC_Ident.lident -> unit ;
  ds_push_module_abbrev_hook:
    env -> FStarC_Ident.ident -> FStarC_Ident.lident -> unit }
let (__proj__Mkenv__item__curmodule :
  env -> FStarC_Ident.lident FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmodule
let (__proj__Mkenv__item__curmonad :
  env -> FStarC_Ident.ident FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmonad
let (__proj__Mkenv__item__modules :
  env -> (FStarC_Ident.lident * FStarC_Syntax_Syntax.modul) Prims.list) =
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
  env -> exported_id_set FStarC_Compiler_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> exported_ids
let (__proj__Mkenv__item__trans_exported_ids :
  env -> exported_id_set FStarC_Compiler_Util.smap) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> trans_exported_ids
let (__proj__Mkenv__item__includes :
  env ->
    (FStarC_Ident.lident * FStarC_Syntax_Syntax.restriction) Prims.list
      FStarC_Compiler_Effect.ref FStarC_Compiler_Util.smap)
  =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> includes
let (__proj__Mkenv__item__sigaccum : env -> FStarC_Syntax_Syntax.sigelts) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> sigaccum
let (__proj__Mkenv__item__sigmap :
  env -> (FStarC_Syntax_Syntax.sigelt * Prims.bool) FStarC_Compiler_Util.smap)
  =
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
  env -> (FStarC_Ident.lident * FStarC_Parser_AST.decl Prims.list) Prims.list)
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
let (__proj__Mkenv__item__dep_graph : env -> FStarC_Parser_Dep.deps) =
  fun projectee ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> dep_graph
let (__proj__Mkdsenv_hooks__item__ds_push_open_hook :
  dsenv_hooks -> env -> FStarC_Syntax_Syntax.open_module_or_namespace -> unit)
  =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_open_hook
let (__proj__Mkdsenv_hooks__item__ds_push_include_hook :
  dsenv_hooks -> env -> FStarC_Ident.lident -> unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_include_hook
let (__proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook :
  dsenv_hooks -> env -> FStarC_Ident.ident -> FStarC_Ident.lident -> unit) =
  fun projectee ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_module_abbrev_hook
let (mk_dsenv_hooks :
  (env -> FStarC_Syntax_Syntax.open_module_or_namespace -> unit) ->
    (env -> FStarC_Ident.lident -> unit) ->
      (env -> FStarC_Ident.ident -> FStarC_Ident.lident -> unit) ->
        dsenv_hooks)
  =
  fun open_hook ->
    fun include_hook ->
      fun module_abbrev_hook ->
        {
          ds_push_open_hook = open_hook;
          ds_push_include_hook = include_hook;
          ds_push_module_abbrev_hook = module_abbrev_hook
        }
type 'a withenv = env -> ('a * env)
type foundname =
  | Term_name of (FStarC_Syntax_Syntax.typ * FStarC_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStarC_Syntax_Syntax.sigelt * FStarC_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Term_name _0 -> true | uu___ -> false
let (__proj__Term_name__item___0 :
  foundname ->
    (FStarC_Syntax_Syntax.typ * FStarC_Syntax_Syntax.attribute Prims.list))
  = fun projectee -> match projectee with | Term_name _0 -> _0
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee ->
    match projectee with | Eff_name _0 -> true | uu___ -> false
let (__proj__Eff_name__item___0 :
  foundname -> (FStarC_Syntax_Syntax.sigelt * FStarC_Ident.lident)) =
  fun projectee -> match projectee with | Eff_name _0 -> _0
let (default_ds_hooks : dsenv_hooks) =
  {
    ds_push_open_hook = (fun uu___ -> fun uu___1 -> ());
    ds_push_include_hook = (fun uu___ -> fun uu___1 -> ());
    ds_push_module_abbrev_hook =
      (fun uu___ -> fun uu___1 -> fun uu___2 -> ())
  }
let (set_iface : env -> Prims.bool -> env) =
  fun env1 ->
    fun b ->
      {
        curmodule = (env1.curmodule);
        curmonad = (env1.curmonad);
        modules = (env1.modules);
        scope_mods = (env1.scope_mods);
        exported_ids = (env1.exported_ids);
        trans_exported_ids = (env1.trans_exported_ids);
        includes = (env1.includes);
        sigaccum = (env1.sigaccum);
        sigmap = (env1.sigmap);
        iface = b;
        admitted_iface = (env1.admitted_iface);
        expect_typ = (env1.expect_typ);
        remaining_iface_decls = (env1.remaining_iface_decls);
        syntax_only = (env1.syntax_only);
        ds_hooks = (env1.ds_hooks);
        dep_graph = (env1.dep_graph)
      }
let (iface : env -> Prims.bool) = fun e -> e.iface
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      {
        curmodule = (e.curmodule);
        curmonad = (e.curmonad);
        modules = (e.modules);
        scope_mods = (e.scope_mods);
        exported_ids = (e.exported_ids);
        trans_exported_ids = (e.trans_exported_ids);
        includes = (e.includes);
        sigaccum = (e.sigaccum);
        sigmap = (e.sigmap);
        iface = (e.iface);
        admitted_iface = b;
        expect_typ = (e.expect_typ);
        remaining_iface_decls = (e.remaining_iface_decls);
        syntax_only = (e.syntax_only);
        ds_hooks = (e.ds_hooks);
        dep_graph = (e.dep_graph)
      }
let (admitted_iface : env -> Prims.bool) = fun e -> e.admitted_iface
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e ->
    fun b ->
      {
        curmodule = (e.curmodule);
        curmonad = (e.curmonad);
        modules = (e.modules);
        scope_mods = (e.scope_mods);
        exported_ids = (e.exported_ids);
        trans_exported_ids = (e.trans_exported_ids);
        includes = (e.includes);
        sigaccum = (e.sigaccum);
        sigmap = (e.sigmap);
        iface = (e.iface);
        admitted_iface = (e.admitted_iface);
        expect_typ = b;
        remaining_iface_decls = (e.remaining_iface_decls);
        syntax_only = (e.syntax_only);
        ds_hooks = (e.ds_hooks);
        dep_graph = (e.dep_graph)
      }
let (expect_typ : env -> Prims.bool) = fun e -> e.expect_typ
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type]
let (transitive_exported_ids :
  env -> FStarC_Ident.lident -> Prims.string Prims.list) =
  fun env1 ->
    fun lid ->
      let module_name = FStarC_Ident.string_of_lid lid in
      let uu___ =
        FStarC_Compiler_Util.smap_try_find env1.trans_exported_ids
          module_name in
      match uu___ with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some exported_id_set1 ->
          let uu___1 =
            let uu___2 = exported_id_set1 Exported_id_term_type in
            FStarC_Compiler_Effect.op_Bang uu___2 in
          FStarC_Class_Setlike.elems ()
            (Obj.magic
               (FStarC_Compiler_RBSet.setlike_rbset
                  FStarC_Class_Ord.ord_string)) (Obj.magic uu___1)
let (opens_and_abbrevs :
  env ->
    (FStarC_Syntax_Syntax.open_module_or_namespace,
      FStarC_Syntax_Syntax.module_abbrev) FStar_Pervasives.either Prims.list)
  =
  fun env1 ->
    FStarC_Compiler_List.collect
      (fun uu___ ->
         match uu___ with
         | Open_module_or_namespace payload -> [FStar_Pervasives.Inl payload]
         | Module_abbrev (id, lid) -> [FStar_Pervasives.Inr (id, lid)]
         | uu___1 -> []) env1.scope_mods
let (open_modules :
  env -> (FStarC_Ident.lident * FStarC_Syntax_Syntax.modul) Prims.list) =
  fun e -> e.modules
let (open_modules_and_namespaces : env -> FStarC_Ident.lident Prims.list) =
  fun env1 ->
    FStarC_Compiler_List.filter_map
      (fun uu___ ->
         match uu___ with
         | Open_module_or_namespace (lid, _info, _restriction) ->
             FStar_Pervasives_Native.Some lid
         | uu___1 -> FStar_Pervasives_Native.None) env1.scope_mods
let (module_abbrevs :
  env -> (FStarC_Ident.ident * FStarC_Ident.lident) Prims.list) =
  fun env1 ->
    FStarC_Compiler_List.filter_map
      (fun uu___ ->
         match uu___ with
         | Module_abbrev (l, m) -> FStar_Pervasives_Native.Some (l, m)
         | uu___1 -> FStar_Pervasives_Native.None) env1.scope_mods
let (set_current_module : env -> FStarC_Ident.lident -> env) =
  fun e ->
    fun l ->
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (e.curmonad);
        modules = (e.modules);
        scope_mods = (e.scope_mods);
        exported_ids = (e.exported_ids);
        trans_exported_ids = (e.trans_exported_ids);
        includes = (e.includes);
        sigaccum = (e.sigaccum);
        sigmap = (e.sigmap);
        iface = (e.iface);
        admitted_iface = (e.admitted_iface);
        expect_typ = (e.expect_typ);
        remaining_iface_decls = (e.remaining_iface_decls);
        syntax_only = (e.syntax_only);
        ds_hooks = (e.ds_hooks);
        dep_graph = (e.dep_graph)
      }
let (current_module : env -> FStarC_Ident.lident) =
  fun env1 ->
    match env1.curmodule with
    | FStar_Pervasives_Native.None -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
let (iface_decls :
  env ->
    FStarC_Ident.lident ->
      FStarC_Parser_AST.decl Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ =
        FStarC_Compiler_List.tryFind
          (fun uu___1 ->
             match uu___1 with | (m, uu___2) -> FStarC_Ident.lid_equals l m)
          env1.remaining_iface_decls in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu___1, decls) ->
          FStar_Pervasives_Native.Some decls
let (set_iface_decls :
  env -> FStarC_Ident.lident -> FStarC_Parser_AST.decl Prims.list -> env) =
  fun env1 ->
    fun l ->
      fun ds ->
        let uu___ =
          FStarC_Compiler_List.partition
            (fun uu___1 ->
               match uu___1 with | (m, uu___2) -> FStarC_Ident.lid_equals l m)
            env1.remaining_iface_decls in
        match uu___ with
        | (uu___1, rest) ->
            {
              curmodule = (env1.curmodule);
              curmonad = (env1.curmonad);
              modules = (env1.modules);
              scope_mods = (env1.scope_mods);
              exported_ids = (env1.exported_ids);
              trans_exported_ids = (env1.trans_exported_ids);
              includes = (env1.includes);
              sigaccum = (env1.sigaccum);
              sigmap = (env1.sigmap);
              iface = (env1.iface);
              admitted_iface = (env1.admitted_iface);
              expect_typ = (env1.expect_typ);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (env1.syntax_only);
              ds_hooks = (env1.ds_hooks);
              dep_graph = (env1.dep_graph)
            }
let (qual : FStarC_Ident.lident -> FStarC_Ident.ident -> FStarC_Ident.lident)
  = FStarC_Ident.qual_id
let (qualify : env -> FStarC_Ident.ident -> FStarC_Ident.lident) =
  fun env1 ->
    fun id ->
      match env1.curmonad with
      | FStar_Pervasives_Native.None ->
          let uu___ = current_module env1 in qual uu___ id
      | FStar_Pervasives_Native.Some monad ->
          let uu___ = let uu___1 = current_module env1 in qual uu___1 monad in
          FStarC_Syntax_Util.mk_field_projector_name_from_ident uu___ id
let (syntax_only : env -> Prims.bool) = fun env1 -> env1.syntax_only
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env1 ->
    fun b ->
      {
        curmodule = (env1.curmodule);
        curmonad = (env1.curmonad);
        modules = (env1.modules);
        scope_mods = (env1.scope_mods);
        exported_ids = (env1.exported_ids);
        trans_exported_ids = (env1.trans_exported_ids);
        includes = (env1.includes);
        sigaccum = (env1.sigaccum);
        sigmap = (env1.sigmap);
        iface = (env1.iface);
        admitted_iface = (env1.admitted_iface);
        expect_typ = (env1.expect_typ);
        remaining_iface_decls = (env1.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (env1.ds_hooks);
        dep_graph = (env1.dep_graph)
      }
let (ds_hooks : env -> dsenv_hooks) = fun env1 -> env1.ds_hooks
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env1 ->
    fun hooks ->
      {
        curmodule = (env1.curmodule);
        curmonad = (env1.curmonad);
        modules = (env1.modules);
        scope_mods = (env1.scope_mods);
        exported_ids = (env1.exported_ids);
        trans_exported_ids = (env1.trans_exported_ids);
        includes = (env1.includes);
        sigaccum = (env1.sigaccum);
        sigmap = (env1.sigmap);
        iface = (env1.iface);
        admitted_iface = (env1.admitted_iface);
        expect_typ = (env1.expect_typ);
        remaining_iface_decls = (env1.remaining_iface_decls);
        syntax_only = (env1.syntax_only);
        ds_hooks = hooks;
        dep_graph = (env1.dep_graph)
      }
let new_sigmap : 'uuuuu . unit -> 'uuuuu FStarC_Compiler_Util.smap =
  fun uu___ -> FStarC_Compiler_Util.smap_create (Prims.of_int (100))
let (empty_env : FStarC_Parser_Dep.deps -> env) =
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
let (dep_graph : env -> FStarC_Parser_Dep.deps) = fun env1 -> env1.dep_graph
let (set_dep_graph : env -> FStarC_Parser_Dep.deps -> env) =
  fun env1 ->
    fun ds ->
      {
        curmodule = (env1.curmodule);
        curmonad = (env1.curmonad);
        modules = (env1.modules);
        scope_mods = (env1.scope_mods);
        exported_ids = (env1.exported_ids);
        trans_exported_ids = (env1.trans_exported_ids);
        includes = (env1.includes);
        sigaccum = (env1.sigaccum);
        sigmap = (env1.sigmap);
        iface = (env1.iface);
        admitted_iface = (env1.admitted_iface);
        expect_typ = (env1.expect_typ);
        remaining_iface_decls = (env1.remaining_iface_decls);
        syntax_only = (env1.syntax_only);
        ds_hooks = (env1.ds_hooks);
        dep_graph = ds
      }
let (sigmap :
  env -> (FStarC_Syntax_Syntax.sigelt * Prims.bool) FStarC_Compiler_Util.smap)
  = fun env1 -> env1.sigmap
let (set_bv_range :
  FStarC_Syntax_Syntax.bv ->
    FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.bv)
  =
  fun bv ->
    fun r ->
      let id = FStarC_Ident.set_id_range r bv.FStarC_Syntax_Syntax.ppname in
      {
        FStarC_Syntax_Syntax.ppname = id;
        FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
        FStarC_Syntax_Syntax.sort = (bv.FStarC_Syntax_Syntax.sort)
      }
let (bv_to_name :
  FStarC_Syntax_Syntax.bv ->
    FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.term)
  =
  fun bv ->
    fun r ->
      let uu___ = set_bv_range bv r in FStarC_Syntax_Syntax.bv_to_name uu___
let (unmangleMap :
  (Prims.string * Prims.string * FStarC_Syntax_Syntax.fv_qual
    FStar_Pervasives_Native.option) Prims.list)
  =
  [("op_ColonColon", "Cons",
     (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Pervasives_Native.None)]
let (unmangleOpName :
  FStarC_Ident.ident ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun id ->
    FStarC_Compiler_Util.find_map unmangleMap
      (fun uu___ ->
         match uu___ with
         | (x, y, dq) ->
             let uu___1 =
               let uu___2 = FStarC_Ident.string_of_id id in uu___2 = x in
             if uu___1
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Ident.range_of_id id in
                   FStarC_Ident.lid_of_path ["Prims"; y] uu___4 in
                 FStarC_Syntax_Syntax.fvar_with_dd uu___3 dq in
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
    FStarC_Ident.ident Prims.list ->
      FStarC_Ident.ident ->
        record_or_dc -> (record_or_dc -> 'uuuuu cont_t) -> 'uuuuu cont_t
  =
  fun ns ->
    fun id ->
      fun record ->
        fun cont ->
          let typename' =
            let uu___ =
              let uu___1 =
                let uu___2 = FStarC_Ident.ident_of_lid record.typename in
                [uu___2] in
              FStarC_Compiler_List.op_At ns uu___1 in
            FStarC_Ident.lid_of_ids uu___ in
          let uu___ = FStarC_Ident.lid_equals typename' record.typename in
          if uu___
          then
            let fname =
              let uu___1 =
                let uu___2 = FStarC_Ident.ns_of_lid record.typename in
                FStarC_Compiler_List.op_At uu___2 [id] in
              FStarC_Ident.lid_of_ids uu___1 in
            let find =
              FStarC_Compiler_Util.find_map record.fields
                (fun uu___1 ->
                   match uu___1 with
                   | (f, uu___2) ->
                       let uu___3 =
                         let uu___4 = FStarC_Ident.string_of_id id in
                         let uu___5 = FStarC_Ident.string_of_id f in
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
      (exported_id_kind -> string_set FStarC_Compiler_Effect.ref)
        FStar_Pervasives_Native.option)
  =
  fun e ->
    fun mname -> FStarC_Compiler_Util.smap_try_find e.exported_ids mname
let (get_trans_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStarC_Compiler_Effect.ref)
        FStar_Pervasives_Native.option)
  =
  fun e ->
    fun mname ->
      FStarC_Compiler_Util.smap_try_find e.trans_exported_ids mname
let (string_of_exported_id_kind : exported_id_kind -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Exported_id_field -> "field"
    | Exported_id_term_type -> "term/type"
let (is_exported_id_termtype : exported_id_kind -> Prims.bool) =
  fun uu___ ->
    match uu___ with | Exported_id_term_type -> true | uu___1 -> false
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___ -> match uu___ with | Exported_id_field -> true | uu___1 -> false
let find_in_module_with_includes :
  'a .
    exported_id_kind ->
      (FStarC_Ident.lident -> 'a cont_t) ->
        'a cont_t ->
          env -> FStarC_Ident.lident -> FStarC_Ident.ident -> 'a cont_t
  =
  fun eikind ->
    fun find_in_module ->
      fun find_in_module_default ->
        fun env1 ->
          fun ns ->
            fun id ->
              let rec aux uu___ =
                match uu___ with
                | [] -> find_in_module_default
                | (modul, id1)::q ->
                    let mname = FStarC_Ident.string_of_lid modul in
                    let not_shadowed =
                      let uu___1 = get_exported_id_set env1 mname in
                      match uu___1 with
                      | FStar_Pervasives_Native.None -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu___2 = mex eikind in
                            FStarC_Compiler_Effect.op_Bang uu___2 in
                          let uu___2 = FStarC_Ident.string_of_id id1 in
                          FStarC_Class_Setlike.mem ()
                            (Obj.magic
                               (FStarC_Compiler_RBSet.setlike_rbset
                                  FStarC_Class_Ord.ord_string)) uu___2
                            (Obj.magic mexports) in
                    let mincludes =
                      let uu___1 =
                        FStarC_Compiler_Util.smap_try_find env1.includes
                          mname in
                      match uu___1 with
                      | FStar_Pervasives_Native.None -> []
                      | FStar_Pervasives_Native.Some minc ->
                          let uu___2 = FStarC_Compiler_Effect.op_Bang minc in
                          FStarC_Compiler_List.filter_map
                            (fun uu___3 ->
                               match uu___3 with
                               | (ns1, restriction) ->
                                   let opt =
                                     FStarC_Syntax_Syntax.is_ident_allowed_by_restriction
                                       id1 restriction in
                                   FStarC_Compiler_Util.map_opt opt
                                     (fun id2 -> (ns1, id2))) uu___2 in
                    let look_into =
                      if not_shadowed
                      then
                        let uu___1 = qual modul id1 in find_in_module uu___1
                      else Cont_ignore in
                    (match look_into with
                     | Cont_ignore ->
                         aux (FStarC_Compiler_List.op_At mincludes q)
                     | uu___1 -> look_into) in
              aux [(ns, id)]
let try_lookup_id'' :
  'a .
    env ->
      FStarC_Ident.ident ->
        exported_id_kind ->
          (local_binding -> 'a cont_t) ->
            (rec_binding -> 'a cont_t) ->
              (record_or_dc -> 'a cont_t) ->
                (FStarC_Ident.lident -> 'a cont_t) ->
                  ('a cont_t -> FStarC_Ident.ident -> 'a cont_t) ->
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
                        let uu___3 = FStarC_Ident.string_of_id id' in
                        let uu___4 = FStarC_Ident.string_of_id id in
                        uu___3 = uu___4 in
                  let check_rec_binding_id uu___ =
                    match uu___ with
                    | (id', uu___1, uu___2) ->
                        let uu___3 = FStarC_Ident.string_of_id id' in
                        let uu___4 = FStarC_Ident.string_of_id id in
                        uu___3 = uu___4 in
                  let curmod_ns =
                    let uu___ = current_module env1 in
                    FStarC_Ident.ids_of_lid uu___ in
                  let proc uu___ =
                    match uu___ with
                    | Local_binding l when check_local_binding_id l ->
                        let uu___1 = l in
                        (match uu___1 with
                         | (uu___2, uu___3, used_marker1) ->
                             (FStarC_Compiler_Effect.op_Colon_Equals
                                used_marker1 true;
                              k_local_binding l))
                    | Rec_binding r when check_rec_binding_id r ->
                        let uu___1 = r in
                        (match uu___1 with
                         | (uu___2, uu___3, used_marker1) ->
                             (FStarC_Compiler_Effect.op_Colon_Equals
                                used_marker1 true;
                              k_rec_binding r))
                    | Open_module_or_namespace
                        (ns, FStarC_Syntax_Syntax.Open_module, restriction)
                        ->
                        let uu___1 =
                          FStarC_Syntax_Syntax.is_ident_allowed_by_restriction
                            id restriction in
                        (match uu___1 with
                         | FStar_Pervasives_Native.None -> Cont_ignore
                         | FStar_Pervasives_Native.Some id1 ->
                             find_in_module_with_includes eikind
                               find_in_module Cont_ignore env1 ns id1)
                    | Top_level_def id' when
                        let uu___1 = FStarC_Ident.string_of_id id' in
                        let uu___2 = FStarC_Ident.string_of_id id in
                        uu___1 = uu___2 -> lookup_default_id Cont_ignore id
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu___1 = FStarC_Ident.lid_of_ids curmod_ns in
                        find_in_module_with_includes Exported_id_field
                          (fun lid ->
                             let id1 = FStarC_Ident.ident_of_lid lid in
                             let uu___2 = FStarC_Ident.ns_of_lid lid in
                             find_in_record uu___2 id1 r k_record)
                          Cont_ignore env1 uu___1 id
                    | Record_or_dc r when is_exported_id_termtype eikind ->
                        let uu___1 =
                          let uu___2 = FStarC_Ident.ident_of_lid r.typename in
                          FStarC_Ident.ident_equals uu___2 id in
                        if uu___1 then k_record r else Cont_ignore
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
    FStarC_Compiler_Range_Type.range ->
      ('uuuuu * FStarC_Syntax_Syntax.bv * 'uuuuu1) ->
        FStarC_Syntax_Syntax.term
  =
  fun r -> fun uu___ -> match uu___ with | (id', x, uu___1) -> bv_to_name x r
let find_in_module :
  'uuuuu .
    env ->
      FStarC_Ident.lident ->
        (FStarC_Ident.lident ->
           (FStarC_Syntax_Syntax.sigelt * Prims.bool) -> 'uuuuu)
          -> 'uuuuu -> 'uuuuu
  =
  fun env1 ->
    fun lid ->
      fun k_global_def ->
        fun k_not_found ->
          let uu___ =
            let uu___1 = FStarC_Ident.string_of_lid lid in
            FStarC_Compiler_Util.smap_try_find (sigmap env1) uu___1 in
          match uu___ with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None -> k_not_found
let (try_lookup_id :
  env ->
    FStarC_Ident.ident ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
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
                 let uu___3 = FStarC_Ident.range_of_id id in
                 found_local_binding uu___3 r in
               Cont_ok uu___2) (fun uu___2 -> Cont_fail)
            (fun uu___2 -> Cont_ignore)
            (fun i ->
               find_in_module env1 i (fun uu___2 -> fun uu___3 -> Cont_fail)
                 Cont_ignore) (fun uu___2 -> fun uu___3 -> Cont_fail)
let lookup_default_id :
  'a .
    env ->
      FStarC_Ident.ident ->
        (FStarC_Ident.lident ->
           (FStarC_Syntax_Syntax.sigelt * Prims.bool) -> 'a cont_t)
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
                  let uu___2 = FStarC_Ident.string_of_lid lid in
                  FStarC_Compiler_Util.smap_try_find (sigmap env1) uu___2 in
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
let (lid_is_curmod : env -> FStarC_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      match env1.curmodule with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some m -> FStarC_Ident.lid_equals lid m
let (module_is_defined : env -> FStarC_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      (lid_is_curmod env1 lid) ||
        (FStarC_Compiler_List.existsb
           (fun x ->
              FStarC_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env1.modules)
let (resolve_module_name :
  env ->
    FStarC_Ident.lident ->
      Prims.bool -> FStarC_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      fun honor_ns ->
        let nslen =
          let uu___ = FStarC_Ident.ns_of_lid lid in
          FStarC_Compiler_List.length uu___ in
        let rec aux uu___ =
          match uu___ with
          | [] ->
              let uu___1 = module_is_defined env1 lid in
              if uu___1
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace
              (ns, FStarC_Syntax_Syntax.Open_namespace, restriction))::q when
              honor_ns ->
              let new_lid =
                let uu___1 =
                  let uu___2 = FStarC_Ident.path_of_lid ns in
                  let uu___3 = FStarC_Ident.path_of_lid lid in
                  FStarC_Compiler_List.op_At uu___2 uu___3 in
                let uu___2 = FStarC_Ident.range_of_lid lid in
                FStarC_Ident.lid_of_path uu___1 uu___2 in
              let uu___1 = module_is_defined env1 new_lid in
              if uu___1 then FStar_Pervasives_Native.Some new_lid else aux q
          | (Module_abbrev (name, modul))::uu___1 when
              (nslen = Prims.int_zero) &&
                (let uu___2 = FStarC_Ident.string_of_id name in
                 let uu___3 =
                   let uu___4 = FStarC_Ident.ident_of_lid lid in
                   FStarC_Ident.string_of_id uu___4 in
                 uu___2 = uu___3)
              -> FStar_Pervasives_Native.Some modul
          | uu___1::q -> aux q in
        aux env1.scope_mods
let (is_open :
  env -> FStarC_Ident.lident -> FStarC_Syntax_Syntax.open_kind -> Prims.bool)
  =
  fun env1 ->
    fun lid ->
      fun open_kind ->
        FStarC_Compiler_List.existsb
          (fun uu___ ->
             match uu___ with
             | Open_module_or_namespace
                 (ns, k, FStarC_Syntax_Syntax.Unrestricted) ->
                 (k = open_kind) && (FStarC_Ident.lid_equals lid ns)
             | uu___1 -> false) env1.scope_mods
let (namespace_is_open : env -> FStarC_Ident.lident -> Prims.bool) =
  fun env1 -> fun lid -> is_open env1 lid FStarC_Syntax_Syntax.Open_namespace
let (module_is_open : env -> FStarC_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      (lid_is_curmod env1 lid) ||
        (is_open env1 lid FStarC_Syntax_Syntax.Open_module)
let (shorten_module_path :
  env ->
    FStarC_Ident.ident Prims.list ->
      Prims.bool ->
        (FStarC_Ident.ident Prims.list * FStarC_Ident.ident Prims.list))
  =
  fun env1 ->
    fun ids ->
      fun is_full_path ->
        let rec aux revns id =
          let lid =
            FStarC_Ident.lid_of_ns_and_id (FStarC_Compiler_List.rev revns) id in
          let uu___ = namespace_is_open env1 lid in
          if uu___
          then
            FStar_Pervasives_Native.Some
              ((FStarC_Compiler_List.rev (id :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu___2 = aux rev_ns_prefix ns_last_id in
                 FStarC_Compiler_Util.map_option
                   (fun uu___3 ->
                      match uu___3 with
                      | (stripped_ids, rev_kept_ids) ->
                          (stripped_ids, (id :: rev_kept_ids))) uu___2) in
        let do_shorten env2 ids1 =
          match FStarC_Compiler_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu___ = aux ns_rev_prefix ns_last_id in
              (match uu___ with
               | FStar_Pervasives_Native.None -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) ->
                   (stripped_ids, (FStarC_Compiler_List.rev rev_kept_ids))) in
        if
          is_full_path &&
            ((FStarC_Compiler_List.length ids) > Prims.int_zero)
        then
          let uu___ =
            let uu___1 = FStarC_Ident.lid_of_ids ids in
            resolve_module_name env1 uu___1 true in
          match uu___ with
          | FStar_Pervasives_Native.Some m when module_is_open env1 m ->
              (ids, [])
          | uu___1 -> do_shorten env1 ids
        else do_shorten env1 ids
let resolve_in_open_namespaces'' :
  'a .
    env ->
      FStarC_Ident.lident ->
        exported_id_kind ->
          (local_binding -> 'a cont_t) ->
            (rec_binding -> 'a cont_t) ->
              (record_or_dc -> 'a cont_t) ->
                (FStarC_Ident.lident -> 'a cont_t) ->
                  ('a cont_t -> FStarC_Ident.ident -> 'a cont_t) ->
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
                  let uu___ = FStarC_Ident.ns_of_lid lid in
                  match uu___ with
                  | uu___1::uu___2 ->
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 = FStarC_Ident.ns_of_lid lid in
                            FStarC_Ident.lid_of_ids uu___6 in
                          let uu___6 = FStarC_Ident.range_of_lid lid in
                          FStarC_Ident.set_lid_range uu___5 uu___6 in
                        resolve_module_name env1 uu___4 true in
                      (match uu___3 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu___4 =
                             let uu___5 = FStarC_Ident.ident_of_lid lid in
                             find_in_module_with_includes eikind f_module
                               Cont_fail env1 modul uu___5 in
                           option_of_cont
                             (fun uu___5 -> FStar_Pervasives_Native.None)
                             uu___4)
                  | [] ->
                      let uu___1 = FStarC_Ident.ident_of_lid lid in
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
      FStarC_Ident.lident ->
        (local_binding -> 'a FStar_Pervasives_Native.option) ->
          (rec_binding -> 'a FStar_Pervasives_Native.option) ->
            (FStarC_Ident.lident ->
               (FStarC_Syntax_Syntax.sigelt * Prims.bool) ->
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
  FStarC_Syntax_Syntax.sigelt ->
    FStarC_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se ->
    match se.FStarC_Syntax_Syntax.sigel with
    | FStarC_Syntax_Syntax.Sig_datacon
        { FStarC_Syntax_Syntax.lid1 = uu___;
          FStarC_Syntax_Syntax.us1 = uu___1;
          FStarC_Syntax_Syntax.t1 = uu___2; FStarC_Syntax_Syntax.ty_lid = l;
          FStarC_Syntax_Syntax.num_ty_params = uu___3;
          FStarC_Syntax_Syntax.mutuals1 = uu___4;
          FStarC_Syntax_Syntax.injective_type_params1 = uu___5;_}
        ->
        let qopt =
          FStarC_Compiler_Util.find_map se.FStarC_Syntax_Syntax.sigquals
            (fun uu___6 ->
               match uu___6 with
               | FStarC_Syntax_Syntax.RecordConstructor (uu___7, fs) ->
                   FStar_Pervasives_Native.Some
                     (FStarC_Syntax_Syntax.Record_ctor (l, fs))
               | uu___7 -> FStar_Pervasives_Native.None) in
        (match qopt with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStarC_Syntax_Syntax.Sig_declare_typ uu___ ->
        FStar_Pervasives_Native.None
    | uu___ -> FStar_Pervasives_Native.None
let (lb_fv :
  FStarC_Syntax_Syntax.letbinding Prims.list ->
    FStarC_Ident.lident -> FStarC_Syntax_Syntax.fv)
  =
  fun lbs ->
    fun lid ->
      let uu___ =
        FStarC_Compiler_Util.find_map lbs
          (fun lb ->
             let fv =
               FStarC_Compiler_Util.right lb.FStarC_Syntax_Syntax.lbname in
             let uu___1 = FStarC_Syntax_Syntax.fv_eq_lid fv lid in
             if uu___1
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None) in
      FStarC_Compiler_Util.must uu___
let (ns_of_lid_equals :
  FStarC_Ident.lident -> FStarC_Ident.lident -> Prims.bool) =
  fun lid ->
    fun ns ->
      (let uu___ =
         let uu___1 = FStarC_Ident.ns_of_lid lid in
         FStarC_Compiler_List.length uu___1 in
       let uu___1 =
         let uu___2 = FStarC_Ident.ids_of_lid ns in
         FStarC_Compiler_List.length uu___2 in
       uu___ = uu___1) &&
        (let uu___ =
           let uu___1 = FStarC_Ident.ns_of_lid lid in
           FStarC_Ident.lid_of_ids uu___1 in
         FStarC_Ident.lid_equals uu___ ns)
let (try_lookup_name :
  Prims.bool ->
    Prims.bool ->
      env -> FStarC_Ident.lident -> foundname FStar_Pervasives_Native.option)
  =
  fun any_val ->
    fun exclude_interf ->
      fun env1 ->
        fun lid ->
          let occurrence_range = FStarC_Ident.range_of_lid lid in
          let k_global_def source_lid uu___ =
            match uu___ with
            | (uu___1, true) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se, uu___1) ->
                (match se.FStarC_Syntax_Syntax.sigel with
                 | FStarC_Syntax_Syntax.Sig_inductive_typ uu___2 ->
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           FStarC_Syntax_Syntax.fvar_with_dd source_lid
                             FStar_Pervasives_Native.None in
                         (uu___5, (se.FStarC_Syntax_Syntax.sigattrs)) in
                       Term_name uu___4 in
                     FStar_Pervasives_Native.Some uu___3
                 | FStarC_Syntax_Syntax.Sig_datacon uu___2 ->
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = fv_qual_of_se se in
                           FStarC_Syntax_Syntax.fvar_with_dd source_lid
                             uu___6 in
                         (uu___5, (se.FStarC_Syntax_Syntax.sigattrs)) in
                       Term_name uu___4 in
                     FStar_Pervasives_Native.Some uu___3
                 | FStarC_Syntax_Syntax.Sig_let
                     { FStarC_Syntax_Syntax.lbs1 = (uu___2, lbs);
                       FStarC_Syntax_Syntax.lids1 = uu___3;_}
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           FStarC_Syntax_Syntax.fvar_with_dd source_lid
                             fv.FStarC_Syntax_Syntax.fv_qual in
                         (uu___6, (se.FStarC_Syntax_Syntax.sigattrs)) in
                       Term_name uu___5 in
                     FStar_Pervasives_Native.Some uu___4
                 | FStarC_Syntax_Syntax.Sig_declare_typ
                     { FStarC_Syntax_Syntax.lid2 = lid1;
                       FStarC_Syntax_Syntax.us2 = uu___2;
                       FStarC_Syntax_Syntax.t2 = uu___3;_}
                     ->
                     let quals = se.FStarC_Syntax_Syntax.sigquals in
                     let uu___4 =
                       any_val ||
                         (FStarC_Compiler_Util.for_some
                            (fun uu___5 ->
                               match uu___5 with
                               | FStarC_Syntax_Syntax.Assumption -> true
                               | uu___6 -> false) quals) in
                     if uu___4
                     then
                       let lid2 =
                         let uu___5 = FStarC_Ident.range_of_lid source_lid in
                         FStarC_Ident.set_lid_range lid1 uu___5 in
                       let uu___5 =
                         FStarC_Compiler_Util.find_map quals
                           (fun uu___6 ->
                              match uu___6 with
                              | FStarC_Syntax_Syntax.Reflectable refl_monad
                                  -> FStar_Pervasives_Native.Some refl_monad
                              | uu___7 -> FStar_Pervasives_Native.None) in
                       (match uu___5 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStarC_Syntax_Syntax.mk
                                (FStarC_Syntax_Syntax.Tm_constant
                                   (FStarC_Const.Const_reflect refl_monad))
                                occurrence_range in
                            FStar_Pervasives_Native.Some
                              (Term_name
                                 (refl_const,
                                   (se.FStarC_Syntax_Syntax.sigattrs)))
                        | uu___6 ->
                            let uu___7 =
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 = fv_qual_of_se se in
                                  FStarC_Syntax_Syntax.fvar_with_dd lid2
                                    uu___10 in
                                (uu___9, (se.FStarC_Syntax_Syntax.sigattrs)) in
                              Term_name uu___8 in
                            FStar_Pervasives_Native.Some uu___7)
                     else FStar_Pervasives_Native.None
                 | FStarC_Syntax_Syntax.Sig_new_effect ne ->
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 = FStarC_Ident.range_of_lid source_lid in
                           FStarC_Ident.set_lid_range
                             ne.FStarC_Syntax_Syntax.mname uu___5 in
                         (se, uu___4) in
                       Eff_name uu___3 in
                     FStar_Pervasives_Native.Some uu___2
                 | FStarC_Syntax_Syntax.Sig_effect_abbrev uu___2 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStarC_Syntax_Syntax.Sig_splice
                     { FStarC_Syntax_Syntax.is_typed = uu___2;
                       FStarC_Syntax_Syntax.lids2 = lids;
                       FStarC_Syntax_Syntax.tac = t;_}
                     ->
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           FStarC_Syntax_Syntax.fvar_with_dd source_lid
                             FStar_Pervasives_Native.None in
                         (uu___5, []) in
                       Term_name uu___4 in
                     FStar_Pervasives_Native.Some uu___3
                 | uu___2 -> FStar_Pervasives_Native.None) in
          let k_local_binding r =
            let t =
              let uu___ = FStarC_Ident.range_of_lid lid in
              found_local_binding uu___ r in
            FStar_Pervasives_Native.Some (Term_name (t, [])) in
          let k_rec_binding uu___ =
            match uu___ with
            | (id, l, used_marker1) ->
                (FStarC_Compiler_Effect.op_Colon_Equals used_marker1 true;
                 (let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = FStarC_Ident.range_of_lid lid in
                          FStarC_Ident.set_lid_range l uu___6 in
                        FStarC_Syntax_Syntax.fvar_with_dd uu___5
                          FStar_Pervasives_Native.None in
                      (uu___4, []) in
                    Term_name uu___3 in
                  FStar_Pervasives_Native.Some uu___2)) in
          let found_unmangled =
            let uu___ = FStarC_Ident.ns_of_lid lid in
            match uu___ with
            | [] ->
                let uu___1 =
                  let uu___2 = FStarC_Ident.ident_of_lid lid in
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
      FStarC_Ident.lident ->
        (FStarC_Syntax_Syntax.sigelt * FStarC_Ident.lident)
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
    FStarC_Ident.lident -> FStarC_Ident.lident FStar_Pervasives_Native.option)
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
    FStarC_Ident.lident ->
      (FStarC_Ident.lident * FStarC_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu___ with
      | FStar_Pervasives_Native.Some
          ({
             FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_new_effect
               ne;
             FStarC_Syntax_Syntax.sigrng = uu___1;
             FStarC_Syntax_Syntax.sigquals = uu___2;
             FStarC_Syntax_Syntax.sigmeta = uu___3;
             FStarC_Syntax_Syntax.sigattrs = uu___4;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
             FStarC_Syntax_Syntax.sigopts = uu___6;_},
           l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStarC_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStarC_Syntax_Syntax.sigel =
               FStarC_Syntax_Syntax.Sig_effect_abbrev
               { FStarC_Syntax_Syntax.lid4 = uu___1;
                 FStarC_Syntax_Syntax.us4 = uu___2;
                 FStarC_Syntax_Syntax.bs2 = uu___3;
                 FStarC_Syntax_Syntax.comp1 = uu___4;
                 FStarC_Syntax_Syntax.cflags = cattributes;_};
             FStarC_Syntax_Syntax.sigrng = uu___5;
             FStarC_Syntax_Syntax.sigquals = uu___6;
             FStarC_Syntax_Syntax.sigmeta = uu___7;
             FStarC_Syntax_Syntax.sigattrs = uu___8;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___9;
             FStarC_Syntax_Syntax.sigopts = uu___10;_},
           l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu___1 -> FStar_Pervasives_Native.None
let (try_lookup_effect_defn :
  env ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu___ with
      | FStar_Pervasives_Native.Some
          ({
             FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_new_effect
               ne;
             FStarC_Syntax_Syntax.sigrng = uu___1;
             FStarC_Syntax_Syntax.sigquals = uu___2;
             FStarC_Syntax_Syntax.sigmeta = uu___3;
             FStarC_Syntax_Syntax.sigattrs = uu___4;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
             FStarC_Syntax_Syntax.sigopts = uu___6;_},
           uu___7)
          -> FStar_Pervasives_Native.Some ne
      | uu___1 -> FStar_Pervasives_Native.None
let (is_effect_name : env -> FStarC_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun lid ->
      let uu___ = try_lookup_effect_name env1 lid in
      match uu___ with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu___1 -> true
let (try_lookup_root_effect_name :
  env ->
    FStarC_Ident.lident -> FStarC_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ =
        try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
      match uu___ with
      | FStar_Pervasives_Native.Some
          ({
             FStarC_Syntax_Syntax.sigel =
               FStarC_Syntax_Syntax.Sig_effect_abbrev
               { FStarC_Syntax_Syntax.lid4 = l';
                 FStarC_Syntax_Syntax.us4 = uu___1;
                 FStarC_Syntax_Syntax.bs2 = uu___2;
                 FStarC_Syntax_Syntax.comp1 = uu___3;
                 FStarC_Syntax_Syntax.cflags = uu___4;_};
             FStarC_Syntax_Syntax.sigrng = uu___5;
             FStarC_Syntax_Syntax.sigquals = uu___6;
             FStarC_Syntax_Syntax.sigmeta = uu___7;
             FStarC_Syntax_Syntax.sigattrs = uu___8;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___9;
             FStarC_Syntax_Syntax.sigopts = uu___10;_},
           uu___11)
          ->
          let rec aux new_name =
            let uu___12 =
              let uu___13 = FStarC_Ident.string_of_lid new_name in
              FStarC_Compiler_Util.smap_try_find (sigmap env1) uu___13 in
            match uu___12 with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s, uu___13) ->
                (match s.FStarC_Syntax_Syntax.sigel with
                 | FStarC_Syntax_Syntax.Sig_new_effect ne ->
                     let uu___14 =
                       let uu___15 = FStarC_Ident.range_of_lid l in
                       FStarC_Ident.set_lid_range
                         ne.FStarC_Syntax_Syntax.mname uu___15 in
                     FStar_Pervasives_Native.Some uu___14
                 | FStarC_Syntax_Syntax.Sig_effect_abbrev
                     { FStarC_Syntax_Syntax.lid4 = uu___14;
                       FStarC_Syntax_Syntax.us4 = uu___15;
                       FStarC_Syntax_Syntax.bs2 = uu___16;
                       FStarC_Syntax_Syntax.comp1 = cmp;
                       FStarC_Syntax_Syntax.cflags = uu___17;_}
                     ->
                     let l'' = FStarC_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu___14 -> FStar_Pervasives_Native.None) in
          aux l'
      | FStar_Pervasives_Native.Some (uu___1, l') ->
          FStar_Pervasives_Native.Some l'
      | uu___1 -> FStar_Pervasives_Native.None
let (lookup_letbinding_quals_and_attrs :
  env ->
    FStarC_Ident.lident ->
      (FStarC_Syntax_Syntax.qualifier Prims.list *
        FStarC_Syntax_Syntax.attribute Prims.list))
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___ =
        match uu___ with
        | ({
             FStarC_Syntax_Syntax.sigel =
               FStarC_Syntax_Syntax.Sig_declare_typ uu___1;
             FStarC_Syntax_Syntax.sigrng = uu___2;
             FStarC_Syntax_Syntax.sigquals = quals;
             FStarC_Syntax_Syntax.sigmeta = uu___3;
             FStarC_Syntax_Syntax.sigattrs = attrs;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___4;
             FStarC_Syntax_Syntax.sigopts = uu___5;_},
           uu___6) -> FStar_Pervasives_Native.Some (quals, attrs)
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
    FStarC_Ident.path ->
      FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun path ->
      let uu___ =
        FStarC_Compiler_List.tryFind
          (fun uu___1 ->
             match uu___1 with
             | (mlid, modul) ->
                 let uu___2 = FStarC_Ident.path_of_lid mlid in uu___2 = path)
          env1.modules in
      match uu___ with
      | FStar_Pervasives_Native.Some (uu___1, modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (try_lookup_let :
  env ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___ =
        match uu___ with
        | ({
             FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_let
               { FStarC_Syntax_Syntax.lbs1 = (uu___1, lbs);
                 FStarC_Syntax_Syntax.lids1 = uu___2;_};
             FStarC_Syntax_Syntax.sigrng = uu___3;
             FStarC_Syntax_Syntax.sigquals = uu___4;
             FStarC_Syntax_Syntax.sigmeta = uu___5;
             FStarC_Syntax_Syntax.sigattrs = uu___6;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
             FStarC_Syntax_Syntax.sigopts = uu___8;_},
           uu___9) ->
            let fv = lb_fv lbs lid1 in
            let uu___10 =
              FStarC_Syntax_Syntax.fvar_with_dd lid1
                fv.FStarC_Syntax_Syntax.fv_qual in
            FStar_Pervasives_Native.Some uu___10
        | uu___1 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu___ -> FStar_Pervasives_Native.None)
        (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let (try_lookup_definition :
  env ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___ =
        match uu___ with
        | ({
             FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_let
               { FStarC_Syntax_Syntax.lbs1 = lbs;
                 FStarC_Syntax_Syntax.lids1 = uu___1;_};
             FStarC_Syntax_Syntax.sigrng = uu___2;
             FStarC_Syntax_Syntax.sigquals = uu___3;
             FStarC_Syntax_Syntax.sigmeta = uu___4;
             FStarC_Syntax_Syntax.sigattrs = uu___5;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
             FStarC_Syntax_Syntax.sigopts = uu___7;_},
           uu___8) ->
            FStarC_Compiler_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb ->
                 match lb.FStarC_Syntax_Syntax.lbname with
                 | FStar_Pervasives.Inr fv when
                     FStarC_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStarC_Syntax_Syntax.lbdef)
                 | uu___9 -> FStar_Pervasives_Native.None)
        | uu___1 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu___ -> FStar_Pervasives_Native.None)
        (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let (empty_include_smap :
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.restriction) Prims.list
    FStarC_Compiler_Effect.ref FStarC_Compiler_Util.smap)
  = new_sigmap ()
let (empty_exported_id_smap : exported_id_set FStarC_Compiler_Util.smap) =
  new_sigmap ()
let (try_lookup_lid' :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStarC_Ident.lident ->
          (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.attribute
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
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x ->
    match x with
    | FStar_Pervasives_Native.Some (t, uu___) ->
        FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (try_lookup_lid_with_attributes :
  env ->
    FStarC_Ident.lident ->
      (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  = fun env1 -> fun l -> try_lookup_lid' env1.iface false env1 l
let (try_lookup_lid :
  env ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ = try_lookup_lid_with_attributes env1 l in
      drop_attributes uu___
let (resolve_to_fully_qualified_name :
  env ->
    FStarC_Ident.lident -> FStarC_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let r =
        let uu___ = try_lookup_name true false env1 l in
        match uu___ with
        | FStar_Pervasives_Native.Some (Term_name (e, attrs)) ->
            let uu___1 =
              let uu___2 = FStarC_Syntax_Subst.compress e in
              uu___2.FStarC_Syntax_Syntax.n in
            (match uu___1 with
             | FStarC_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Pervasives_Native.Some
                   ((fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v)
             | uu___2 -> FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some (Eff_name (o, l1)) ->
            FStar_Pervasives_Native.Some l1
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      r
let (is_abbrev :
  env ->
    FStarC_Ident.lident -> FStarC_Ident.ipath FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      FStarC_Compiler_List.tryPick
        (fun uu___ ->
           match uu___ with
           | Module_abbrev (id, ns) when FStarC_Ident.lid_equals lid ns ->
               FStar_Pervasives_Native.Some [id]
           | uu___1 -> FStar_Pervasives_Native.None) env1.scope_mods
let (try_shorten_abbrev :
  env ->
    FStarC_Ident.ipath ->
      (FStarC_Ident.ipath * FStarC_Ident.ident Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun ns ->
      let rec aux ns1 rest =
        match ns1 with
        | [] -> FStar_Pervasives_Native.None
        | hd::tl ->
            let uu___ =
              let uu___1 =
                FStarC_Ident.lid_of_ids (FStarC_Compiler_List.rev ns1) in
              is_abbrev env1 uu___1 in
            (match uu___ with
             | FStar_Pervasives_Native.Some short ->
                 FStar_Pervasives_Native.Some (short, rest)
             | uu___1 -> aux tl (hd :: rest)) in
      aux (FStarC_Compiler_List.rev ns) []
let (shorten_lid' : env -> FStarC_Ident.lident -> FStarC_Ident.lident) =
  fun env1 ->
    fun lid0 ->
      let id0 = FStarC_Ident.ident_of_lid lid0 in
      let ns0 = FStarC_Ident.ns_of_lid lid0 in
      let uu___ =
        let uu___1 = try_shorten_abbrev env1 ns0 in
        match uu___1 with
        | FStar_Pervasives_Native.None -> ([], ns0)
        | FStar_Pervasives_Native.Some (ns, rest) -> (ns, rest) in
      match uu___ with
      | (pref, ns) ->
          let rec tails l =
            match l with
            | [] -> [[]]
            | uu___1::tl -> let uu___2 = tails tl in l :: uu___2 in
          let suffs =
            let uu___1 = tails ns in FStarC_Compiler_List.rev uu___1 in
          let try1 lid' =
            let uu___1 = resolve_to_fully_qualified_name env1 lid' in
            match uu___1 with
            | FStar_Pervasives_Native.Some lid2 when
                FStarC_Ident.lid_equals lid2 lid0 -> true
            | uu___2 -> false in
          let rec go nss =
            match nss with
            | ns1::rest ->
                let lid' =
                  FStarC_Ident.lid_of_ns_and_id
                    (FStarC_Compiler_List.op_At pref ns1) id0 in
                let uu___1 = try1 lid' in if uu___1 then lid' else go rest
            | [] -> lid0 in
          let r = go suffs in r
let (shorten_lid : env -> FStarC_Ident.lid -> FStarC_Ident.lid) =
  fun env1 ->
    fun lid0 ->
      match env1.curmodule with
      | FStar_Pervasives_Native.None -> lid0
      | uu___ -> shorten_lid' env1 lid0
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStarC_Ident.lident ->
      (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let env' =
        {
          curmodule = (env1.curmodule);
          curmonad = (env1.curmonad);
          modules = (env1.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (env1.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (env1.sigaccum);
          sigmap = (env1.sigmap);
          iface = (env1.iface);
          admitted_iface = (env1.admitted_iface);
          expect_typ = (env1.expect_typ);
          remaining_iface_decls = (env1.remaining_iface_decls);
          syntax_only = (env1.syntax_only);
          ds_hooks = (env1.ds_hooks);
          dep_graph = (env1.dep_graph)
        } in
      try_lookup_lid_with_attributes env' l
let (try_lookup_lid_no_resolve :
  env ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun l ->
      let uu___ = try_lookup_lid_with_attributes_no_resolve env1 l in
      drop_attributes uu___
let (try_lookup_datacon :
  env ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 se =
        match se with
        | ({
             FStarC_Syntax_Syntax.sigel =
               FStarC_Syntax_Syntax.Sig_declare_typ uu___;
             FStarC_Syntax_Syntax.sigrng = uu___1;
             FStarC_Syntax_Syntax.sigquals = quals;
             FStarC_Syntax_Syntax.sigmeta = uu___2;
             FStarC_Syntax_Syntax.sigattrs = uu___3;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___4;
             FStarC_Syntax_Syntax.sigopts = uu___5;_},
           uu___6) ->
            let uu___7 =
              FStarC_Compiler_Util.for_some
                (fun uu___8 ->
                   match uu___8 with
                   | FStarC_Syntax_Syntax.Assumption -> true
                   | uu___9 -> false) quals in
            if uu___7
            then
              let uu___8 =
                FStarC_Syntax_Syntax.lid_and_dd_as_fv lid1
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu___8
            else FStar_Pervasives_Native.None
        | ({
             FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_splice
               uu___;
             FStarC_Syntax_Syntax.sigrng = uu___1;
             FStarC_Syntax_Syntax.sigquals = uu___2;
             FStarC_Syntax_Syntax.sigmeta = uu___3;
             FStarC_Syntax_Syntax.sigattrs = uu___4;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
             FStarC_Syntax_Syntax.sigopts = uu___6;_},
           uu___7) ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se) in
            let uu___8 = FStarC_Syntax_Syntax.lid_and_dd_as_fv lid1 qual1 in
            FStar_Pervasives_Native.Some uu___8
        | ({
             FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
               uu___;
             FStarC_Syntax_Syntax.sigrng = uu___1;
             FStarC_Syntax_Syntax.sigquals = uu___2;
             FStarC_Syntax_Syntax.sigmeta = uu___3;
             FStarC_Syntax_Syntax.sigattrs = uu___4;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
             FStarC_Syntax_Syntax.sigopts = uu___6;_},
           uu___7) ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se) in
            let uu___8 = FStarC_Syntax_Syntax.lid_and_dd_as_fv lid1 qual1 in
            FStar_Pervasives_Native.Some uu___8
        | uu___ -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu___ -> FStar_Pervasives_Native.None)
        (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let (find_all_datacons :
  env ->
    FStarC_Ident.lident ->
      FStarC_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___ =
        match uu___ with
        | ({
             FStarC_Syntax_Syntax.sigel =
               FStarC_Syntax_Syntax.Sig_inductive_typ
               { FStarC_Syntax_Syntax.lid = uu___1;
                 FStarC_Syntax_Syntax.us = uu___2;
                 FStarC_Syntax_Syntax.params = uu___3;
                 FStarC_Syntax_Syntax.num_uniform_params = uu___4;
                 FStarC_Syntax_Syntax.t = uu___5;
                 FStarC_Syntax_Syntax.mutuals = datas;
                 FStarC_Syntax_Syntax.ds = uu___6;
                 FStarC_Syntax_Syntax.injective_type_params = uu___7;_};
             FStarC_Syntax_Syntax.sigrng = uu___8;
             FStarC_Syntax_Syntax.sigquals = uu___9;
             FStarC_Syntax_Syntax.sigmeta = uu___10;
             FStarC_Syntax_Syntax.sigattrs = uu___11;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
             FStarC_Syntax_Syntax.sigopts = uu___13;_},
           uu___14) -> FStar_Pervasives_Native.Some datas
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
  let record_cache = FStarC_Compiler_Util.mk_ref [[]] in
  let push uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Compiler_Effect.op_Bang record_cache in
        FStarC_Compiler_List.hd uu___3 in
      let uu___3 = FStarC_Compiler_Effect.op_Bang record_cache in uu___2 ::
        uu___3 in
    FStarC_Compiler_Effect.op_Colon_Equals record_cache uu___1 in
  let pop uu___ =
    let uu___1 =
      let uu___2 = FStarC_Compiler_Effect.op_Bang record_cache in
      FStarC_Compiler_List.tl uu___2 in
    FStarC_Compiler_Effect.op_Colon_Equals record_cache uu___1 in
  let snapshot uu___ = FStarC_Common.snapshot push record_cache () in
  let rollback depth = FStarC_Common.rollback pop record_cache depth in
  let peek uu___ =
    let uu___1 = FStarC_Compiler_Effect.op_Bang record_cache in
    FStarC_Compiler_List.hd uu___1 in
  let insert r =
    let uu___ =
      let uu___1 = let uu___2 = peek () in r :: uu___2 in
      let uu___2 =
        let uu___3 = FStarC_Compiler_Effect.op_Bang record_cache in
        FStarC_Compiler_List.tl uu___3 in
      uu___1 :: uu___2 in
    FStarC_Compiler_Effect.op_Colon_Equals record_cache uu___ in
  let filter uu___ =
    let rc = peek () in
    let filtered =
      FStarC_Compiler_List.filter (fun r -> Prims.op_Negation r.is_private)
        rc in
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Compiler_Effect.op_Bang record_cache in
        FStarC_Compiler_List.tl uu___3 in
      filtered :: uu___2 in
    FStarC_Compiler_Effect.op_Colon_Equals record_cache uu___1 in
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
    scope_mod Prims.list FStarC_Compiler_Effect.ref ->
      FStarC_Syntax_Syntax.sigelt -> unit)
  =
  fun e ->
    fun new_globs ->
      fun se ->
        match se.FStarC_Syntax_Syntax.sigel with
        | FStarC_Syntax_Syntax.Sig_bundle
            { FStarC_Syntax_Syntax.ses = sigs;
              FStarC_Syntax_Syntax.lids = uu___;_}
            ->
            let is_record =
              FStarC_Compiler_Util.for_some
                (fun uu___1 ->
                   match uu___1 with
                   | FStarC_Syntax_Syntax.RecordType uu___2 -> true
                   | FStarC_Syntax_Syntax.RecordConstructor uu___2 -> true
                   | uu___2 -> false) in
            let find_dc dc =
              FStarC_Compiler_Util.find_opt
                (fun uu___1 ->
                   match uu___1 with
                   | {
                       FStarC_Syntax_Syntax.sigel =
                         FStarC_Syntax_Syntax.Sig_datacon
                         { FStarC_Syntax_Syntax.lid1 = lid;
                           FStarC_Syntax_Syntax.us1 = uu___2;
                           FStarC_Syntax_Syntax.t1 = uu___3;
                           FStarC_Syntax_Syntax.ty_lid = uu___4;
                           FStarC_Syntax_Syntax.num_ty_params = uu___5;
                           FStarC_Syntax_Syntax.mutuals1 = uu___6;
                           FStarC_Syntax_Syntax.injective_type_params1 =
                             uu___7;_};
                       FStarC_Syntax_Syntax.sigrng = uu___8;
                       FStarC_Syntax_Syntax.sigquals = uu___9;
                       FStarC_Syntax_Syntax.sigmeta = uu___10;
                       FStarC_Syntax_Syntax.sigattrs = uu___11;
                       FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
                       FStarC_Syntax_Syntax.sigopts = uu___13;_} ->
                       FStarC_Ident.lid_equals dc lid
                   | uu___2 -> false) sigs in
            FStarC_Compiler_List.iter
              (fun uu___1 ->
                 match uu___1 with
                 | {
                     FStarC_Syntax_Syntax.sigel =
                       FStarC_Syntax_Syntax.Sig_inductive_typ
                       { FStarC_Syntax_Syntax.lid = typename;
                         FStarC_Syntax_Syntax.us = univs;
                         FStarC_Syntax_Syntax.params = parms;
                         FStarC_Syntax_Syntax.num_uniform_params = uu___2;
                         FStarC_Syntax_Syntax.t = uu___3;
                         FStarC_Syntax_Syntax.mutuals = uu___4;
                         FStarC_Syntax_Syntax.ds = dc::[];
                         FStarC_Syntax_Syntax.injective_type_params = uu___5;_};
                     FStarC_Syntax_Syntax.sigrng = uu___6;
                     FStarC_Syntax_Syntax.sigquals = typename_quals;
                     FStarC_Syntax_Syntax.sigmeta = uu___7;
                     FStarC_Syntax_Syntax.sigattrs = uu___8;
                     FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___9;
                     FStarC_Syntax_Syntax.sigopts = uu___10;_} ->
                     let uu___11 =
                       let uu___12 = find_dc dc in
                       FStarC_Compiler_Util.must uu___12 in
                     (match uu___11 with
                      | {
                          FStarC_Syntax_Syntax.sigel =
                            FStarC_Syntax_Syntax.Sig_datacon
                            { FStarC_Syntax_Syntax.lid1 = constrname;
                              FStarC_Syntax_Syntax.us1 = uu___12;
                              FStarC_Syntax_Syntax.t1 = t;
                              FStarC_Syntax_Syntax.ty_lid = uu___13;
                              FStarC_Syntax_Syntax.num_ty_params = n;
                              FStarC_Syntax_Syntax.mutuals1 = uu___14;
                              FStarC_Syntax_Syntax.injective_type_params1 =
                                uu___15;_};
                          FStarC_Syntax_Syntax.sigrng = uu___16;
                          FStarC_Syntax_Syntax.sigquals = uu___17;
                          FStarC_Syntax_Syntax.sigmeta = uu___18;
                          FStarC_Syntax_Syntax.sigattrs = uu___19;
                          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___20;
                          FStarC_Syntax_Syntax.sigopts = uu___21;_} ->
                          let uu___22 = FStarC_Syntax_Util.arrow_formals t in
                          (match uu___22 with
                           | (all_formals, uu___23) ->
                               let uu___24 =
                                 FStarC_Compiler_Util.first_N n all_formals in
                               (match uu___24 with
                                | (_params, formals) ->
                                    let is_rec = is_record typename_quals in
                                    let formals' =
                                      FStarC_Compiler_List.collect
                                        (fun f ->
                                           let uu___25 =
                                             (FStarC_Syntax_Syntax.is_null_bv
                                                f.FStarC_Syntax_Syntax.binder_bv)
                                               ||
                                               (is_rec &&
                                                  (FStarC_Syntax_Syntax.is_bqual_implicit
                                                     f.FStarC_Syntax_Syntax.binder_qual)) in
                                           if uu___25 then [] else [f])
                                        formals in
                                    let fields' =
                                      FStarC_Compiler_List.map
                                        (fun f ->
                                           (((f.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname),
                                             ((f.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)))
                                        formals' in
                                    let fields = fields' in
                                    let record =
                                      let uu___25 =
                                        FStarC_Ident.ident_of_lid constrname in
                                      {
                                        typename;
                                        constrname = uu___25;
                                        parms;
                                        fields;
                                        is_private =
                                          (FStarC_Compiler_List.contains
                                             FStarC_Syntax_Syntax.Private
                                             typename_quals);
                                        is_record = is_rec
                                      } in
                                    ((let uu___26 =
                                        let uu___27 =
                                          FStarC_Compiler_Effect.op_Bang
                                            new_globs in
                                        (Record_or_dc record) :: uu___27 in
                                      FStarC_Compiler_Effect.op_Colon_Equals
                                        new_globs uu___26);
                                     (match () with
                                      | () ->
                                          ((let add_field uu___27 =
                                              match uu___27 with
                                              | (id, uu___28) ->
                                                  let modul =
                                                    let uu___29 =
                                                      let uu___30 =
                                                        FStarC_Ident.ns_of_lid
                                                          constrname in
                                                      FStarC_Ident.lid_of_ids
                                                        uu___30 in
                                                    FStarC_Ident.string_of_lid
                                                      uu___29 in
                                                  let uu___29 =
                                                    get_exported_id_set e
                                                      modul in
                                                  (match uu___29 with
                                                   | FStar_Pervasives_Native.Some
                                                       my_ex ->
                                                       let my_exported_ids =
                                                         my_ex
                                                           Exported_id_field in
                                                       ((let uu___31 =
                                                           let uu___32 =
                                                             FStarC_Ident.string_of_id
                                                               id in
                                                           let uu___33 =
                                                             FStarC_Compiler_Effect.op_Bang
                                                               my_exported_ids in
                                                           Obj.magic
                                                             (FStarC_Class_Setlike.add
                                                                ()
                                                                (Obj.magic
                                                                   (FStarC_Compiler_RBSet.setlike_rbset
                                                                    FStarC_Class_Ord.ord_string))
                                                                uu___32
                                                                (Obj.magic
                                                                   uu___33)) in
                                                         FStarC_Compiler_Effect.op_Colon_Equals
                                                           my_exported_ids
                                                           uu___31);
                                                        (match () with
                                                         | () ->
                                                             let projname =
                                                               let uu___31 =
                                                                 let uu___32
                                                                   =
                                                                   FStarC_Syntax_Util.mk_field_projector_name_from_ident
                                                                    constrname
                                                                    id in
                                                                 FStarC_Ident.ident_of_lid
                                                                   uu___32 in
                                                               FStarC_Ident.string_of_id
                                                                 uu___31 in
                                                             let uu___32 =
                                                               let uu___33 =
                                                                 FStarC_Compiler_Effect.op_Bang
                                                                   my_exported_ids in
                                                               Obj.magic
                                                                 (FStarC_Class_Setlike.add
                                                                    ()
                                                                    (
                                                                    Obj.magic
                                                                    (FStarC_Compiler_RBSet.setlike_rbset
                                                                    FStarC_Class_Ord.ord_string))
                                                                    projname
                                                                    (
                                                                    Obj.magic
                                                                    uu___33)) in
                                                             FStarC_Compiler_Effect.op_Colon_Equals
                                                               my_exported_ids
                                                               uu___32))
                                                   | FStar_Pervasives_Native.None
                                                       -> ()) in
                                            FStarC_Compiler_List.iter
                                              add_field fields');
                                           (match () with
                                            | () ->
                                                insert_record_cache record))))))
                      | uu___12 -> ())
                 | uu___2 -> ()) sigs
        | uu___ -> ()
let (try_lookup_record_or_dc_by_field_name :
  env -> FStarC_Ident.lident -> record_or_dc FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun fieldname ->
      let find_in_cache fieldname1 =
        let uu___ =
          let uu___1 = FStarC_Ident.ns_of_lid fieldname1 in
          let uu___2 = FStarC_Ident.ident_of_lid fieldname1 in
          (uu___1, uu___2) in
        match uu___ with
        | (ns, id) ->
            let uu___1 = peek_record_cache () in
            FStarC_Compiler_Util.find_map uu___1
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
  env -> FStarC_Ident.lident -> record_or_dc FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun fieldname ->
      let uu___ = try_lookup_record_or_dc_by_field_name env1 fieldname in
      match uu___ with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu___1 -> FStar_Pervasives_Native.None
let (try_lookup_record_type :
  env -> FStarC_Ident.lident -> record_or_dc FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun typename ->
      let find_in_cache name =
        let uu___ =
          let uu___1 = FStarC_Ident.ns_of_lid name in
          let uu___2 = FStarC_Ident.ident_of_lid name in (uu___1, uu___2) in
        match uu___ with
        | (ns, id) ->
            let uu___1 = peek_record_cache () in
            FStarC_Compiler_Util.find_map uu___1
              (fun record ->
                 let uu___2 =
                   let uu___3 = FStarC_Ident.ident_of_lid record.typename in
                   FStarC_Ident.ident_equals uu___3 id in
                 if uu___2
                 then FStar_Pervasives_Native.Some record
                 else FStar_Pervasives_Native.None) in
      resolve_in_open_namespaces'' env1 typename Exported_id_term_type
        (fun uu___ -> Cont_ignore) (fun uu___ -> Cont_ignore)
        (fun r -> Cont_ok r)
        (fun l ->
           let uu___ = find_in_cache l in cont_of_option Cont_ignore uu___)
        (fun k -> fun uu___ -> k)
let (belongs_to_record :
  env -> FStarC_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env1 ->
    fun lid ->
      fun record ->
        let uu___ = try_lookup_record_by_field_name env1 lid in
        match uu___ with
        | FStar_Pervasives_Native.Some record' when
            let uu___1 = FStarC_Ident.nsstr record.typename in
            let uu___2 = FStarC_Ident.nsstr record'.typename in
            uu___1 = uu___2 ->
            let uu___1 =
              let uu___2 = FStarC_Ident.ns_of_lid record.typename in
              let uu___3 = FStarC_Ident.ident_of_lid lid in
              find_in_record uu___2 uu___3 record (fun uu___4 -> Cont_ok ()) in
            (match uu___1 with | Cont_ok uu___2 -> true | uu___2 -> false)
        | uu___1 -> false
let (try_lookup_dc_by_field_name :
  env ->
    FStarC_Ident.lident ->
      (FStarC_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
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
                  let uu___5 = FStarC_Ident.ns_of_lid r.typename in
                  FStarC_Compiler_List.op_At uu___5 [r.constrname] in
                FStarC_Ident.lid_of_ids uu___4 in
              let uu___4 = FStarC_Ident.range_of_lid fieldname in
              FStarC_Ident.set_lid_range uu___3 uu___4 in
            (uu___2, (r.is_record)) in
          FStar_Pervasives_Native.Some uu___1
      | uu___1 -> FStar_Pervasives_Native.None
let (string_set_ref_new : unit -> string_set FStarC_Compiler_Effect.ref) =
  fun uu___ ->
    let uu___1 =
      Obj.magic
        (FStarC_Class_Setlike.empty ()
           (Obj.magic
              (FStarC_Compiler_RBSet.setlike_rbset
                 FStarC_Class_Ord.ord_string)) ()) in
    FStarC_Compiler_Util.mk_ref uu___1
let (exported_id_set_new :
  unit -> exported_id_kind -> string_set FStarC_Compiler_Effect.ref) =
  fun uu___ ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___1 ->
      match uu___1 with
      | Exported_id_term_type -> term_type_set
      | Exported_id_field -> field_set
let (unique :
  Prims.bool -> Prims.bool -> env -> FStarC_Ident.lident -> Prims.bool) =
  fun any_val ->
    fun exclude_interface ->
      fun env1 ->
        fun lid ->
          let filter_scope_mods uu___ =
            match uu___ with | Rec_binding uu___1 -> true | uu___1 -> false in
          let this_env =
            let uu___ =
              FStarC_Compiler_List.filter filter_scope_mods env1.scope_mods in
            {
              curmodule = (env1.curmodule);
              curmonad = (env1.curmonad);
              modules = (env1.modules);
              scope_mods = uu___;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (env1.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (env1.sigaccum);
              sigmap = (env1.sigmap);
              iface = (env1.iface);
              admitted_iface = (env1.admitted_iface);
              expect_typ = (env1.expect_typ);
              remaining_iface_decls = (env1.remaining_iface_decls);
              syntax_only = (env1.syntax_only);
              ds_hooks = (env1.ds_hooks);
              dep_graph = (env1.dep_graph)
            } in
          let uu___ = try_lookup_lid' any_val exclude_interface this_env lid in
          match uu___ with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some uu___1 -> false
let (push_scope_mod : env -> scope_mod -> env) =
  fun env1 ->
    fun scope_mod1 ->
      {
        curmodule = (env1.curmodule);
        curmonad = (env1.curmonad);
        modules = (env1.modules);
        scope_mods = (scope_mod1 :: (env1.scope_mods));
        exported_ids = (env1.exported_ids);
        trans_exported_ids = (env1.trans_exported_ids);
        includes = (env1.includes);
        sigaccum = (env1.sigaccum);
        sigmap = (env1.sigmap);
        iface = (env1.iface);
        admitted_iface = (env1.admitted_iface);
        expect_typ = (env1.expect_typ);
        remaining_iface_decls = (env1.remaining_iface_decls);
        syntax_only = (env1.syntax_only);
        ds_hooks = (env1.ds_hooks);
        dep_graph = (env1.dep_graph)
      }
let (push_bv' :
  env -> FStarC_Ident.ident -> (env * FStarC_Syntax_Syntax.bv * used_marker))
  =
  fun env1 ->
    fun x ->
      let r = FStarC_Ident.range_of_id x in
      let bv =
        let uu___ = FStarC_Ident.string_of_id x in
        FStarC_Syntax_Syntax.gen_bv uu___ (FStar_Pervasives_Native.Some r)
          {
            FStarC_Syntax_Syntax.n =
              (FStarC_Syntax_Syntax.tun.FStarC_Syntax_Syntax.n);
            FStarC_Syntax_Syntax.pos = r;
            FStarC_Syntax_Syntax.vars =
              (FStarC_Syntax_Syntax.tun.FStarC_Syntax_Syntax.vars);
            FStarC_Syntax_Syntax.hash_code =
              (FStarC_Syntax_Syntax.tun.FStarC_Syntax_Syntax.hash_code)
          } in
      let used_marker1 = FStarC_Compiler_Util.mk_ref false in
      ((push_scope_mod env1 (Local_binding (x, bv, used_marker1))), bv,
        used_marker1)
let (push_bv : env -> FStarC_Ident.ident -> (env * FStarC_Syntax_Syntax.bv))
  =
  fun env1 ->
    fun x ->
      let uu___ = push_bv' env1 x in
      match uu___ with | (env2, bv, uu___1) -> (env2, bv)
let (push_top_level_rec_binding :
  env -> FStarC_Ident.ident -> (env * Prims.bool FStarC_Compiler_Effect.ref))
  =
  fun env0 ->
    fun x ->
      let l = qualify env0 x in
      let uu___ =
        (unique false true env0 l) || (FStarC_Options.interactive ()) in
      if uu___
      then
        let used_marker1 = FStarC_Compiler_Util.mk_ref false in
        ((push_scope_mod env0 (Rec_binding (x, l, used_marker1))),
          used_marker1)
      else
        (let uu___2 =
           let uu___3 = FStarC_Ident.string_of_lid l in
           Prims.strcat "Duplicate top-level names " uu___3 in
         FStarC_Errors.raise_error FStarC_Ident.hasrange_lident l
           FStarC_Errors_Codes.Fatal_DuplicateTopLevelNames ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_string)
           (Obj.magic uu___2))
let (push_sigelt' : Prims.bool -> env -> FStarC_Syntax_Syntax.sigelt -> env)
  =
  fun fail_on_dup ->
    fun env1 ->
      fun s ->
        let err l =
          let sopt =
            let uu___ = FStarC_Ident.string_of_lid l in
            FStarC_Compiler_Util.smap_try_find (sigmap env1) uu___ in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se, uu___) ->
                let uu___1 =
                  FStarC_Compiler_Util.find_opt (FStarC_Ident.lid_equals l)
                    (FStarC_Syntax_Util.lids_of_sigelt se) in
                (match uu___1 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu___2 = FStarC_Ident.range_of_lid l1 in
                     FStarC_Compiler_Range_Ops.string_of_range uu___2
                 | FStar_Pervasives_Native.None -> "<unknown>")
            | FStar_Pervasives_Native.None -> "<unknown>" in
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStarC_Ident.string_of_lid l in
                FStarC_Compiler_Util.format1 "Duplicate top-level names [%s]"
                  uu___3 in
              FStarC_Errors_Msg.text uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_Compiler_Util.format1 "Previously declared at %s" r in
                FStarC_Errors_Msg.text uu___4 in
              [uu___3] in
            uu___1 :: uu___2 in
          FStarC_Errors.raise_error FStarC_Ident.hasrange_lident l
            FStarC_Errors_Codes.Fatal_DuplicateTopLevelNames ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
            (Obj.magic uu___) in
        let globals = FStarC_Compiler_Util.mk_ref env1.scope_mods in
        let env2 =
          let uu___ =
            match s.FStarC_Syntax_Syntax.sigel with
            | FStarC_Syntax_Syntax.Sig_let uu___1 -> (false, true)
            | FStarC_Syntax_Syntax.Sig_bundle uu___1 -> (false, true)
            | uu___1 -> (false, false) in
          match uu___ with
          | (any_val, exclude_interface) ->
              let lids = FStarC_Syntax_Util.lids_of_sigelt s in
              let uu___1 =
                FStarC_Compiler_Util.find_map lids
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
                    {
                      curmodule = (env1.curmodule);
                      curmonad = (env1.curmonad);
                      modules = (env1.modules);
                      scope_mods = (env1.scope_mods);
                      exported_ids = (env1.exported_ids);
                      trans_exported_ids = (env1.trans_exported_ids);
                      includes = (env1.includes);
                      sigaccum = (s :: (env1.sigaccum));
                      sigmap = (env1.sigmap);
                      iface = (env1.iface);
                      admitted_iface = (env1.admitted_iface);
                      expect_typ = (env1.expect_typ);
                      remaining_iface_decls = (env1.remaining_iface_decls);
                      syntax_only = (env1.syntax_only);
                      ds_hooks = (env1.ds_hooks);
                      dep_graph = (env1.dep_graph)
                    })) in
        let env3 =
          let uu___ = FStarC_Compiler_Effect.op_Bang globals in
          {
            curmodule = (env2.curmodule);
            curmonad = (env2.curmonad);
            modules = (env2.modules);
            scope_mods = uu___;
            exported_ids = (env2.exported_ids);
            trans_exported_ids = (env2.trans_exported_ids);
            includes = (env2.includes);
            sigaccum = (env2.sigaccum);
            sigmap = (env2.sigmap);
            iface = (env2.iface);
            admitted_iface = (env2.admitted_iface);
            expect_typ = (env2.expect_typ);
            remaining_iface_decls = (env2.remaining_iface_decls);
            syntax_only = (env2.syntax_only);
            ds_hooks = (env2.ds_hooks);
            dep_graph = (env2.dep_graph)
          } in
        let uu___ =
          match s.FStarC_Syntax_Syntax.sigel with
          | FStarC_Syntax_Syntax.Sig_bundle
              { FStarC_Syntax_Syntax.ses = ses;
                FStarC_Syntax_Syntax.lids = uu___1;_}
              ->
              let uu___2 =
                FStarC_Compiler_List.map
                  (fun se -> ((FStarC_Syntax_Util.lids_of_sigelt se), se))
                  ses in
              (env3, uu___2)
          | uu___1 -> (env3, [((FStarC_Syntax_Util.lids_of_sigelt s), s)]) in
        match uu___ with
        | (env4, lss) ->
            (FStarC_Compiler_List.iter
               (fun uu___2 ->
                  match uu___2 with
                  | (lids, se) ->
                      FStarC_Compiler_List.iter
                        (fun lid ->
                           (let uu___4 =
                              let uu___5 =
                                let uu___6 = FStarC_Ident.ident_of_lid lid in
                                Top_level_def uu___6 in
                              let uu___6 =
                                FStarC_Compiler_Effect.op_Bang globals in
                              uu___5 :: uu___6 in
                            FStarC_Compiler_Effect.op_Colon_Equals globals
                              uu___4);
                           (match () with
                            | () ->
                                let modul =
                                  let uu___4 =
                                    let uu___5 = FStarC_Ident.ns_of_lid lid in
                                    FStarC_Ident.lid_of_ids uu___5 in
                                  FStarC_Ident.string_of_lid uu___4 in
                                ((let uu___5 = get_exported_id_set env4 modul in
                                  match uu___5 with
                                  | FStar_Pervasives_Native.Some f ->
                                      let my_exported_ids =
                                        f Exported_id_term_type in
                                      let uu___6 =
                                        let uu___7 =
                                          let uu___8 =
                                            FStarC_Ident.ident_of_lid lid in
                                          FStarC_Ident.string_of_id uu___8 in
                                        let uu___8 =
                                          FStarC_Compiler_Effect.op_Bang
                                            my_exported_ids in
                                        Obj.magic
                                          (FStarC_Class_Setlike.add ()
                                             (Obj.magic
                                                (FStarC_Compiler_RBSet.setlike_rbset
                                                   FStarC_Class_Ord.ord_string))
                                             uu___7 (Obj.magic uu___8)) in
                                      FStarC_Compiler_Effect.op_Colon_Equals
                                        my_exported_ids uu___6
                                  | FStar_Pervasives_Native.None -> ());
                                 (match () with
                                  | () ->
                                      let is_iface =
                                        env4.iface &&
                                          (Prims.op_Negation
                                             env4.admitted_iface) in
                                      let uu___5 =
                                        FStarC_Ident.string_of_lid lid in
                                      FStarC_Compiler_Util.smap_add
                                        (sigmap env4) uu___5
                                        (se,
                                          (env4.iface &&
                                             (Prims.op_Negation
                                                env4.admitted_iface)))))))
                        lids) lss;
             (let env5 =
                let uu___2 = FStarC_Compiler_Effect.op_Bang globals in
                {
                  curmodule = (env4.curmodule);
                  curmonad = (env4.curmonad);
                  modules = (env4.modules);
                  scope_mods = uu___2;
                  exported_ids = (env4.exported_ids);
                  trans_exported_ids = (env4.trans_exported_ids);
                  includes = (env4.includes);
                  sigaccum = (env4.sigaccum);
                  sigmap = (env4.sigmap);
                  iface = (env4.iface);
                  admitted_iface = (env4.admitted_iface);
                  expect_typ = (env4.expect_typ);
                  remaining_iface_decls = (env4.remaining_iface_decls);
                  syntax_only = (env4.syntax_only);
                  ds_hooks = (env4.ds_hooks);
                  dep_graph = (env4.dep_graph)
                } in
              env5))
let (push_sigelt : env -> FStarC_Syntax_Syntax.sigelt -> env) =
  fun env1 -> fun se -> push_sigelt' true env1 se
let (push_sigelt_force : env -> FStarC_Syntax_Syntax.sigelt -> env) =
  fun env1 -> fun se -> push_sigelt' false env1 se
let (find_data_constructors_for_typ :
  env ->
    FStarC_Ident.lident ->
      FStarC_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun lid ->
      let k_global_def lid1 uu___ =
        match uu___ with
        | ({
             FStarC_Syntax_Syntax.sigel =
               FStarC_Syntax_Syntax.Sig_inductive_typ
               { FStarC_Syntax_Syntax.lid = uu___1;
                 FStarC_Syntax_Syntax.us = uu___2;
                 FStarC_Syntax_Syntax.params = uu___3;
                 FStarC_Syntax_Syntax.num_uniform_params = uu___4;
                 FStarC_Syntax_Syntax.t = uu___5;
                 FStarC_Syntax_Syntax.mutuals = uu___6;
                 FStarC_Syntax_Syntax.ds = ds;
                 FStarC_Syntax_Syntax.injective_type_params = uu___7;_};
             FStarC_Syntax_Syntax.sigrng = uu___8;
             FStarC_Syntax_Syntax.sigquals = uu___9;
             FStarC_Syntax_Syntax.sigmeta = uu___10;
             FStarC_Syntax_Syntax.sigattrs = uu___11;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
             FStarC_Syntax_Syntax.sigopts = uu___13;_},
           uu___14) -> FStar_Pervasives_Native.Some ds
        | uu___1 -> FStar_Pervasives_Native.None in
      resolve_in_open_namespaces' env1 lid
        (fun uu___ -> FStar_Pervasives_Native.None)
        (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let (find_binders_for_datacons :
  env ->
    FStarC_Ident.lident ->
      FStarC_Ident.ident Prims.list FStar_Pervasives_Native.option)
  =
  let debug = FStarC_Compiler_Debug.get_toggle "open_include_restrictions" in
  fun env1 ->
    fun lid ->
      let ns = FStarC_Ident.ns_of_lid lid in
      let k_global_def lid1 uu___ =
        match uu___ with
        | ({
             FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
               { FStarC_Syntax_Syntax.lid1 = uu___1;
                 FStarC_Syntax_Syntax.us1 = uu___2;
                 FStarC_Syntax_Syntax.t1 = t;
                 FStarC_Syntax_Syntax.ty_lid = uu___3;
                 FStarC_Syntax_Syntax.num_ty_params = num_ty_params;
                 FStarC_Syntax_Syntax.mutuals1 = uu___4;
                 FStarC_Syntax_Syntax.injective_type_params1 = uu___5;_};
             FStarC_Syntax_Syntax.sigrng = uu___6;
             FStarC_Syntax_Syntax.sigquals = uu___7;
             FStarC_Syntax_Syntax.sigmeta = uu___8;
             FStarC_Syntax_Syntax.sigattrs = uu___9;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___10;
             FStarC_Syntax_Syntax.sigopts = uu___11;_},
           uu___12) ->
            let uu___13 =
              let uu___14 =
                let uu___15 =
                  let uu___16 =
                    let uu___17 = FStarC_Syntax_Util.arrow_formals_comp_ln t in
                    FStar_Pervasives_Native.fst uu___17 in
                  FStarC_Compiler_List.splitAt num_ty_params uu___16 in
                FStar_Pervasives_Native.snd uu___15 in
              FStarC_Compiler_List.map
                (fun x ->
                   (x.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname)
                uu___14 in
            FStar_Pervasives_Native.Some uu___13
        | uu___1 -> FStar_Pervasives_Native.None in
      let result =
        resolve_in_open_namespaces' env1 lid
          (fun uu___ -> FStar_Pervasives_Native.None)
          (fun uu___ -> FStar_Pervasives_Native.None) k_global_def in
      (let uu___1 = FStarC_Compiler_Effect.op_Bang debug in
       if uu___1
       then
         let uu___2 =
           let uu___3 =
             let uu___4 =
               FStarC_Class_Show.show FStarC_Ident.showable_lident lid in
             let uu___5 =
               let uu___6 =
                 FStarC_Class_Show.show
                   (FStarC_Class_Show.show_option
                      (FStarC_Class_Show.show_list
                         FStarC_Ident.showable_ident)) result in
               Prims.strcat ") = " uu___6 in
             Prims.strcat uu___4 uu___5 in
           Prims.strcat "find_binders_for_datacons(_, " uu___3 in
         FStarC_Compiler_Util.print_endline uu___2
       else ());
      result
let elab_restriction :
  'uuuuu .
    (env -> FStarC_Ident.lident -> FStarC_Syntax_Syntax.restriction -> 'uuuuu)
      ->
      env ->
        FStarC_Ident.lident -> FStarC_Syntax_Syntax.restriction -> 'uuuuu
  =
  fun f ->
    fun env1 ->
      fun ns ->
        fun restriction ->
          match restriction with
          | FStarC_Syntax_Syntax.Unrestricted -> f env1 ns restriction
          | FStarC_Syntax_Syntax.AllowList l ->
              let mk_lid id =
                let uu___ =
                  let uu___1 =
                    let uu___2 = FStarC_Ident.qual_id ns id in
                    FStarC_Ident.ids_of_lid uu___2 in
                  FStarC_Ident.lid_of_ids uu___1 in
                let uu___1 = FStarC_Ident.range_of_id id in
                FStarC_Ident.set_lid_range uu___ uu___1 in
              let name_exists id =
                let lid = mk_lid id in
                let uu___ = try_lookup_lid env1 lid in
                match uu___ with
                | FStar_Pervasives_Native.Some uu___1 -> true
                | FStar_Pervasives_Native.None ->
                    let uu___1 =
                      try_lookup_record_or_dc_by_field_name env1 lid in
                    FStarC_Compiler_Util.is_some uu___1 in
              let l1 =
                let uu___ =
                  let uu___1 =
                    FStarC_Compiler_List.map
                      (fun uu___2 ->
                         match uu___2 with
                         | (id, renamed) ->
                             let with_id_range =
                               let uu___3 =
                                 FStarC_Ident.range_of_id
                                   (FStarC_Compiler_Util.dflt id renamed) in
                               FStarC_Ident.set_id_range uu___3 in
                             let uu___3 =
                               let uu___4 = mk_lid id in
                               find_data_constructors_for_typ env1 uu___4 in
                             (match uu___3 with
                              | FStar_Pervasives_Native.Some idents ->
                                  FStarC_Compiler_List.map
                                    (fun id1 ->
                                       let uu___4 =
                                         let uu___5 =
                                           FStarC_Ident.ident_of_lid id1 in
                                         with_id_range uu___5 in
                                       (uu___4, FStar_Pervasives_Native.None))
                                    idents
                              | FStar_Pervasives_Native.None -> [])) l in
                  FStarC_Compiler_List.flatten uu___1 in
                FStarC_Compiler_List.append l uu___ in
              let l2 =
                let constructor_lid_to_desugared_record_lids =
                  let uu___ =
                    let uu___1 =
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_list () ()
                           (Obj.magic env1.modules)
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 let uu___2 = Obj.magic uu___2 in
                                 match uu___2 with
                                 | (uu___3,
                                    { FStarC_Syntax_Syntax.name = uu___4;
                                      FStarC_Syntax_Syntax.declarations =
                                        declarations;
                                      FStarC_Syntax_Syntax.is_interface =
                                        uu___5;_})
                                     ->
                                     Obj.magic
                                       (FStarC_Class_Monad.op_let_Bang
                                          FStarC_Class_Monad.monad_list () ()
                                          (Obj.magic declarations)
                                          (fun uu___6 ->
                                             (fun sigelt ->
                                                let sigelt = Obj.magic sigelt in
                                                Obj.magic
                                                  (FStarC_Class_Monad.op_let_Bang
                                                     FStarC_Class_Monad.monad_list
                                                     () ()
                                                     (match sigelt.FStarC_Syntax_Syntax.sigel
                                                      with
                                                      | FStarC_Syntax_Syntax.Sig_bundle
                                                          {
                                                            FStarC_Syntax_Syntax.ses
                                                              = ses;
                                                            FStarC_Syntax_Syntax.lids
                                                              = uu___6;_}
                                                          -> Obj.magic ses
                                                      | uu___6 ->
                                                          Obj.magic [])
                                                     (fun uu___6 ->
                                                        (fun sigelt1 ->
                                                           let sigelt1 =
                                                             Obj.magic
                                                               sigelt1 in
                                                           Obj.magic
                                                             (FStarC_Class_Monad.op_let_Bang
                                                                FStarC_Class_Monad.monad_list
                                                                () ()
                                                                (Obj.magic
                                                                   (FStarC_Syntax_Util.lids_of_sigelt
                                                                    sigelt1))
                                                                (fun uu___6
                                                                   ->
                                                                   (fun lid
                                                                    ->
                                                                    let lid =
                                                                    Obj.magic
                                                                    lid in
                                                                    let uu___6
                                                                    =
                                                                    FStarC_Syntax_Util.get_attribute
                                                                    FStarC_Parser_Const.desugar_of_variant_record_lid
                                                                    sigelt1.FStarC_Syntax_Syntax.sigattrs in
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (({
                                                                    FStarC_Syntax_Syntax.n
                                                                    =
                                                                    FStarC_Syntax_Syntax.Tm_constant
                                                                    (FStarC_Const.Const_string
                                                                    (s,
                                                                    uu___7));
                                                                    FStarC_Syntax_Syntax.pos
                                                                    = uu___8;
                                                                    FStarC_Syntax_Syntax.vars
                                                                    = uu___9;
                                                                    FStarC_Syntax_Syntax.hash_code
                                                                    = uu___10;_},
                                                                    FStar_Pervasives_Native.None)::[])
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Ident.lid_of_str
                                                                    s in
                                                                    (uu___12,
                                                                    lid) in
                                                                    Obj.magic
                                                                    [uu___11]
                                                                    | 
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    [])
                                                                    uu___6)))
                                                          uu___6))) uu___6)))
                                uu___2)) in
                    FStarC_Compiler_List.filter
                      (fun uu___2 ->
                         match uu___2 with
                         | (cons, lid) ->
                             (let uu___3 = FStarC_Ident.ns_of_lid cons in
                              let uu___4 = FStarC_Ident.ns_of_lid lid in
                              FStarC_Class_Deq.op_Equals_Question
                                (FStarC_Class_Ord.ord_eq
                                   (FStarC_Class_Ord.ord_list
                                      FStarC_Syntax_Syntax.ord_ident)) uu___3
                                uu___4)
                               &&
                               (let uu___3 = FStarC_Ident.ns_of_lid lid in
                                let uu___4 = FStarC_Ident.ids_of_lid ns in
                                FStarC_Class_Deq.op_Equals_Question
                                  (FStarC_Class_Ord.ord_eq
                                     (FStarC_Class_Ord.ord_list
                                        FStarC_Syntax_Syntax.ord_ident))
                                  uu___3 uu___4)) uu___1 in
                  FStarC_Compiler_List.map
                    (fun uu___1 ->
                       match uu___1 with
                       | (cons, lid) ->
                           let uu___2 = FStarC_Ident.ident_of_lid cons in
                           let uu___3 = FStarC_Ident.ident_of_lid lid in
                           (uu___2, uu___3)) uu___ in
                let uu___ =
                  let uu___1 =
                    FStarC_Compiler_List.filter
                      (fun uu___2 ->
                         match uu___2 with
                         | (cons, uu___3) ->
                             let uu___4 =
                               FStarC_Compiler_List.find
                                 (fun uu___5 ->
                                    match uu___5 with
                                    | (lid, uu___6) ->
                                        FStarC_Class_Deq.op_Equals_Question
                                          FStarC_Syntax_Syntax.deq_univ_name
                                          lid cons) l1 in
                             FStar_Pervasives_Native.uu___is_Some uu___4)
                      constructor_lid_to_desugared_record_lids in
                  FStarC_Compiler_List.map
                    (fun uu___2 ->
                       match uu___2 with
                       | (uu___3, lid) -> (lid, FStar_Pervasives_Native.None))
                    uu___1 in
                FStarC_Compiler_List.append l1 uu___ in
              let l3 =
                let uu___ =
                  let uu___1 =
                    FStarC_Compiler_List.map
                      (fun uu___2 ->
                         match uu___2 with
                         | (id, renamed) ->
                             let with_renamed_range =
                               let uu___3 =
                                 FStarC_Ident.range_of_id
                                   (FStarC_Compiler_Util.dflt id renamed) in
                               FStarC_Ident.set_id_range uu___3 in
                             let with_id_range =
                               let uu___3 =
                                 FStarC_Ident.range_of_id
                                   (FStarC_Compiler_Util.dflt id renamed) in
                               FStarC_Ident.set_id_range uu___3 in
                             let lid = mk_lid id in
                             let uu___3 =
                               let uu___4 =
                                 let uu___5 =
                                   let uu___6 =
                                     find_binders_for_datacons env1 lid in
                                   match uu___6 with
                                   | FStar_Pervasives_Native.None -> []
                                   | FStar_Pervasives_Native.Some l4 -> l4 in
                                 FStarC_Compiler_List.map
                                   (fun binder ->
                                      let uu___6 =
                                        let uu___7 =
                                          FStarC_Syntax_Util.mk_field_projector_name_from_ident
                                            lid binder in
                                        FStarC_Ident.ident_of_lid uu___7 in
                                      let uu___7 =
                                        FStarC_Compiler_Util.map_opt renamed
                                          (fun renamed1 ->
                                             let uu___8 =
                                               let uu___9 =
                                                 FStarC_Ident.lid_of_ids
                                                   [renamed1] in
                                               FStarC_Syntax_Util.mk_field_projector_name_from_ident
                                                 uu___9 binder in
                                             FStarC_Ident.ident_of_lid uu___8) in
                                      (uu___6, uu___7)) uu___5 in
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 =
                                     let uu___8 =
                                       let uu___9 =
                                         let uu___10 =
                                           let uu___11 =
                                             FStarC_Ident.lid_of_ids [id] in
                                           FStarC_Syntax_Util.mk_discriminator
                                             uu___11 in
                                         let uu___11 =
                                           FStarC_Compiler_Util.map_opt
                                             renamed
                                             (fun renamed1 ->
                                                let uu___12 =
                                                  FStarC_Ident.lid_of_ids
                                                    [renamed1] in
                                                FStarC_Syntax_Util.mk_discriminator
                                                  uu___12) in
                                         (uu___10, uu___11) in
                                       [uu___9] in
                                     FStarC_Compiler_List.map
                                       (fun uu___9 ->
                                          match uu___9 with
                                          | (x, y) ->
                                              let uu___10 =
                                                FStarC_Ident.ident_of_lid x in
                                              let uu___11 =
                                                FStarC_Compiler_Util.map_opt
                                                  y FStarC_Ident.ident_of_lid in
                                              (uu___10, uu___11)) uu___8 in
                                   FStarC_Compiler_List.filter
                                     (fun uu___8 ->
                                        match uu___8 with
                                        | (x, uu___9) -> name_exists x)
                                     uu___7 in
                                 let uu___7 =
                                   let uu___8 =
                                     try_lookup_record_type env1 lid in
                                   match uu___8 with
                                   | FStar_Pervasives_Native.Some
                                       { typename = uu___9; constrname;
                                         parms = uu___10; fields;
                                         is_private = uu___11;
                                         is_record = uu___12;_}
                                       ->
                                       FStarC_Compiler_List.map
                                         (fun uu___13 ->
                                            match uu___13 with
                                            | (id1, uu___14) ->
                                                (id1,
                                                  FStar_Pervasives_Native.None))
                                         fields
                                   | FStar_Pervasives_Native.None -> [] in
                                 FStarC_Compiler_List.op_At uu___6 uu___7 in
                               FStarC_Compiler_List.op_At uu___4 uu___5 in
                             FStarC_Compiler_List.map
                               (fun uu___4 ->
                                  match uu___4 with
                                  | (id1, renamed1) ->
                                      let uu___5 = with_id_range id1 in
                                      let uu___6 =
                                        FStarC_Compiler_Util.map_opt renamed1
                                          with_renamed_range in
                                      (uu___5, uu___6)) uu___3) l2 in
                  FStarC_Compiler_List.flatten uu___1 in
                FStarC_Compiler_List.append l2 uu___ in
              ((let final_idents =
                  FStarC_Compiler_List.mapi
                    (fun i ->
                       fun uu___ ->
                         match uu___ with
                         | (id, renamed) ->
                             ((FStarC_Compiler_Util.dflt id renamed), i)) l3 in
                let uu___ =
                  FStarC_Compiler_Util.find_dup
                    (fun uu___1 ->
                       fun uu___2 ->
                         match (uu___1, uu___2) with
                         | ((x, uu___3), (y, uu___4)) ->
                             FStarC_Class_Deq.op_Equals_Question
                               FStarC_Syntax_Syntax.deq_univ_name x y)
                    final_idents in
                match uu___ with
                | FStar_Pervasives_Native.Some (id, i) ->
                    let others =
                      FStarC_Compiler_List.filter
                        (fun uu___1 ->
                           match uu___1 with
                           | (id', i') ->
                               (FStarC_Class_Deq.op_Equals_Question
                                  FStarC_Syntax_Syntax.deq_univ_name id id')
                                 &&
                                 (let uu___2 =
                                    FStarC_Class_Deq.op_Equals_Question
                                      (FStarC_Class_Ord.ord_eq
                                         FStarC_Class_Ord.ord_int) i i' in
                                  Prims.op_Negation uu___2)) final_idents in
                    ((let uu___2 =
                        FStarC_Compiler_List.mapi
                          (fun nth ->
                             fun uu___3 ->
                               match uu___3 with
                               | (other, uu___4) ->
                                   let nth1 =
                                     match nth with
                                     | uu___5 when uu___5 = Prims.int_zero ->
                                         "first"
                                     | uu___5 when uu___5 = Prims.int_one ->
                                         "second"
                                     | uu___5 when
                                         uu___5 = (Prims.of_int (2)) ->
                                         "third"
                                     | nth2 ->
                                         let uu___5 =
                                           FStarC_Class_Show.show
                                             FStarC_Class_Show.showable_int
                                             (nth2 + Prims.int_one) in
                                         Prims.strcat uu___5 "th" in
                                   let uu___5 =
                                     let uu___6 =
                                       let uu___7 =
                                         let uu___8 =
                                           FStarC_Class_Show.show
                                             FStarC_Ident.showable_ident
                                             other in
                                         Prims.strcat uu___8
                                           (Prims.strcat " "
                                              (Prims.strcat nth1
                                                 " occurence comes from this declaration")) in
                                       FStarC_Errors_Msg.text uu___7 in
                                     [uu___6] in
                                   let uu___6 =
                                     let uu___7 =
                                       FStarC_Ident.range_of_id other in
                                     FStar_Pervasives_Native.Some uu___7 in
                                   {
                                     FStarC_Errors.issue_msg = uu___5;
                                     FStarC_Errors.issue_level =
                                       FStarC_Errors.EError;
                                     FStarC_Errors.issue_range = uu___6;
                                     FStarC_Errors.issue_number =
                                       FStar_Pervasives_Native.None;
                                     FStarC_Errors.issue_ctx = []
                                   }) others in
                      FStarC_Errors.add_issues uu___2);
                     (let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_int
                                ((FStarC_Compiler_List.length others) +
                                   Prims.int_one) in
                            Prims.strcat uu___5 " times" in
                          Prims.strcat "The name %s was imported " uu___4 in
                        let uu___4 = FStarC_Ident.string_of_id id in
                        FStarC_Compiler_Util.format1 uu___3 uu___4 in
                      FStarC_Errors.raise_error FStarC_Ident.hasrange_ident
                        id FStarC_Errors_Codes.Fatal_DuplicateTopLevelNames
                        ()
                        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                        (Obj.magic uu___2)))
                | FStar_Pervasives_Native.None -> ());
               FStarC_Compiler_List.iter
                 (fun uu___1 ->
                    match uu___1 with
                    | (id, _renamed) ->
                        let uu___2 =
                          let uu___3 = name_exists id in
                          Prims.op_Negation uu___3 in
                        if uu___2
                        then
                          let uu___3 =
                            let uu___4 =
                              let uu___5 = mk_lid id in
                              FStarC_Ident.string_of_lid uu___5 in
                            FStarC_Compiler_Util.format1
                              "Definition %s cannot be found" uu___4 in
                          FStarC_Errors.raise_error
                            FStarC_Ident.hasrange_ident id
                            FStarC_Errors_Codes.Fatal_NameNotFound ()
                            (Obj.magic
                               FStarC_Errors_Msg.is_error_message_string)
                            (Obj.magic uu___3)
                        else ()) l3;
               f env1 ns (FStarC_Syntax_Syntax.AllowList l3))
let (push_namespace' :
  env -> FStarC_Ident.lident -> FStarC_Syntax_Syntax.restriction -> env) =
  fun env1 ->
    fun ns ->
      fun restriction ->
        let uu___ =
          let uu___1 = resolve_module_name env1 ns false in
          match uu___1 with
          | FStar_Pervasives_Native.None ->
              let module_names =
                FStarC_Compiler_List.map FStar_Pervasives_Native.fst
                  env1.modules in
              let module_names1 =
                match env1.curmodule with
                | FStar_Pervasives_Native.None -> module_names
                | FStar_Pervasives_Native.Some l -> l :: module_names in
              let uu___2 =
                FStarC_Compiler_Util.for_some
                  (fun m ->
                     let uu___3 =
                       let uu___4 = FStarC_Ident.string_of_lid m in
                       Prims.strcat uu___4 "." in
                     let uu___4 =
                       let uu___5 = FStarC_Ident.string_of_lid ns in
                       Prims.strcat uu___5 "." in
                     FStarC_Compiler_Util.starts_with uu___3 uu___4)
                  module_names1 in
              if uu___2
              then (ns, FStarC_Syntax_Syntax.Open_namespace)
              else
                (let uu___4 =
                   let uu___5 = FStarC_Ident.string_of_lid ns in
                   FStarC_Compiler_Util.format1
                     "Namespace %s cannot be found" uu___5 in
                 FStarC_Errors.raise_error FStarC_Ident.hasrange_lident ns
                   FStarC_Errors_Codes.Fatal_NameSpaceNotFound ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                   (Obj.magic uu___4))
          | FStar_Pervasives_Native.Some ns' ->
              (ns', FStarC_Syntax_Syntax.Open_module) in
        match uu___ with
        | (ns', kd) ->
            ((env1.ds_hooks).ds_push_open_hook env1 (ns', kd, restriction);
             push_scope_mod env1
               (Open_module_or_namespace (ns', kd, restriction)))
let (push_include' :
  env -> FStarC_Ident.lident -> FStarC_Syntax_Syntax.restriction -> env) =
  fun env1 ->
    fun ns ->
      fun restriction ->
        let ns0 = ns in
        let uu___ = resolve_module_name env1 ns false in
        match uu___ with
        | FStar_Pervasives_Native.Some ns1 ->
            ((env1.ds_hooks).ds_push_include_hook env1 ns1;
             (let env2 =
                push_scope_mod env1
                  (Open_module_or_namespace
                     (ns1, FStarC_Syntax_Syntax.Open_module, restriction)) in
              let curmod =
                let uu___2 = current_module env2 in
                FStarC_Ident.string_of_lid uu___2 in
              (let uu___3 =
                 FStarC_Compiler_Util.smap_try_find env2.includes curmod in
               match uu___3 with
               | FStar_Pervasives_Native.None -> ()
               | FStar_Pervasives_Native.Some incl ->
                   let uu___4 =
                     let uu___5 = FStarC_Compiler_Effect.op_Bang incl in
                     (ns1, restriction) :: uu___5 in
                   FStarC_Compiler_Effect.op_Colon_Equals incl uu___4);
              (match () with
               | () ->
                   let uu___3 =
                     let uu___4 = FStarC_Ident.string_of_lid ns1 in
                     get_trans_exported_id_set env2 uu___4 in
                   (match uu___3 with
                    | FStar_Pervasives_Native.Some ns_trans_exports ->
                        ((let uu___5 =
                            let uu___6 = get_exported_id_set env2 curmod in
                            let uu___7 =
                              get_trans_exported_id_set env2 curmod in
                            (uu___6, uu___7) in
                          match uu___5 with
                          | (FStar_Pervasives_Native.Some cur_exports,
                             FStar_Pervasives_Native.Some cur_trans_exports)
                              ->
                              let update_exports k =
                                let ns_ex =
                                  let uu___6 =
                                    let uu___7 = ns_trans_exports k in
                                    FStarC_Compiler_Effect.op_Bang uu___7 in
                                  Obj.magic
                                    (FStarC_Class_Setlike.filter ()
                                       (Obj.magic
                                          (FStarC_Compiler_RBSet.setlike_rbset
                                             FStarC_Class_Ord.ord_string))
                                       (fun id ->
                                          let uu___7 =
                                            let uu___8 =
                                              FStarC_Ident.id_of_text id in
                                            FStarC_Syntax_Syntax.is_ident_allowed_by_restriction
                                              uu___8 restriction in
                                          FStarC_Compiler_Util.is_some uu___7)
                                       (Obj.magic uu___6)) in
                                let ex = cur_exports k in
                                (let uu___7 =
                                   let uu___8 =
                                     FStarC_Compiler_Effect.op_Bang ex in
                                   Obj.magic
                                     (FStarC_Class_Setlike.diff ()
                                        (Obj.magic
                                           (FStarC_Compiler_RBSet.setlike_rbset
                                              FStarC_Class_Ord.ord_string))
                                        (Obj.magic uu___8) (Obj.magic ns_ex)) in
                                 FStarC_Compiler_Effect.op_Colon_Equals ex
                                   uu___7);
                                (match () with
                                 | () ->
                                     let trans_ex = cur_trans_exports k in
                                     let uu___8 =
                                       let uu___9 =
                                         FStarC_Compiler_Effect.op_Bang
                                           trans_ex in
                                       Obj.magic
                                         (FStarC_Class_Setlike.union ()
                                            (Obj.magic
                                               (FStarC_Compiler_RBSet.setlike_rbset
                                                  FStarC_Class_Ord.ord_string))
                                            (Obj.magic uu___9)
                                            (Obj.magic ns_ex)) in
                                     FStarC_Compiler_Effect.op_Colon_Equals
                                       trans_ex uu___8) in
                              FStarC_Compiler_List.iter update_exports
                                all_exported_id_kinds
                          | uu___6 -> ());
                         (match () with | () -> env2))
                    | FStar_Pervasives_Native.None ->
                        let uu___4 =
                          let uu___5 = FStarC_Ident.string_of_lid ns1 in
                          FStarC_Compiler_Util.format1
                            "include: Module %s was not prepared" uu___5 in
                        FStarC_Errors.raise_error
                          FStarC_Ident.hasrange_lident ns1
                          FStarC_Errors_Codes.Fatal_IncludeModuleNotPrepared
                          ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_string)
                          (Obj.magic uu___4)))))
        | uu___1 ->
            let uu___2 =
              let uu___3 = FStarC_Ident.string_of_lid ns in
              FStarC_Compiler_Util.format1
                "include: Module %s cannot be found" uu___3 in
            FStarC_Errors.raise_error FStarC_Ident.hasrange_lident ns
              FStarC_Errors_Codes.Fatal_ModuleNotFound ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___2)
let (push_namespace :
  env -> FStarC_Ident.lident -> FStarC_Syntax_Syntax.restriction -> env) =
  elab_restriction push_namespace'
let (push_include :
  env -> FStarC_Ident.lident -> FStarC_Syntax_Syntax.restriction -> env) =
  elab_restriction push_include'
let (push_module_abbrev :
  env -> FStarC_Ident.ident -> FStarC_Ident.lident -> env) =
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
             let uu___3 = FStarC_Ident.string_of_lid l in
             FStarC_Compiler_Util.format1 "Module %s cannot be found" uu___3 in
           FStarC_Errors.raise_error FStarC_Ident.hasrange_lident l
             FStarC_Errors_Codes.Fatal_ModuleNotFound ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_string)
             (Obj.magic uu___2))
let (check_admits :
  env -> FStarC_Syntax_Syntax.modul -> FStarC_Syntax_Syntax.modul) =
  fun env1 ->
    fun m ->
      let admitted_sig_lids =
        FStarC_Compiler_List.fold_left
          (fun lids ->
             fun se ->
               match se.FStarC_Syntax_Syntax.sigel with
               | FStarC_Syntax_Syntax.Sig_declare_typ
                   { FStarC_Syntax_Syntax.lid2 = l;
                     FStarC_Syntax_Syntax.us2 = u;
                     FStarC_Syntax_Syntax.t2 = t;_}
                   when
                   Prims.op_Negation
                     (FStarC_Compiler_List.contains
                        FStarC_Syntax_Syntax.Assumption
                        se.FStarC_Syntax_Syntax.sigquals)
                   ->
                   let uu___ =
                     let uu___1 = FStarC_Ident.string_of_lid l in
                     FStarC_Compiler_Util.smap_try_find (sigmap env1) uu___1 in
                   (match uu___ with
                    | FStar_Pervasives_Native.Some
                        ({
                           FStarC_Syntax_Syntax.sigel =
                             FStarC_Syntax_Syntax.Sig_let uu___1;
                           FStarC_Syntax_Syntax.sigrng = uu___2;
                           FStarC_Syntax_Syntax.sigquals = uu___3;
                           FStarC_Syntax_Syntax.sigmeta = uu___4;
                           FStarC_Syntax_Syntax.sigattrs = uu___5;
                           FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
                           FStarC_Syntax_Syntax.sigopts = uu___7;_},
                         uu___8)
                        -> lids
                    | FStar_Pervasives_Native.Some
                        ({
                           FStarC_Syntax_Syntax.sigel =
                             FStarC_Syntax_Syntax.Sig_inductive_typ uu___1;
                           FStarC_Syntax_Syntax.sigrng = uu___2;
                           FStarC_Syntax_Syntax.sigquals = uu___3;
                           FStarC_Syntax_Syntax.sigmeta = uu___4;
                           FStarC_Syntax_Syntax.sigattrs = uu___5;
                           FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
                           FStarC_Syntax_Syntax.sigopts = uu___7;_},
                         uu___8)
                        -> lids
                    | FStar_Pervasives_Native.Some
                        ({
                           FStarC_Syntax_Syntax.sigel =
                             FStarC_Syntax_Syntax.Sig_splice uu___1;
                           FStarC_Syntax_Syntax.sigrng = uu___2;
                           FStarC_Syntax_Syntax.sigquals = uu___3;
                           FStarC_Syntax_Syntax.sigmeta = uu___4;
                           FStarC_Syntax_Syntax.sigattrs = uu___5;
                           FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
                           FStarC_Syntax_Syntax.sigopts = uu___7;_},
                         uu___8)
                        -> lids
                    | uu___1 ->
                        ((let uu___3 =
                            let uu___4 = FStarC_Options.interactive () in
                            Prims.op_Negation uu___4 in
                          if uu___3
                          then
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 =
                                    FStarC_Class_Show.show
                                      FStarC_Ident.showable_lident l in
                                  FStarC_Pprint.doc_of_string uu___7 in
                                let uu___7 =
                                  FStarC_Errors_Msg.text
                                    "is declared but no definition was found" in
                                FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                              let uu___6 =
                                let uu___7 =
                                  FStarC_Errors_Msg.text
                                    "Add an 'assume' if this is intentional" in
                                [uu___7] in
                              uu___5 :: uu___6 in
                            FStarC_Errors.log_issue
                              FStarC_Ident.hasrange_lident l
                              FStarC_Errors_Codes.Error_AdmitWithoutDefinition
                              ()
                              (Obj.magic
                                 FStarC_Errors_Msg.is_error_message_list_doc)
                              (Obj.magic uu___4)
                          else ());
                         (let quals = FStarC_Syntax_Syntax.Assumption ::
                            (se.FStarC_Syntax_Syntax.sigquals) in
                          (let uu___4 = FStarC_Ident.string_of_lid l in
                           FStarC_Compiler_Util.smap_add (sigmap env1) uu___4
                             ({
                                FStarC_Syntax_Syntax.sigel =
                                  (se.FStarC_Syntax_Syntax.sigel);
                                FStarC_Syntax_Syntax.sigrng =
                                  (se.FStarC_Syntax_Syntax.sigrng);
                                FStarC_Syntax_Syntax.sigquals = quals;
                                FStarC_Syntax_Syntax.sigmeta =
                                  (se.FStarC_Syntax_Syntax.sigmeta);
                                FStarC_Syntax_Syntax.sigattrs =
                                  (se.FStarC_Syntax_Syntax.sigattrs);
                                FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                  (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                FStarC_Syntax_Syntax.sigopts =
                                  (se.FStarC_Syntax_Syntax.sigopts)
                              }, false));
                          l
                          ::
                          lids)))
               | uu___ -> lids) [] env1.sigaccum in
      m
let (finish : env -> FStarC_Syntax_Syntax.modul -> env) =
  fun env1 ->
    fun modul ->
      FStarC_Compiler_List.iter
        (fun se ->
           let quals = se.FStarC_Syntax_Syntax.sigquals in
           match se.FStarC_Syntax_Syntax.sigel with
           | FStarC_Syntax_Syntax.Sig_bundle
               { FStarC_Syntax_Syntax.ses = ses;
                 FStarC_Syntax_Syntax.lids = uu___1;_}
               ->
               if
                 FStarC_Compiler_List.contains FStarC_Syntax_Syntax.Private
                   quals
               then
                 FStarC_Compiler_List.iter
                   (fun se1 ->
                      match se1.FStarC_Syntax_Syntax.sigel with
                      | FStarC_Syntax_Syntax.Sig_datacon
                          { FStarC_Syntax_Syntax.lid1 = lid;
                            FStarC_Syntax_Syntax.us1 = uu___2;
                            FStarC_Syntax_Syntax.t1 = uu___3;
                            FStarC_Syntax_Syntax.ty_lid = uu___4;
                            FStarC_Syntax_Syntax.num_ty_params = uu___5;
                            FStarC_Syntax_Syntax.mutuals1 = uu___6;
                            FStarC_Syntax_Syntax.injective_type_params1 =
                              uu___7;_}
                          ->
                          let uu___8 = FStarC_Ident.string_of_lid lid in
                          FStarC_Compiler_Util.smap_remove (sigmap env1)
                            uu___8
                      | FStarC_Syntax_Syntax.Sig_inductive_typ
                          { FStarC_Syntax_Syntax.lid = lid;
                            FStarC_Syntax_Syntax.us = univ_names;
                            FStarC_Syntax_Syntax.params = binders;
                            FStarC_Syntax_Syntax.num_uniform_params = uu___2;
                            FStarC_Syntax_Syntax.t = typ;
                            FStarC_Syntax_Syntax.mutuals = uu___3;
                            FStarC_Syntax_Syntax.ds = uu___4;
                            FStarC_Syntax_Syntax.injective_type_params =
                              uu___5;_}
                          ->
                          ((let uu___7 = FStarC_Ident.string_of_lid lid in
                            FStarC_Compiler_Util.smap_remove (sigmap env1)
                              uu___7);
                           if
                             Prims.op_Negation
                               (FStarC_Compiler_List.contains
                                  FStarC_Syntax_Syntax.Private quals)
                           then
                             (let sigel =
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        let uu___11 =
                                          FStarC_Syntax_Syntax.mk_Total typ in
                                        {
                                          FStarC_Syntax_Syntax.bs1 = binders;
                                          FStarC_Syntax_Syntax.comp = uu___11
                                        } in
                                      FStarC_Syntax_Syntax.Tm_arrow uu___10 in
                                    let uu___10 =
                                      FStarC_Ident.range_of_lid lid in
                                    FStarC_Syntax_Syntax.mk uu___9 uu___10 in
                                  {
                                    FStarC_Syntax_Syntax.lid2 = lid;
                                    FStarC_Syntax_Syntax.us2 = univ_names;
                                    FStarC_Syntax_Syntax.t2 = uu___8
                                  } in
                                FStarC_Syntax_Syntax.Sig_declare_typ uu___7 in
                              let se2 =
                                {
                                  FStarC_Syntax_Syntax.sigel = sigel;
                                  FStarC_Syntax_Syntax.sigrng =
                                    (se1.FStarC_Syntax_Syntax.sigrng);
                                  FStarC_Syntax_Syntax.sigquals =
                                    (FStarC_Syntax_Syntax.Assumption ::
                                    quals);
                                  FStarC_Syntax_Syntax.sigmeta =
                                    (se1.FStarC_Syntax_Syntax.sigmeta);
                                  FStarC_Syntax_Syntax.sigattrs =
                                    (se1.FStarC_Syntax_Syntax.sigattrs);
                                  FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                    (se1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                  FStarC_Syntax_Syntax.sigopts =
                                    (se1.FStarC_Syntax_Syntax.sigopts)
                                } in
                              let uu___7 = FStarC_Ident.string_of_lid lid in
                              FStarC_Compiler_Util.smap_add (sigmap env1)
                                uu___7 (se2, false))
                           else ())
                      | uu___2 -> ()) ses
               else ()
           | FStarC_Syntax_Syntax.Sig_declare_typ
               { FStarC_Syntax_Syntax.lid2 = lid;
                 FStarC_Syntax_Syntax.us2 = uu___1;
                 FStarC_Syntax_Syntax.t2 = uu___2;_}
               ->
               if
                 FStarC_Compiler_List.contains FStarC_Syntax_Syntax.Private
                   quals
               then
                 let uu___3 = FStarC_Ident.string_of_lid lid in
                 FStarC_Compiler_Util.smap_remove (sigmap env1) uu___3
               else ()
           | FStarC_Syntax_Syntax.Sig_let
               { FStarC_Syntax_Syntax.lbs1 = (uu___1, lbs);
                 FStarC_Syntax_Syntax.lids1 = uu___2;_}
               ->
               if
                 FStarC_Compiler_List.contains FStarC_Syntax_Syntax.Private
                   quals
               then
                 FStarC_Compiler_List.iter
                   (fun lb ->
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStarC_Compiler_Util.right
                                lb.FStarC_Syntax_Syntax.lbname in
                            uu___6.FStarC_Syntax_Syntax.fv_name in
                          uu___5.FStarC_Syntax_Syntax.v in
                        FStarC_Ident.string_of_lid uu___4 in
                      FStarC_Compiler_Util.smap_remove (sigmap env1) uu___3)
                   lbs
               else ()
           | uu___1 -> ()) modul.FStarC_Syntax_Syntax.declarations;
      (let curmod =
         let uu___1 = current_module env1 in
         FStarC_Ident.string_of_lid uu___1 in
       (let uu___2 =
          let uu___3 = get_exported_id_set env1 curmod in
          let uu___4 = get_trans_exported_id_set env1 curmod in
          (uu___3, uu___4) in
        match uu___2 with
        | (FStar_Pervasives_Native.Some cur_ex, FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu___3 = cur_ex eikind in
                FStarC_Compiler_Effect.op_Bang uu___3 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu___3 =
                let uu___4 =
                  FStarC_Compiler_Effect.op_Bang cur_trans_ex_set_ref in
                Obj.magic
                  (FStarC_Class_Setlike.union ()
                     (Obj.magic
                        (FStarC_Compiler_RBSet.setlike_rbset
                           FStarC_Class_Ord.ord_string))
                     (Obj.magic cur_ex_set) (Obj.magic uu___4)) in
              FStarC_Compiler_Effect.op_Colon_Equals cur_trans_ex_set_ref
                uu___3 in
            FStarC_Compiler_List.iter update_exports all_exported_id_kinds
        | uu___3 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (env1.curmonad);
                    modules = (((modul.FStarC_Syntax_Syntax.name), modul) ::
                      (env1.modules));
                    scope_mods = [];
                    exported_ids = (env1.exported_ids);
                    trans_exported_ids = (env1.trans_exported_ids);
                    includes = (env1.includes);
                    sigaccum = [];
                    sigmap = (env1.sigmap);
                    iface = (env1.iface);
                    admitted_iface = (env1.admitted_iface);
                    expect_typ = (env1.expect_typ);
                    remaining_iface_decls = (env1.remaining_iface_decls);
                    syntax_only = (env1.syntax_only);
                    ds_hooks = (env1.ds_hooks);
                    dep_graph = (env1.dep_graph)
                  }))))
let (stack : env Prims.list FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref []
let (push : env -> env) =
  fun env1 ->
    FStarC_Compiler_Util.atomically
      (fun uu___ ->
         push_record_cache ();
         (let uu___3 =
            let uu___4 = FStarC_Compiler_Effect.op_Bang stack in env1 ::
              uu___4 in
          FStarC_Compiler_Effect.op_Colon_Equals stack uu___3);
         (let uu___3 = FStarC_Compiler_Util.smap_copy env1.exported_ids in
          let uu___4 = FStarC_Compiler_Util.smap_copy env1.trans_exported_ids in
          let uu___5 = FStarC_Compiler_Util.smap_copy env1.includes in
          let uu___6 = FStarC_Compiler_Util.smap_copy env1.sigmap in
          {
            curmodule = (env1.curmodule);
            curmonad = (env1.curmonad);
            modules = (env1.modules);
            scope_mods = (env1.scope_mods);
            exported_ids = uu___3;
            trans_exported_ids = uu___4;
            includes = uu___5;
            sigaccum = (env1.sigaccum);
            sigmap = uu___6;
            iface = (env1.iface);
            admitted_iface = (env1.admitted_iface);
            expect_typ = (env1.expect_typ);
            remaining_iface_decls = (env1.remaining_iface_decls);
            syntax_only = (env1.syntax_only);
            ds_hooks = (env1.ds_hooks);
            dep_graph = (env1.dep_graph)
          }))
let (pop : unit -> env) =
  fun uu___ ->
    FStarC_Compiler_Util.atomically
      (fun uu___1 ->
         let uu___2 = FStarC_Compiler_Effect.op_Bang stack in
         match uu___2 with
         | env1::tl ->
             (pop_record_cache ();
              FStarC_Compiler_Effect.op_Colon_Equals stack tl;
              env1)
         | uu___3 -> failwith "Impossible: Too many pops")
let (snapshot : env -> (Prims.int * env)) =
  fun env1 -> FStarC_Common.snapshot push stack env1
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth -> FStarC_Common.rollback pop stack depth
let (export_interface : FStarC_Ident.lident -> env -> env) =
  fun m ->
    fun env1 ->
      let sigelt_in_m se =
        match FStarC_Syntax_Util.lids_of_sigelt se with
        | l::uu___ ->
            let uu___1 = FStarC_Ident.nsstr l in
            let uu___2 = FStarC_Ident.string_of_lid m in uu___1 = uu___2
        | uu___ -> false in
      let sm = sigmap env1 in
      let env2 = pop () in
      let keys = FStarC_Compiler_Util.smap_keys sm in
      let sm' = sigmap env2 in
      FStarC_Compiler_List.iter
        (fun k ->
           let uu___1 = FStarC_Compiler_Util.smap_try_find sm' k in
           match uu___1 with
           | FStar_Pervasives_Native.Some (se, true) when sigelt_in_m se ->
               (FStarC_Compiler_Util.smap_remove sm' k;
                (let se1 =
                   match se.FStarC_Syntax_Syntax.sigel with
                   | FStarC_Syntax_Syntax.Sig_declare_typ
                       { FStarC_Syntax_Syntax.lid2 = l;
                         FStarC_Syntax_Syntax.us2 = u;
                         FStarC_Syntax_Syntax.t2 = t;_}
                       ->
                       {
                         FStarC_Syntax_Syntax.sigel =
                           (se.FStarC_Syntax_Syntax.sigel);
                         FStarC_Syntax_Syntax.sigrng =
                           (se.FStarC_Syntax_Syntax.sigrng);
                         FStarC_Syntax_Syntax.sigquals =
                           (FStarC_Syntax_Syntax.Assumption ::
                           (se.FStarC_Syntax_Syntax.sigquals));
                         FStarC_Syntax_Syntax.sigmeta =
                           (se.FStarC_Syntax_Syntax.sigmeta);
                         FStarC_Syntax_Syntax.sigattrs =
                           (se.FStarC_Syntax_Syntax.sigattrs);
                         FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                           (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                         FStarC_Syntax_Syntax.sigopts =
                           (se.FStarC_Syntax_Syntax.sigopts)
                       }
                   | uu___3 -> se in
                 FStarC_Compiler_Util.smap_add sm' k (se1, false)))
           | uu___2 -> ()) keys;
      env2
let (finish_module_or_interface :
  env -> FStarC_Syntax_Syntax.modul -> (env * FStarC_Syntax_Syntax.modul)) =
  fun env1 ->
    fun modul ->
      let modul1 =
        if Prims.op_Negation modul.FStarC_Syntax_Syntax.is_interface
        then check_admits env1 modul
        else modul in
      let uu___ = finish env1 modul1 in (uu___, modul1)
type exported_ids =
  {
  exported_id_terms: string_set ;
  exported_id_fields: string_set }
let (__proj__Mkexported_ids__item__exported_id_terms :
  exported_ids -> string_set) =
  fun projectee ->
    match projectee with
    | { exported_id_terms; exported_id_fields;_} -> exported_id_terms
let (__proj__Mkexported_ids__item__exported_id_fields :
  exported_ids -> string_set) =
  fun projectee ->
    match projectee with
    | { exported_id_terms; exported_id_fields;_} -> exported_id_fields
let (as_exported_ids : exported_id_set -> exported_ids) =
  fun e ->
    let terms =
      let uu___ = e Exported_id_term_type in
      FStarC_Compiler_Effect.op_Bang uu___ in
    let fields =
      let uu___ = e Exported_id_field in FStarC_Compiler_Effect.op_Bang uu___ in
    { exported_id_terms = terms; exported_id_fields = fields }
let (as_exported_id_set :
  exported_ids FStar_Pervasives_Native.option ->
    exported_id_kind -> string_set FStarC_Compiler_Effect.ref)
  =
  fun e ->
    match e with
    | FStar_Pervasives_Native.None -> exported_id_set_new ()
    | FStar_Pervasives_Native.Some e1 ->
        let terms = FStarC_Compiler_Util.mk_ref e1.exported_id_terms in
        let fields = FStarC_Compiler_Util.mk_ref e1.exported_id_fields in
        (fun uu___ ->
           match uu___ with
           | Exported_id_term_type -> terms
           | Exported_id_field -> fields)
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_includes:
    (FStarC_Ident.lident * FStarC_Syntax_Syntax.restriction) Prims.list
      FStar_Pervasives_Native.option
    }
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
    (FStarC_Ident.lident * FStarC_Syntax_Syntax.restriction) Prims.list
      FStar_Pervasives_Native.option)
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
      'uuuuu Prims.list FStarC_Compiler_Effect.ref
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> FStarC_Compiler_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStarC_Compiler_Util.mk_ref l
let (inclusion_info : env -> FStarC_Ident.lident -> module_inclusion_info) =
  fun env1 ->
    fun l ->
      let mname = FStarC_Ident.string_of_lid l in
      let as_ids_opt m =
        let uu___ = FStarC_Compiler_Util.smap_try_find m mname in
        FStarC_Compiler_Util.map_opt uu___ as_exported_ids in
      let uu___ = as_ids_opt env1.exported_ids in
      let uu___1 = as_ids_opt env1.trans_exported_ids in
      let uu___2 =
        let uu___3 = FStarC_Compiler_Util.smap_try_find env1.includes mname in
        FStarC_Compiler_Util.map_opt uu___3
          (fun r -> FStarC_Compiler_Effect.op_Bang r) in
      {
        mii_exported_ids = uu___;
        mii_trans_exported_ids = uu___1;
        mii_includes = uu___2
      }
let (prepare_module_or_interface :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStarC_Ident.lident -> module_inclusion_info -> (env * Prims.bool))
  =
  fun intf ->
    fun admitted ->
      fun env1 ->
        fun mname ->
          fun mii ->
            let prep env2 =
              let filename =
                let uu___ = FStarC_Ident.string_of_lid mname in
                FStarC_Compiler_Util.strcat uu___ ".fst" in
              let auto_open =
                FStarC_Parser_Dep.hard_coded_dependencies filename in
              let auto_open1 =
                let convert_kind uu___ =
                  match uu___ with
                  | FStarC_Parser_Dep.Open_namespace ->
                      FStarC_Syntax_Syntax.Open_namespace
                  | FStarC_Parser_Dep.Open_module ->
                      FStarC_Syntax_Syntax.Open_module in
                FStarC_Compiler_List.map
                  (fun uu___ ->
                     match uu___ with
                     | (lid, kind) ->
                         (lid, (convert_kind kind),
                           FStarC_Syntax_Syntax.Unrestricted)) auto_open in
              let namespace_of_module =
                let uu___ =
                  let uu___1 =
                    let uu___2 = FStarC_Ident.ns_of_lid mname in
                    FStarC_Compiler_List.length uu___2 in
                  uu___1 > Prims.int_zero in
                if uu___
                then
                  let uu___1 =
                    let uu___2 =
                      let uu___3 = FStarC_Ident.ns_of_lid mname in
                      FStarC_Ident.lid_of_ids uu___3 in
                    (uu___2, FStarC_Syntax_Syntax.Open_namespace,
                      FStarC_Syntax_Syntax.Unrestricted) in
                  [uu___1]
                else [] in
              let auto_open2 =
                FStarC_Compiler_List.op_At namespace_of_module
                  (FStarC_Compiler_List.rev auto_open1) in
              (let uu___1 = FStarC_Ident.string_of_lid mname in
               let uu___2 = as_exported_id_set mii.mii_exported_ids in
               FStarC_Compiler_Util.smap_add env2.exported_ids uu___1 uu___2);
              (match () with
               | () ->
                   ((let uu___2 = FStarC_Ident.string_of_lid mname in
                     let uu___3 =
                       as_exported_id_set mii.mii_trans_exported_ids in
                     FStarC_Compiler_Util.smap_add env2.trans_exported_ids
                       uu___2 uu___3);
                    (match () with
                     | () ->
                         ((let uu___3 = FStarC_Ident.string_of_lid mname in
                           let uu___4 = as_includes mii.mii_includes in
                           FStarC_Compiler_Util.smap_add env2.includes uu___3
                             uu___4);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___3 =
                                   FStarC_Compiler_List.map
                                     (fun x -> Open_module_or_namespace x)
                                     auto_open2 in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (env2.curmonad);
                                   modules = (env2.modules);
                                   scope_mods = uu___3;
                                   exported_ids = (env2.exported_ids);
                                   trans_exported_ids =
                                     (env2.trans_exported_ids);
                                   includes = (env2.includes);
                                   sigaccum = (env2.sigaccum);
                                   sigmap = (env2.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (env2.expect_typ);
                                   remaining_iface_decls =
                                     (env2.remaining_iface_decls);
                                   syntax_only = (env2.syntax_only);
                                   ds_hooks = (env2.ds_hooks);
                                   dep_graph = (env2.dep_graph)
                                 } in
                               (FStarC_Compiler_List.iter
                                  (fun op ->
                                     (env2.ds_hooks).ds_push_open_hook env'
                                       op)
                                  (FStarC_Compiler_List.rev auto_open2);
                                env')))))) in
            let uu___ =
              FStarC_Compiler_Util.find_opt
                (fun uu___1 ->
                   match uu___1 with
                   | (l, uu___2) -> FStarC_Ident.lid_equals l mname)
                env1.modules in
            match uu___ with
            | FStar_Pervasives_Native.None ->
                let uu___1 = prep env1 in (uu___1, false)
            | FStar_Pervasives_Native.Some (uu___1, m) ->
                ((let uu___3 =
                    (let uu___4 = FStarC_Options.interactive () in
                     Prims.op_Negation uu___4) &&
                      ((Prims.op_Negation m.FStarC_Syntax_Syntax.is_interface)
                         || intf) in
                  if uu___3
                  then
                    let uu___4 =
                      let uu___5 = FStarC_Ident.string_of_lid mname in
                      FStarC_Compiler_Util.format1
                        "Duplicate module or interface name: %s" uu___5 in
                    FStarC_Errors.raise_error FStarC_Ident.hasrange_lident
                      mname
                      FStarC_Errors_Codes.Fatal_DuplicateModuleOrInterface ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                      (Obj.magic uu___4)
                  else ());
                 (let uu___3 = let uu___4 = push env1 in prep uu___4 in
                  (uu___3, true)))
let (enter_monad_scope : env -> FStarC_Ident.ident -> env) =
  fun env1 ->
    fun mname ->
      match env1.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_Class_Show.show FStarC_Ident.showable_ident mname in
              let uu___3 =
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Ident.showable_ident mname' in
                Prims.strcat ", but already in monad scope " uu___4 in
              Prims.strcat uu___2 uu___3 in
            Prims.strcat "Trying to define monad " uu___1 in
          FStarC_Errors.raise_error FStarC_Ident.hasrange_ident mname
            FStarC_Errors_Codes.Fatal_MonadAlreadyDefined ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___)
      | FStar_Pervasives_Native.None ->
          {
            curmodule = (env1.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (env1.modules);
            scope_mods = (env1.scope_mods);
            exported_ids = (env1.exported_ids);
            trans_exported_ids = (env1.trans_exported_ids);
            includes = (env1.includes);
            sigaccum = (env1.sigaccum);
            sigmap = (env1.sigmap);
            iface = (env1.iface);
            admitted_iface = (env1.admitted_iface);
            expect_typ = (env1.expect_typ);
            remaining_iface_decls = (env1.remaining_iface_decls);
            syntax_only = (env1.syntax_only);
            ds_hooks = (env1.ds_hooks);
            dep_graph = (env1.dep_graph)
          }
let fail_or :
  'a .
    env ->
      (FStarC_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStarC_Ident.lident -> 'a
  =
  fun env1 ->
    fun lookup ->
      fun lid ->
        let uu___ = lookup lid in
        match uu___ with
        | FStar_Pervasives_Native.Some r -> r
        | FStar_Pervasives_Native.None ->
            let opened_modules =
              FStarC_Compiler_List.map
                (fun uu___1 ->
                   match uu___1 with
                   | (lid1, uu___2) -> FStarC_Ident.string_of_lid lid1)
                env1.modules in
            let msg =
              let uu___1 =
                let uu___2 = FStarC_Ident.string_of_lid lid in
                FStarC_Compiler_Util.format1 "Identifier not found: [%s]"
                  uu___2 in
              FStarC_Errors_Msg.mkmsg uu___1 in
            let msg1 =
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStarC_Ident.ns_of_lid lid in
                  FStarC_Compiler_List.length uu___3 in
                uu___2 = Prims.int_zero in
              if uu___1
              then msg
              else
                (let modul =
                   let uu___3 =
                     let uu___4 = FStarC_Ident.ns_of_lid lid in
                     FStarC_Ident.lid_of_ids uu___4 in
                   let uu___4 = FStarC_Ident.range_of_lid lid in
                   FStarC_Ident.set_lid_range uu___3 uu___4 in
                 let subdoc d =
                   let uu___3 =
                     let uu___4 = FStarC_Pprint.align d in
                     FStarC_Pprint.op_Hat_Hat FStarC_Pprint.hardline uu___4 in
                   FStarC_Pprint.nest (Prims.of_int (2)) uu___3 in
                 let uu___3 = resolve_module_name env1 modul true in
                 match uu___3 with
                 | FStar_Pervasives_Native.None ->
                     let opened_modules1 =
                       FStarC_Errors_Msg.text
                         (FStarC_Compiler_String.concat ", " opened_modules) in
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = FStarC_Ident.string_of_lid modul in
                           FStarC_Compiler_Util.format1
                             "Could not resolve module name %s" uu___7 in
                         FStarC_Errors_Msg.text uu___6 in
                       [uu___5] in
                     FStarC_Compiler_List.op_At msg uu___4
                 | FStar_Pervasives_Native.Some modul' when
                     let uu___4 =
                       FStarC_Compiler_List.existsb
                         (fun m ->
                            let uu___5 = FStarC_Ident.string_of_lid modul' in
                            m = uu___5) opened_modules in
                     Prims.op_Negation uu___4 ->
                     let opened_modules1 =
                       FStarC_Errors_Msg.text
                         (FStarC_Compiler_String.concat ", " opened_modules) in
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             let uu___8 = FStarC_Ident.string_of_lid modul in
                             let uu___9 = FStarC_Ident.string_of_lid modul' in
                             FStarC_Compiler_Util.format2
                               "Module %s resolved into %s, which does not belong to the list of modules in scope, namely:"
                               uu___8 uu___9 in
                           FStarC_Errors_Msg.text uu___7 in
                         let uu___7 = subdoc opened_modules1 in
                         FStarC_Pprint.op_Hat_Hat uu___6 uu___7 in
                       [uu___5] in
                     FStarC_Compiler_List.op_At msg uu___4
                 | FStar_Pervasives_Native.Some modul' ->
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = FStarC_Ident.string_of_lid modul in
                           let uu___8 = FStarC_Ident.string_of_lid modul' in
                           let uu___9 =
                             let uu___10 = FStarC_Ident.ident_of_lid lid in
                             FStarC_Ident.string_of_id uu___10 in
                           FStarC_Compiler_Util.format3
                             "Module %s resolved into %s, definition %s not found"
                             uu___7 uu___8 uu___9 in
                         FStarC_Errors_Msg.text uu___6 in
                       [uu___5] in
                     FStarC_Compiler_List.op_At msg uu___4) in
            FStarC_Errors.raise_error FStarC_Ident.hasrange_lident lid
              FStarC_Errors_Codes.Fatal_IdentifierNotFound ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic msg1)
let fail_or2 :
  'a .
    (FStarC_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStarC_Ident.ident -> 'a
  =
  fun lookup ->
    fun id ->
      let uu___ = lookup id in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Ident.string_of_id id in
              Prims.strcat uu___3 "]" in
            Prims.strcat "Identifier not found [" uu___2 in
          FStarC_Errors.raise_error FStarC_Ident.hasrange_ident id
            FStarC_Errors_Codes.Fatal_IdentifierNotFound ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___1)
      | FStar_Pervasives_Native.Some r -> r
let (resolve_name :
  env ->
    FStarC_Ident.lident ->
      (FStarC_Syntax_Syntax.bv, FStarC_Syntax_Syntax.fv)
        FStar_Pervasives.either FStar_Pervasives_Native.option)
  =
  fun e ->
    fun name ->
      let uu___ = try_lookup_name false false e name in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (Term_name (e1, attrs)) ->
          let uu___1 =
            let uu___2 = FStarC_Syntax_Subst.compress e1 in
            uu___2.FStarC_Syntax_Syntax.n in
          (match uu___1 with
           | FStarC_Syntax_Syntax.Tm_name n ->
               FStar_Pervasives_Native.Some (FStar_Pervasives.Inl n)
           | FStarC_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some (FStar_Pervasives.Inr fv)
           | uu___2 -> FStar_Pervasives_Native.None)
      | FStar_Pervasives_Native.Some (Eff_name (se, l)) ->
          let uu___1 =
            let uu___2 =
              FStarC_Syntax_Syntax.lid_and_dd_as_fv l
                FStar_Pervasives_Native.None in
            FStar_Pervasives.Inr uu___2 in
          FStar_Pervasives_Native.Some uu___1