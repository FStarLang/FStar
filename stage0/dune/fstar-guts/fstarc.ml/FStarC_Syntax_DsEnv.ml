open Prims
let rec takeWhileMax :
  'a . Prims.int -> ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list =
  fun n f xs ->
    if n <= Prims.int_zero
    then []
    else
      (match xs with
       | [] -> []
       | x::xs' ->
           if f x then x :: (takeWhileMax (n - Prims.int_one) f xs') else [])
let typo_candidates (x : Prims.string) (xs : Prims.string Prims.list) :
  Prims.string Prims.list=
  let cands =
    FStarC_List.map
      (fun y -> let uu___ = FStarC_EditDist.edit_distance x y in (uu___, y))
      xs in
  let cands1 =
    let uu___ =
      FStarC_Class_Ord.sort
        (FStarC_Class_Ord.ord_tuple2 FStarC_Class_Ord.ord_int
           FStarC_Class_Ord.ord_string) cands in
    FStarC_Class_Ord.dedup
      (FStarC_Class_Ord.ord_tuple2 FStarC_Class_Ord.ord_int
         FStarC_Class_Ord.ord_string) uu___ in
  let cands2 =
    takeWhileMax (Prims.of_int (5))
      (fun uu___ -> match uu___ with | (d, uu___1) -> d < (Prims.of_int (3)))
      cands1 in
  FStarC_List.map FStar_Pervasives_Native.snd cands2
let rec list_sep2 : 'a . 'a -> 'a -> 'a Prims.list -> 'a Prims.list =
  fun s1 s2 xs ->
    match xs with
    | [] -> []
    | x::[] -> [x]
    | x::y::[] -> [x; s2; y]
    | x::y::xs1 -> x :: s1 :: (list_sep2 s1 s2 (y :: xs1))
let typo_msg (x : Prims.string) (xs : Prims.string Prims.list) :
  FStar_Pprint.document=
  let cands = typo_candidates x xs in
  if (FStarC_List.length cands) = Prims.int_zero
  then FStar_Pprint.empty
  else
    (let uu___1 =
       let uu___2 =
         let uu___3 =
           let uu___4 =
             let uu___5 = FStarC_List.map FStar_Pprint.doc_of_string cands in
             list_sep2
               (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                  (FStar_Pprint.break_ Prims.int_one))
               (FStar_Pprint.op_Hat_Hat (FStar_Pprint.break_ Prims.int_one)
                  (FStar_Pprint.op_Hat_Hat (FStar_Pprint.doc_of_string "or")
                     (FStar_Pprint.break_ Prims.int_one))) uu___5 in
           FStar_Pprint.flow FStar_Pprint.empty uu___4 in
         FStar_Pprint.op_Hat_Hat uu___3 (FStar_Pprint.doc_of_string "?") in
       FStar_Pprint.op_Hat_Slash_Hat
         (FStarC_Errors_Msg.text "Hint: Did you mean") uu___2 in
     FStar_Pprint.nest (Prims.of_int (2)) uu___1)
let ugly_sigelt_to_string_hook :
  (FStarC_Syntax_Syntax.sigelt -> Prims.string) FStarC_Effect.ref=
  FStarC_Effect.mk_ref (fun uu___ -> "")
type open_module_or_namespace = FStarC_Syntax_Syntax.open_module_or_namespace
type used_marker = Prims.bool FStarC_Effect.ref
type record_or_dc =
  {
  typename: FStarC_Ident.lident ;
  constrname: FStarC_Ident.ident ;
  parms: FStarC_Syntax_Syntax.binders ;
  fields: (FStarC_Ident.ident * FStarC_Syntax_Syntax.typ) Prims.list ;
  is_private: Prims.bool ;
  is_record: Prims.bool }
let __proj__Mkrecord_or_dc__item__typename (projectee : record_or_dc) :
  FStarC_Ident.lident=
  match projectee with
  | { typename; constrname; parms; fields; is_private; is_record;_} ->
      typename
let __proj__Mkrecord_or_dc__item__constrname (projectee : record_or_dc) :
  FStarC_Ident.ident=
  match projectee with
  | { typename; constrname; parms; fields; is_private; is_record;_} ->
      constrname
let __proj__Mkrecord_or_dc__item__parms (projectee : record_or_dc) :
  FStarC_Syntax_Syntax.binders=
  match projectee with
  | { typename; constrname; parms; fields; is_private; is_record;_} -> parms
let __proj__Mkrecord_or_dc__item__fields (projectee : record_or_dc) :
  (FStarC_Ident.ident * FStarC_Syntax_Syntax.typ) Prims.list=
  match projectee with
  | { typename; constrname; parms; fields; is_private; is_record;_} -> fields
let __proj__Mkrecord_or_dc__item__is_private (projectee : record_or_dc) :
  Prims.bool=
  match projectee with
  | { typename; constrname; parms; fields; is_private; is_record;_} ->
      is_private
let __proj__Mkrecord_or_dc__item__is_record (projectee : record_or_dc) :
  Prims.bool=
  match projectee with
  | { typename; constrname; parms; fields; is_private; is_record;_} ->
      is_record
let ugly_sigelt_to_string (se : FStarC_Syntax_Syntax.sigelt) : Prims.string=
  let uu___ = FStarC_Effect.op_Bang ugly_sigelt_to_string_hook in uu___ se
type local_binding =
  (FStarC_Ident.ident * FStarC_Syntax_Syntax.bv * used_marker)
type rec_binding = (FStarC_Ident.ident * FStarC_Ident.lid * used_marker)
type scope_mod =
  | Local_bindings of local_binding FStarC_PSMap.t 
  | Rec_binding of rec_binding 
  | Module_abbrev of FStarC_Syntax_Syntax.module_abbrev 
  | Open_module_or_namespace of (open_module_or_namespace * Prims.bool) 
  | Top_level_defs of unit FStarC_PSMap.t 
  | Record_or_dc of record_or_dc 
let uu___is_Local_bindings (projectee : scope_mod) : Prims.bool=
  match projectee with | Local_bindings _0 -> true | uu___ -> false
let __proj__Local_bindings__item___0 (projectee : scope_mod) :
  local_binding FStarC_PSMap.t=
  match projectee with | Local_bindings _0 -> _0
let uu___is_Rec_binding (projectee : scope_mod) : Prims.bool=
  match projectee with | Rec_binding _0 -> true | uu___ -> false
let __proj__Rec_binding__item___0 (projectee : scope_mod) : rec_binding=
  match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev (projectee : scope_mod) : Prims.bool=
  match projectee with | Module_abbrev _0 -> true | uu___ -> false
let __proj__Module_abbrev__item___0 (projectee : scope_mod) :
  FStarC_Syntax_Syntax.module_abbrev=
  match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace (projectee : scope_mod) : Prims.bool=
  match projectee with | Open_module_or_namespace _0 -> true | uu___ -> false
let __proj__Open_module_or_namespace__item___0 (projectee : scope_mod) :
  (open_module_or_namespace * Prims.bool)=
  match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_defs (projectee : scope_mod) : Prims.bool=
  match projectee with | Top_level_defs _0 -> true | uu___ -> false
let __proj__Top_level_defs__item___0 (projectee : scope_mod) :
  unit FStarC_PSMap.t= match projectee with | Top_level_defs _0 -> _0
let uu___is_Record_or_dc (projectee : scope_mod) : Prims.bool=
  match projectee with | Record_or_dc _0 -> true | uu___ -> false
let __proj__Record_or_dc__item___0 (projectee : scope_mod) : record_or_dc=
  match projectee with | Record_or_dc _0 -> _0
let namespace_scope_of_module (mname : FStarC_Ident.lident) :
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.open_kind *
    FStarC_Syntax_Syntax.restriction) Prims.list=
  if (FStarC_List.length (FStarC_Ident.ns_of_lid mname)) > Prims.int_zero
  then
    let uu___ =
      let uu___1 = FStarC_Ident.lid_of_ids (FStarC_Ident.ns_of_lid mname) in
      (uu___1, FStarC_Syntax_Syntax.Open_namespace,
        FStarC_Syntax_Syntax.Unrestricted) in
    [uu___]
  else []
let scope_mod_as_parsing_data (s : scope_mod) :
  FStarC_Parser_Dep.parsing_data_elt Prims.list=
  match s with
  | Local_bindings uu___ -> []
  | Rec_binding uu___ -> []
  | Module_abbrev ma -> [FStarC_Parser_Dep.P_alias ma]
  | Open_module_or_namespace ((l, _k, _restrict), uu___) ->
      [FStarC_Parser_Dep.P_open (false, l)]
  | Top_level_defs uu___ -> []
  | Record_or_dc uu___ -> []
let uu___0 : scope_mod FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Local_bindings lbs ->
             let uu___1 =
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_list
                    FStarC_Class_Show.showable_string)
                 (FStarC_PSMap.keys lbs) in
             FStarC_Format.fmt1 "(Local_bindings %s)" uu___1
         | Rec_binding (id, lid, uu___1) ->
             Prims.strcat "Rec_binding "
               (Prims.strcat (FStarC_Ident.string_of_id id)
                  (Prims.strcat " " (FStarC_Ident.string_of_lid lid)))
         | Module_abbrev (id, lid) ->
             Prims.strcat "Module_abbrev "
               (Prims.strcat (FStarC_Ident.string_of_id id)
                  (Prims.strcat " " (FStarC_Ident.string_of_lid lid)))
         | Open_module_or_namespace ((lid, uu___1, uu___2), implicit) ->
             let uu___3 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                 implicit in
             let uu___4 =
               FStarC_Class_Show.show FStarC_Ident.showable_lident lid in
             FStarC_Format.fmt2 "Open_module_or_namespace(implicit=%s) %s"
               uu___3 uu___4
         | Top_level_defs lbs ->
             let uu___1 =
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_list
                    FStarC_Class_Show.showable_string)
                 (FStarC_PSMap.keys lbs) in
             FStarC_Format.fmt1 "(Top_level_defs %s)" uu___1
         | Record_or_dc r ->
             Prims.strcat "Record_or_dc "
               (FStarC_Ident.string_of_lid r.typename))
  }
type string_set = Prims.string FStarC_RBSet.t
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field 
let uu___is_Exported_id_term_type (projectee : exported_id_kind) :
  Prims.bool=
  match projectee with | Exported_id_term_type -> true | uu___ -> false
let uu___is_Exported_id_field (projectee : exported_id_kind) : Prims.bool=
  match projectee with | Exported_id_field -> true | uu___ -> false
let uu___1 : exported_id_kind FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Exported_id_field -> "Exported_id_field"
         | Exported_id_term_type -> "Exported_id_term_type")
  }
type exported_id_set = exported_id_kind -> string_set FStarC_Effect.ref
type env =
  {
  curmodule: FStarC_Ident.lident FStar_Pervasives_Native.option ;
  curmonad: FStarC_Ident.ident FStar_Pervasives_Native.option ;
  modules: (FStarC_Ident.lident * FStarC_Syntax_Syntax.modul) Prims.list ;
  scope_mods: scope_mod Prims.list ;
  exported_ids: exported_id_set FStarC_SMap.t ;
  trans_exported_ids: exported_id_set FStarC_SMap.t ;
  includes:
    (FStarC_Ident.lident * FStarC_Syntax_Syntax.restriction) Prims.list
      FStarC_Effect.ref FStarC_SMap.t
    ;
  sigaccum: FStarC_Syntax_Syntax.sigelts ;
  sigmap: (FStarC_Syntax_Syntax.sigelt * Prims.bool) FStarC_SMap.t ;
  iface: Prims.bool ;
  admitted_iface: Prims.bool ;
  expect_typ: Prims.bool ;
  remaining_iface_decls:
    (FStarC_Ident.lident * FStarC_Parser_AST.decl Prims.list) Prims.list ;
  iface_interleaving_init: Prims.bool ;
  syntax_only: Prims.bool ;
  ds_hooks: dsenv_hooks ;
  dep_graph: FStarC_Parser_Dep.deps ;
  no_prelude: Prims.bool }
and dsenv_hooks =
  {
  ds_push_open_hook: env -> open_module_or_namespace -> unit ;
  ds_push_include_hook: env -> FStarC_Ident.lident -> unit ;
  ds_push_module_abbrev_hook:
    env -> FStarC_Ident.ident -> FStarC_Ident.lident -> unit }
let __proj__Mkenv__item__curmodule (projectee : env) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> curmodule
let __proj__Mkenv__item__curmonad (projectee : env) :
  FStarC_Ident.ident FStar_Pervasives_Native.option=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> curmonad
let __proj__Mkenv__item__modules (projectee : env) :
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.modul) Prims.list=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> modules
let __proj__Mkenv__item__scope_mods (projectee : env) : scope_mod Prims.list=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> scope_mods
let __proj__Mkenv__item__exported_ids (projectee : env) :
  exported_id_set FStarC_SMap.t=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> exported_ids
let __proj__Mkenv__item__trans_exported_ids (projectee : env) :
  exported_id_set FStarC_SMap.t=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> trans_exported_ids
let __proj__Mkenv__item__includes (projectee : env) :
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.restriction) Prims.list
    FStarC_Effect.ref FStarC_SMap.t=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> includes
let __proj__Mkenv__item__sigaccum (projectee : env) :
  FStarC_Syntax_Syntax.sigelts=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> sigaccum
let __proj__Mkenv__item__sigmap (projectee : env) :
  (FStarC_Syntax_Syntax.sigelt * Prims.bool) FStarC_SMap.t=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> sigmap
let __proj__Mkenv__item__iface (projectee : env) : Prims.bool=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> iface
let __proj__Mkenv__item__admitted_iface (projectee : env) : Prims.bool=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> admitted_iface
let __proj__Mkenv__item__expect_typ (projectee : env) : Prims.bool=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> expect_typ
let __proj__Mkenv__item__remaining_iface_decls (projectee : env) :
  (FStarC_Ident.lident * FStarC_Parser_AST.decl Prims.list) Prims.list=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} ->
      remaining_iface_decls
let __proj__Mkenv__item__iface_interleaving_init (projectee : env) :
  Prims.bool=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} ->
      iface_interleaving_init
let __proj__Mkenv__item__syntax_only (projectee : env) : Prims.bool=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> syntax_only
let __proj__Mkenv__item__ds_hooks (projectee : env) : dsenv_hooks=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> ds_hooks
let __proj__Mkenv__item__dep_graph (projectee : env) :
  FStarC_Parser_Dep.deps=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> dep_graph
let __proj__Mkenv__item__no_prelude (projectee : env) : Prims.bool=
  match projectee with
  | { curmodule; curmonad; modules; scope_mods; exported_ids;
      trans_exported_ids; includes; sigaccum; sigmap; iface; admitted_iface;
      expect_typ; remaining_iface_decls; iface_interleaving_init;
      syntax_only; ds_hooks; dep_graph; no_prelude;_} -> no_prelude
let __proj__Mkdsenv_hooks__item__ds_push_open_hook (projectee : dsenv_hooks)
  : env -> open_module_or_namespace -> unit=
  match projectee with
  | { ds_push_open_hook; ds_push_include_hook; ds_push_module_abbrev_hook;_}
      -> ds_push_open_hook
let __proj__Mkdsenv_hooks__item__ds_push_include_hook
  (projectee : dsenv_hooks) : env -> FStarC_Ident.lident -> unit=
  match projectee with
  | { ds_push_open_hook; ds_push_include_hook; ds_push_module_abbrev_hook;_}
      -> ds_push_include_hook
let __proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook
  (projectee : dsenv_hooks) :
  env -> FStarC_Ident.ident -> FStarC_Ident.lident -> unit=
  match projectee with
  | { ds_push_open_hook; ds_push_include_hook; ds_push_module_abbrev_hook;_}
      -> ds_push_module_abbrev_hook
type 'a withenv = env -> ('a * env)
type foundname =
  | Term_name of (FStarC_Syntax_Syntax.typ * FStarC_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStarC_Syntax_Syntax.sigelt * FStarC_Ident.lident) 
let uu___is_Term_name (projectee : foundname) : Prims.bool=
  match projectee with | Term_name _0 -> true | uu___ -> false
let __proj__Term_name__item___0 (projectee : foundname) :
  (FStarC_Syntax_Syntax.typ * FStarC_Syntax_Syntax.attribute Prims.list)=
  match projectee with | Term_name _0 -> _0
let uu___is_Eff_name (projectee : foundname) : Prims.bool=
  match projectee with | Eff_name _0 -> true | uu___ -> false
let __proj__Eff_name__item___0 (projectee : foundname) :
  (FStarC_Syntax_Syntax.sigelt * FStarC_Ident.lident)=
  match projectee with | Eff_name _0 -> _0
let parsing_data_for_scope (e : env) :
  FStarC_Parser_Dep.parsing_data_elt Prims.list=
  let curmod_scope =
    match e.curmodule with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some m -> namespace_scope_of_module m in
  let scope_mods =
    match curmod_scope with
    | [] -> e.scope_mods
    | (lid, uu___, uu___2)::[] ->
        FStarC_List.filter
          (fun uu___3 ->
             match uu___3 with
             | Open_module_or_namespace ((lid', uu___4, uu___5), true) ->
                 Prims.op_Negation (FStarC_Ident.lid_equals lid lid')
             | uu___4 -> true) e.scope_mods in
  FStarC_List.collect scope_mod_as_parsing_data scope_mods
let with_restored_scope (e : env) (f : env -> ('a * env)) : ('a * env)=
  let uu___ = f e in
  match uu___ with
  | (res, e1) ->
      (res,
        {
          curmodule = (e.curmodule);
          curmonad = (e.curmonad);
          modules = (e1.modules);
          scope_mods = (e.scope_mods);
          exported_ids = (e1.exported_ids);
          trans_exported_ids = (e1.trans_exported_ids);
          includes = (e1.includes);
          sigaccum = (e.sigaccum);
          sigmap = (e1.sigmap);
          iface = (e.iface);
          admitted_iface = (e.admitted_iface);
          expect_typ = (e.expect_typ);
          remaining_iface_decls = (e.remaining_iface_decls);
          iface_interleaving_init = (e.iface_interleaving_init);
          syntax_only = (e1.syntax_only);
          ds_hooks = (e1.ds_hooks);
          dep_graph = (e1.dep_graph);
          no_prelude = (e.no_prelude)
        })
let all_local_names (env1 : env) : Prims.string Prims.list=
  FStarC_List.fold_right
    (fun scope acc ->
       match scope with
       | Local_bindings lbs -> FStarC_List.op_At (FStarC_PSMap.keys lbs) acc
       | Rec_binding (x, uu___, uu___2) -> (FStarC_Ident.string_of_id x) ::
           acc
       | Module_abbrev (x, uu___) -> acc
       | Open_module_or_namespace uu___ -> acc
       | Top_level_defs lbs -> FStarC_List.op_At (FStarC_PSMap.keys lbs) acc
       | Record_or_dc r -> (FStarC_Ident.string_of_lid r.typename) :: acc)
    env1.scope_mods []
let all_mod_names (env1 : env) : Prims.string Prims.list=
  let uu___ =
    FStarC_List.map
      (fun uu___2 ->
         match uu___2 with | (l, uu___3) -> FStarC_Ident.string_of_lid l)
      env1.modules in
  let uu___2 =
    FStarC_List.fold_right
      (fun scope acc ->
         match scope with
         | Local_bindings lbs -> acc
         | Rec_binding (x, uu___3, uu___4) -> acc
         | Module_abbrev (x, uu___3) -> (FStarC_Ident.string_of_id x) :: acc
         | Open_module_or_namespace ((m, uu___3, uu___4), uu___5) ->
             (FStarC_Ident.string_of_lid m) :: acc
         | Top_level_defs lbs -> acc
         | Record_or_dc r -> acc) env1.scope_mods [] in
  FStarC_List.op_At uu___ uu___2
let showable_env : env FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun env1 ->
         let uu___ =
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_option FStarC_Ident.showable_lident)
             env1.curmodule in
         let uu___2 =
           let uu___3 =
             FStarC_List.map FStar_Pervasives_Native.fst env1.modules in
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_list FStarC_Ident.showable_lident)
             uu___3 in
         let uu___3 =
           FStarC_Class_Show.show (FStarC_Class_Show.show_list uu___0)
             env1.scope_mods in
         FStarC_Format.fmt3
           "DsEnv { curmod=%s; All mods: %s\nScope mods: %s\n }" uu___ uu___2
           uu___3)
  }
let mk_dsenv_hooks (open_hook : env -> open_module_or_namespace -> unit)
  (include_hook : env -> FStarC_Ident.lident -> unit)
  (module_abbrev_hook :
    env -> FStarC_Ident.ident -> FStarC_Ident.lident -> unit)
  : dsenv_hooks=
  {
    ds_push_open_hook = open_hook;
    ds_push_include_hook = include_hook;
    ds_push_module_abbrev_hook = module_abbrev_hook
  }
let default_ds_hooks : dsenv_hooks=
  {
    ds_push_open_hook = (fun uu___ uu___2 -> ());
    ds_push_include_hook = (fun uu___ uu___2 -> ());
    ds_push_module_abbrev_hook = (fun uu___ uu___2 uu___3 -> ())
  }
let set_iface (env1 : env) (b : Prims.bool) : env=
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
    iface_interleaving_init = (env1.iface_interleaving_init);
    syntax_only = (env1.syntax_only);
    ds_hooks = (env1.ds_hooks);
    dep_graph = (env1.dep_graph);
    no_prelude = (env1.no_prelude)
  }
let iface (e : env) : Prims.bool= e.iface
let set_admitted_iface (e : env) (b : Prims.bool) : env=
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
    iface_interleaving_init = (e.iface_interleaving_init);
    syntax_only = (e.syntax_only);
    ds_hooks = (e.ds_hooks);
    dep_graph = (e.dep_graph);
    no_prelude = (e.no_prelude)
  }
let admitted_iface (e : env) : Prims.bool= e.admitted_iface
let set_expect_typ (e : env) (b : Prims.bool) : env=
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
    iface_interleaving_init = (e.iface_interleaving_init);
    syntax_only = (e.syntax_only);
    ds_hooks = (e.ds_hooks);
    dep_graph = (e.dep_graph);
    no_prelude = (e.no_prelude)
  }
let expect_typ (e : env) : Prims.bool= e.expect_typ
let all_exported_id_kinds : exported_id_kind Prims.list=
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids (env1 : env) (lid : FStarC_Ident.lident) :
  Prims.string Prims.list=
  let module_name = FStarC_Ident.string_of_lid lid in
  let uu___ = FStarC_SMap.try_find env1.trans_exported_ids module_name in
  match uu___ with
  | FStar_Pervasives_Native.None -> []
  | FStar_Pervasives_Native.Some exported_id_set1 ->
      let uu___2 =
        FStarC_Effect.op_Bang (exported_id_set1 Exported_id_term_type) in
      FStarC_Class_Setlike.elems ()
        (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
        (Obj.magic uu___2)
let opens_and_abbrevs (env1 : env) :
  (open_module_or_namespace, FStarC_Syntax_Syntax.module_abbrev)
    FStar_Pervasives.either Prims.list=
  FStarC_List.collect
    (fun uu___ ->
       match uu___ with
       | Open_module_or_namespace (payload, uu___2) ->
           [FStar_Pervasives.Inl payload]
       | Module_abbrev (id, lid) -> [FStar_Pervasives.Inr (id, lid)]
       | uu___2 -> []) env1.scope_mods
let open_modules (e : env) :
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.modul) Prims.list= e.modules
let open_modules_and_namespaces (env1 : env) :
  FStarC_Ident.lident Prims.list=
  FStarC_List.filter_map
    (fun uu___ ->
       match uu___ with
       | Open_module_or_namespace ((lid, _info, _restriction), uu___2) ->
           FStar_Pervasives_Native.Some lid
       | uu___2 -> FStar_Pervasives_Native.None) env1.scope_mods
let module_abbrevs (env1 : env) :
  (FStarC_Ident.ident * FStarC_Ident.lident) Prims.list=
  FStarC_List.filter_map
    (fun uu___ ->
       match uu___ with
       | Module_abbrev (l, m) -> FStar_Pervasives_Native.Some (l, m)
       | uu___2 -> FStar_Pervasives_Native.None) env1.scope_mods
let set_current_module (e : env) (l : FStarC_Ident.lident) : env=
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
    iface_interleaving_init = (e.iface_interleaving_init);
    syntax_only = (e.syntax_only);
    ds_hooks = (e.ds_hooks);
    dep_graph = (e.dep_graph);
    no_prelude = (e.no_prelude)
  }
let clear_scope_mods (e : env) : env=
  {
    curmodule = (e.curmodule);
    curmonad = (e.curmonad);
    modules = (e.modules);
    scope_mods = [];
    exported_ids = (e.exported_ids);
    trans_exported_ids = (e.trans_exported_ids);
    includes = (e.includes);
    sigaccum = (e.sigaccum);
    sigmap = (e.sigmap);
    iface = (e.iface);
    admitted_iface = (e.admitted_iface);
    expect_typ = (e.expect_typ);
    remaining_iface_decls = (e.remaining_iface_decls);
    iface_interleaving_init = (e.iface_interleaving_init);
    syntax_only = (e.syntax_only);
    ds_hooks = (e.ds_hooks);
    dep_graph = (e.dep_graph);
    no_prelude = (e.no_prelude)
  }
let current_module (env1 : env) : FStarC_Ident.lident=
  match env1.curmodule with
  | FStar_Pervasives_Native.None ->
      FStarC_Effect.failwith "Unset current module"
  | FStar_Pervasives_Native.Some m -> m
let iface_decls (env1 : env) (l : FStarC_Ident.lident) :
  FStarC_Parser_AST.decl Prims.list FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___2 ->
         match uu___2 with | (m, uu___3) -> FStarC_Ident.lid_equals l m)
      env1.remaining_iface_decls in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (uu___2, decls) ->
      FStar_Pervasives_Native.Some decls
let set_iface_decls (env1 : env) (l : FStarC_Ident.lident)
  (ds : FStarC_Parser_AST.decl Prims.list) : env=
  let uu___ =
    FStarC_List.partition
      (fun uu___2 ->
         match uu___2 with | (m, uu___3) -> FStarC_Ident.lid_equals l m)
      env1.remaining_iface_decls in
  match uu___ with
  | (uu___2, rest) ->
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
        iface_interleaving_init = true;
        syntax_only = (env1.syntax_only);
        ds_hooks = (env1.ds_hooks);
        dep_graph = (env1.dep_graph);
        no_prelude = (env1.no_prelude)
      }
let iface_interleaving_init (e : env) : Prims.bool= e.iface_interleaving_init
let qual : FStarC_Ident.lident -> FStarC_Ident.ident -> FStarC_Ident.lident=
  FStarC_Ident.qual_id
let qualify (env1 : env) (id : FStarC_Ident.ident) : FStarC_Ident.lident=
  match env1.curmonad with
  | FStar_Pervasives_Native.None ->
      let uu___ = current_module env1 in qual uu___ id
  | FStar_Pervasives_Native.Some monad ->
      let uu___ = let uu___2 = current_module env1 in qual uu___2 monad in
      FStarC_Syntax_Util.mk_field_projector_name_from_ident uu___ id
let syntax_only (env1 : env) : Prims.bool= env1.syntax_only
let set_syntax_only (env1 : env) (b : Prims.bool) : env=
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
    iface_interleaving_init = (env1.iface_interleaving_init);
    syntax_only = b;
    ds_hooks = (env1.ds_hooks);
    dep_graph = (env1.dep_graph);
    no_prelude = (env1.no_prelude)
  }
let ds_hooks (env1 : env) : dsenv_hooks= env1.ds_hooks
let set_ds_hooks (env1 : env) (hooks : dsenv_hooks) : env=
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
    iface_interleaving_init = (env1.iface_interleaving_init);
    syntax_only = (env1.syntax_only);
    ds_hooks = hooks;
    dep_graph = (env1.dep_graph);
    no_prelude = (env1.no_prelude)
  }
let new_sigmap (uu___ : unit) : 'uuuuu FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int (100))
let empty_env (deps : FStarC_Parser_Dep.deps) : env=
  let uu___ = new_sigmap () in
  let uu___2 = new_sigmap () in
  let uu___3 = new_sigmap () in
  let uu___4 = new_sigmap () in
  {
    curmodule = FStar_Pervasives_Native.None;
    curmonad = FStar_Pervasives_Native.None;
    modules = [];
    scope_mods = [];
    exported_ids = uu___;
    trans_exported_ids = uu___2;
    includes = uu___3;
    sigaccum = [];
    sigmap = uu___4;
    iface = false;
    admitted_iface = false;
    expect_typ = false;
    remaining_iface_decls = [];
    iface_interleaving_init = false;
    syntax_only = false;
    ds_hooks = default_ds_hooks;
    dep_graph = deps;
    no_prelude = false
  }
let dep_graph (env1 : env) : FStarC_Parser_Dep.deps= env1.dep_graph
let set_dep_graph (env1 : env) (ds : FStarC_Parser_Dep.deps) : env=
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
    iface_interleaving_init = (env1.iface_interleaving_init);
    syntax_only = (env1.syntax_only);
    ds_hooks = (env1.ds_hooks);
    dep_graph = ds;
    no_prelude = (env1.no_prelude)
  }
let sigmap (env1 : env) :
  (FStarC_Syntax_Syntax.sigelt * Prims.bool) FStarC_SMap.t= env1.sigmap
let set_bv_range (bv : FStarC_Syntax_Syntax.bv) (r : FStarC_Range_Type.range)
  : FStarC_Syntax_Syntax.bv=
  let id = FStarC_Ident.set_id_range r bv.FStarC_Syntax_Syntax.ppname in
  {
    FStarC_Syntax_Syntax.ppname = id;
    FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
    FStarC_Syntax_Syntax.sort = (bv.FStarC_Syntax_Syntax.sort)
  }
let bv_to_name (bv : FStarC_Syntax_Syntax.bv) (r : FStarC_Range_Type.range) :
  FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Syntax.bv_to_name (set_bv_range bv r)
let unmangleMap :
  (Prims.string * Prims.string * FStarC_Syntax_Syntax.fv_qual
    FStar_Pervasives_Native.option) Prims.list=
  [("op_ColonColon", "Cons",
     (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Pervasives_Native.None)]
let unmangleOpName (id : FStarC_Ident.ident) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  FStarC_Util.find_map unmangleMap
    (fun uu___ ->
       match uu___ with
       | (x, y, dq) ->
           if (FStarC_Ident.string_of_id id) = x
           then
             let uu___2 =
               let uu___3 =
                 FStarC_Ident.lid_of_path ["Prims"; y]
                   (FStarC_Ident.range_of_id id) in
               FStarC_Syntax_Syntax.fvar_with_dd uu___3 dq in
             FStar_Pervasives_Native.Some uu___2
           else FStar_Pervasives_Native.None)
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok (projectee : 'a cont_t) : Prims.bool=
  match projectee with | Cont_ok _0 -> true | uu___ -> false
let __proj__Cont_ok__item___0 (projectee : 'a cont_t) : 'a=
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail (projectee : 'a cont_t) : Prims.bool=
  match projectee with | Cont_fail -> true | uu___ -> false
let uu___is_Cont_ignore (projectee : 'a cont_t) : Prims.bool=
  match projectee with | Cont_ignore -> true | uu___ -> false
let option_of_cont (k_ignore : unit -> 'a FStar_Pervasives_Native.option)
  (uu___ : 'a cont_t) : 'a FStar_Pervasives_Native.option=
  match uu___ with
  | Cont_ok a1 -> FStar_Pervasives_Native.Some a1
  | Cont_fail -> FStar_Pervasives_Native.None
  | Cont_ignore -> k_ignore ()
let find_in_record (ns : FStarC_Ident.ident Prims.list)
  (id : FStarC_Ident.ident) (record : record_or_dc)
  (cont : record_or_dc -> 'a cont_t) : 'a cont_t=
  let typename' =
    FStarC_Ident.lid_of_ids
      (FStarC_List.op_At ns [FStarC_Ident.ident_of_lid record.typename]) in
  if FStarC_Ident.lid_equals typename' record.typename
  then
    let fname =
      FStarC_Ident.lid_of_ids
        (FStarC_List.op_At (FStarC_Ident.ns_of_lid record.typename) [id]) in
    let find =
      FStarC_Util.find_map record.fields
        (fun uu___ ->
           match uu___ with
           | (f, uu___2) ->
               if
                 (FStarC_Ident.string_of_id id) =
                   (FStarC_Ident.string_of_id f)
               then FStar_Pervasives_Native.Some record
               else FStar_Pervasives_Native.None) in
    match find with
    | FStar_Pervasives_Native.Some r -> cont r
    | FStar_Pervasives_Native.None -> Cont_ignore
  else Cont_ignore
let find_in_record_many (ids : FStarC_Ident.ident Prims.list)
  (record : record_or_dc) (cont : record_or_dc -> 'a cont_t) : 'a cont_t=
  let found =
    FStarC_Util.multiset_equiv
      (fun uu___ id ->
         match uu___ with
         | (fn, uu___2) ->
             (FStarC_Ident.string_of_id id) = (FStarC_Ident.string_of_id fn))
      record.fields ids in
  if found then cont record else Cont_ignore
let get_exported_id_set (e : env) (mname : Prims.string) :
  (exported_id_kind -> string_set FStarC_Effect.ref)
    FStar_Pervasives_Native.option=
  FStarC_SMap.try_find e.exported_ids mname
let get_trans_exported_id_set (e : env) (mname : Prims.string) :
  (exported_id_kind -> string_set FStarC_Effect.ref)
    FStar_Pervasives_Native.option=
  FStarC_SMap.try_find e.trans_exported_ids mname
let string_of_exported_id_kind (uu___ : exported_id_kind) : Prims.string=
  match uu___ with
  | Exported_id_field -> "field"
  | Exported_id_term_type -> "term/type"
let is_exported_id_termtype (uu___ : exported_id_kind) : Prims.bool=
  match uu___ with | Exported_id_term_type -> true | uu___2 -> false
let is_exported_id_field (uu___ : exported_id_kind) : Prims.bool=
  match uu___ with | Exported_id_field -> true | uu___2 -> false
let find_in_module_with_includes (eikind : exported_id_kind)
  (find_in_module : FStarC_Ident.lident -> 'a cont_t)
  (find_in_module_default : 'a cont_t) (env1 : env)
  (ns : FStarC_Ident.lident) (id : FStarC_Ident.ident) : 'a cont_t=
  let rec aux x =
    match x with
    | [] -> find_in_module_default
    | (modul, id1)::q ->
        let mname = FStarC_Ident.string_of_lid modul in
        let not_shadowed =
          let uu___ = get_exported_id_set env1 mname in
          match uu___ with
          | FStar_Pervasives_Native.None -> true
          | FStar_Pervasives_Native.Some mex ->
              let mexports = FStarC_Effect.op_Bang (mex eikind) in
              FStarC_Class_Setlike.mem ()
                (Obj.magic
                   (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
                (FStarC_Ident.string_of_id id1) (Obj.magic mexports) in
        let mincludes =
          let uu___ = FStarC_SMap.try_find env1.includes mname in
          match uu___ with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some minc ->
              let uu___2 = FStarC_Effect.op_Bang minc in
              FStarC_List.filter_map
                (fun uu___3 ->
                   match uu___3 with
                   | (ns1, restriction) ->
                       let opt =
                         FStarC_Syntax_Syntax.is_ident_allowed_by_restriction
                           id1 restriction in
                       FStarC_Option.map (fun id2 -> (ns1, id2)) opt) uu___2 in
        let look_into =
          if not_shadowed
          then let uu___ = qual modul id1 in find_in_module uu___
          else Cont_ignore in
        (match look_into with
         | Cont_ignore -> aux (FStarC_List.op_At mincludes q)
         | uu___ -> look_into) in
  aux [(ns, id)]
let try_lookup_id'' (env1 : env) (id : FStarC_Ident.ident)
  (eikind : exported_id_kind) (k_local_binding : local_binding -> 'a cont_t)
  (k_rec_binding : rec_binding -> 'a cont_t)
  (k_record : record_or_dc -> 'a cont_t)
  (find_in_module : FStarC_Ident.lident -> 'a cont_t)
  (lookup_default_id : 'a cont_t -> FStarC_Ident.ident -> 'a cont_t) :
  'a FStar_Pervasives_Native.option=
  let check_local_binding_id uu___ =
    match uu___ with
    | (id', uu___2, uu___3) ->
        (FStarC_Ident.string_of_id id') = (FStarC_Ident.string_of_id id) in
  let check_rec_binding_id uu___ =
    match uu___ with
    | (id', uu___2, uu___3) ->
        (FStarC_Ident.string_of_id id') = (FStarC_Ident.string_of_id id) in
  let curmod_ns =
    let uu___ = current_module env1 in FStarC_Ident.ids_of_lid uu___ in
  let proc uu___ =
    match uu___ with
    | Local_bindings lbs when
        FStar_Pervasives_Native.uu___is_Some
          (FStarC_PSMap.try_find lbs (FStarC_Ident.string_of_id id))
        ->
        let uu___2 = FStarC_PSMap.try_find lbs (FStarC_Ident.string_of_id id) in
        (match uu___2 with
         | FStar_Pervasives_Native.Some l ->
             let uu___3 = l in
             (match uu___3 with
              | (uu___4, uu___5, used_marker1) ->
                  (FStarC_Effect.op_Colon_Equals used_marker1 true;
                   k_local_binding l)))
    | Rec_binding r when check_rec_binding_id r ->
        let uu___2 = r in
        (match uu___2 with
         | (uu___3, uu___4, used_marker1) ->
             (FStarC_Effect.op_Colon_Equals used_marker1 true;
              k_rec_binding r))
    | Open_module_or_namespace
        ((ns, FStarC_Syntax_Syntax.Open_module, restriction), uu___2) ->
        let uu___3 =
          FStarC_Syntax_Syntax.is_ident_allowed_by_restriction id restriction in
        (match uu___3 with
         | FStar_Pervasives_Native.None -> Cont_ignore
         | FStar_Pervasives_Native.Some id1 ->
             find_in_module_with_includes eikind find_in_module Cont_ignore
               env1 ns id1)
    | Top_level_defs ids when
        FStar_Pervasives_Native.uu___is_Some
          (FStarC_PSMap.try_find ids (FStarC_Ident.string_of_id id))
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu___2 = FStarC_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid ->
             let id1 = FStarC_Ident.ident_of_lid lid in
             find_in_record (FStarC_Ident.ns_of_lid lid) id1 r k_record)
          Cont_ignore env1 uu___2 id
    | Record_or_dc r when is_exported_id_termtype eikind ->
        if
          FStarC_Ident.ident_equals (FStarC_Ident.ident_of_lid r.typename) id
        then k_record r
        else Cont_ignore
    | uu___2 -> Cont_ignore in
  let rec aux l =
    match l with
    | a1::q ->
        let uu___ = proc a1 in option_of_cont (fun uu___2 -> aux q) uu___
    | [] ->
        let uu___ = lookup_default_id Cont_fail id in
        option_of_cont (fun uu___2 -> FStar_Pervasives_Native.None) uu___ in
  aux env1.scope_mods
let found_local_binding (r : FStarC_Range_Type.range) (lb : local_binding) :
  FStarC_Syntax_Syntax.term=
  let uu___ = lb in match uu___ with | (id', x, uu___2) -> bv_to_name x r
let find_in_module (env1 : env) (lid : FStarC_Ident.lident)
  (k_global_def :
    FStarC_Ident.lident ->
      (FStarC_Syntax_Syntax.sigelt * Prims.bool) -> 'uuuuu)
  (k_not_found : 'uuuuu) : 'uuuuu=
  let uu___ =
    let uu___2 = sigmap env1 in
    FStarC_SMap.try_find uu___2 (FStarC_Ident.string_of_lid lid) in
  match uu___ with
  | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
  | FStar_Pervasives_Native.None -> k_not_found
let try_lookup_id (env1 : env) (id : FStarC_Ident.ident) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ = unmangleOpName id in
  match uu___ with
  | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
  | uu___2 ->
      try_lookup_id'' env1 id Exported_id_term_type
        (fun r ->
           let uu___3 = found_local_binding (FStarC_Ident.range_of_id id) r in
           Cont_ok uu___3) (fun uu___3 -> Cont_fail)
        (fun uu___3 -> Cont_ignore)
        (fun i ->
           find_in_module env1 i (fun uu___3 uu___4 -> Cont_fail) Cont_ignore)
        (fun uu___3 uu___4 -> Cont_fail)
let lookup_default_id (env1 : env) (id : FStarC_Ident.ident)
  (k_global_def :
    FStarC_Ident.lident ->
      (FStarC_Syntax_Syntax.sigelt * Prims.bool) -> 'a cont_t)
  (k_not_found : 'a cont_t) : 'a cont_t=
  let find_in_monad =
    match env1.curmonad with
    | FStar_Pervasives_Native.Some uu___ ->
        let lid = qualify env1 id in
        let uu___2 =
          let uu___3 = sigmap env1 in
          FStarC_SMap.try_find uu___3 (FStarC_Ident.string_of_lid lid) in
        (match uu___2 with
         | FStar_Pervasives_Native.Some r ->
             let uu___3 = k_global_def lid r in
             FStar_Pervasives_Native.Some uu___3
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  match find_in_monad with
  | FStar_Pervasives_Native.Some v -> v
  | FStar_Pervasives_Native.None ->
      let lid = let uu___ = current_module env1 in qual uu___ id in
      find_in_module env1 lid k_global_def k_not_found
let lid_is_curmod (env1 : env) (lid : FStarC_Ident.lident) : Prims.bool=
  match env1.curmodule with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some m -> FStarC_Ident.lid_equals lid m
let module_is_defined (env1 : env) (lid : FStarC_Ident.lident) : Prims.bool=
  let uu___ = lid_is_curmod env1 lid in
  if uu___
  then true
  else
    FStarC_List.existsb
      (fun x -> FStarC_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
      env1.modules
let resolve_module_name (env1 : env) (lid : FStarC_Ident.lident)
  (honor_ns : Prims.bool) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  let nslen = FStarC_List.length (FStarC_Ident.ns_of_lid lid) in
  let rec aux l =
    match l with
    | [] ->
        let uu___ = module_is_defined env1 lid in
        if uu___
        then FStar_Pervasives_Native.Some lid
        else FStar_Pervasives_Native.None
    | (Open_module_or_namespace
        ((ns, FStarC_Syntax_Syntax.Open_namespace, restriction), uu___))::q
        when honor_ns ->
        let new_lid =
          let uu___2 =
            let uu___3 = FStarC_Ident.path_of_lid ns in
            let uu___4 = FStarC_Ident.path_of_lid lid in
            FStarC_List.op_At uu___3 uu___4 in
          FStarC_Ident.lid_of_path uu___2 (FStarC_Ident.range_of_lid lid) in
        let uu___2 = module_is_defined env1 new_lid in
        if uu___2 then FStar_Pervasives_Native.Some new_lid else aux q
    | (Module_abbrev (name, modul))::uu___ when
        (nslen = Prims.int_zero) &&
          ((FStarC_Ident.string_of_id name) =
             (FStarC_Ident.string_of_id (FStarC_Ident.ident_of_lid lid)))
        -> FStar_Pervasives_Native.Some modul
    | uu___::q -> aux q in
  aux env1.scope_mods
let is_open (env1 : env) (lid : FStarC_Ident.lident)
  (open_kind : FStarC_Syntax_Syntax.open_kind) : Prims.bool=
  FStarC_List.existsb
    (fun uu___ ->
       match uu___ with
       | Open_module_or_namespace
           ((ns, k, FStarC_Syntax_Syntax.Unrestricted), uu___2) ->
           (k = open_kind) && (FStarC_Ident.lid_equals lid ns)
       | uu___2 -> false) env1.scope_mods
let namespace_is_open (env1 : env) (lid : FStarC_Ident.lident) : Prims.bool=
  is_open env1 lid FStarC_Syntax_Syntax.Open_namespace
let module_is_open (env1 : env) (lid : FStarC_Ident.lident) : Prims.bool=
  let uu___ = lid_is_curmod env1 lid in
  if uu___ then true else is_open env1 lid FStarC_Syntax_Syntax.Open_module
let shorten_module_path (env1 : env) (ids : FStarC_Ident.ident Prims.list)
  (is_full_path : Prims.bool) :
  (FStarC_Ident.ident Prims.list * FStarC_Ident.ident Prims.list)=
  let rec aux revns id =
    let lid = FStarC_Ident.lid_of_ns_and_id (FStarC_List.rev revns) id in
    let uu___ = namespace_is_open env1 lid in
    if uu___
    then FStar_Pervasives_Native.Some ((FStarC_List.rev (id :: revns)), [])
    else
      (match revns with
       | [] -> FStar_Pervasives_Native.None
       | ns_last_id::rev_ns_prefix ->
           let uu___3 = aux rev_ns_prefix ns_last_id in
           FStarC_Option.map
             (fun uu___4 ->
                match uu___4 with
                | (stripped_ids, rev_kept_ids) ->
                    (stripped_ids, (id :: rev_kept_ids))) uu___3) in
  let do_shorten env2 ids1 =
    match FStarC_List.rev ids1 with
    | [] -> ([], [])
    | ns_last_id::ns_rev_prefix ->
        let uu___ = aux ns_rev_prefix ns_last_id in
        (match uu___ with
         | FStar_Pervasives_Native.None -> ([], ids1)
         | FStar_Pervasives_Native.Some (stripped_ids, rev_kept_ids) ->
             (stripped_ids, (FStarC_List.rev rev_kept_ids))) in
  if is_full_path && ((FStarC_List.length ids) > Prims.int_zero)
  then
    let uu___ =
      let uu___2 = FStarC_Ident.lid_of_ids ids in
      resolve_module_name env1 uu___2 true in
    match uu___ with
    | FStar_Pervasives_Native.Some m when module_is_open env1 m -> (ids, [])
    | uu___2 -> do_shorten env1 ids
  else do_shorten env1 ids
let resolve_in_open_namespaces'' (env1 : env) (lid : FStarC_Ident.lident)
  (eikind : exported_id_kind) (k_local_binding : local_binding -> 'a cont_t)
  (k_rec_binding : rec_binding -> 'a cont_t)
  (k_record : record_or_dc -> 'a cont_t)
  (f_module : FStarC_Ident.lident -> 'a cont_t)
  (l_default : 'a cont_t -> FStarC_Ident.ident -> 'a cont_t) :
  'a FStar_Pervasives_Native.option=
  match FStarC_Ident.ns_of_lid lid with
  | uu___::uu___2 ->
      let uu___3 =
        let uu___4 =
          let uu___5 = FStarC_Ident.lid_of_ids (FStarC_Ident.ns_of_lid lid) in
          FStarC_Ident.set_lid_range uu___5 (FStarC_Ident.range_of_lid lid) in
        resolve_module_name env1 uu___4 true in
      (match uu___3 with
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
       | FStar_Pervasives_Native.Some modul ->
           let uu___4 =
             find_in_module_with_includes eikind f_module Cont_fail env1
               modul (FStarC_Ident.ident_of_lid lid) in
           option_of_cont (fun uu___5 -> FStar_Pervasives_Native.None) uu___4)
  | [] ->
      try_lookup_id'' env1 (FStarC_Ident.ident_of_lid lid) eikind
        k_local_binding k_rec_binding k_record f_module l_default
let cont_of_option (k_none : 'a cont_t)
  (uu___ : 'a FStar_Pervasives_Native.option) : 'a cont_t=
  match uu___ with
  | FStar_Pervasives_Native.Some v -> Cont_ok v
  | FStar_Pervasives_Native.None -> k_none
let resolve_in_open_namespaces' (env1 : env) (lid : FStarC_Ident.lident)
  (k_local_binding : local_binding -> 'a FStar_Pervasives_Native.option)
  (k_rec_binding : rec_binding -> 'a FStar_Pervasives_Native.option)
  (k_global_def :
    FStarC_Ident.lident ->
      (FStarC_Syntax_Syntax.sigelt * Prims.bool) ->
        'a FStar_Pervasives_Native.option)
  : 'a FStar_Pervasives_Native.option=
  let k_global_def' k lid1 def =
    let uu___ = k_global_def lid1 def in cont_of_option k uu___ in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env1 lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env1 i (k_global_def' k) k in
  resolve_in_open_namespaces'' env1 lid Exported_id_term_type
    (fun l -> let uu___ = k_local_binding l in cont_of_option Cont_fail uu___)
    (fun r -> let uu___ = k_rec_binding r in cont_of_option Cont_fail uu___)
    (fun uu___ -> Cont_ignore) f_module l_default
let fv_qual_of_se (se : FStarC_Syntax_Syntax.sigelt) :
  FStarC_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option=
  match se.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_datacon
      { FStarC_Syntax_Syntax.lid1 = uu___; FStarC_Syntax_Syntax.us1 = uu___2;
        FStarC_Syntax_Syntax.t1 = uu___3; FStarC_Syntax_Syntax.ty_lid = l;
        FStarC_Syntax_Syntax.num_ty_params = uu___4;
        FStarC_Syntax_Syntax.mutuals1 = uu___5;
        FStarC_Syntax_Syntax.injective_type_params1 = uu___6;
        FStarC_Syntax_Syntax.proj_disc_lids = uu___7;_}
      ->
      let qopt =
        FStarC_Util.find_map se.FStarC_Syntax_Syntax.sigquals
          (fun uu___8 ->
             match uu___8 with
             | FStarC_Syntax_Syntax.RecordConstructor (uu___9, fs) ->
                 FStar_Pervasives_Native.Some
                   (FStarC_Syntax_Syntax.Record_ctor (l, fs))
             | uu___9 -> FStar_Pervasives_Native.None) in
      (match qopt with
       | FStar_Pervasives_Native.None ->
           FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor
       | x -> x)
  | FStarC_Syntax_Syntax.Sig_declare_typ uu___ ->
      FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let lb_fv (lbs : FStarC_Syntax_Syntax.letbinding Prims.list)
  (lid : FStarC_Ident.lident) : FStarC_Syntax_Syntax.fv=
  let uu___ =
    FStarC_Util.find_map lbs
      (fun lb ->
         let fv =
           FStar_Pervasives.__proj__Inr__item__v
             lb.FStarC_Syntax_Syntax.lbname in
         if FStarC_Syntax_Syntax.fv_eq_lid fv lid
         then FStar_Pervasives_Native.Some fv
         else FStar_Pervasives_Native.None) in
  FStarC_Option.must uu___
let ns_of_lid_equals (lid : FStarC_Ident.lident) (ns : FStarC_Ident.lident) :
  Prims.bool=
  if
    (FStarC_List.length (FStarC_Ident.ns_of_lid lid)) =
      (FStarC_List.length (FStarC_Ident.ids_of_lid ns))
  then
    let uu___ = FStarC_Ident.lid_of_ids (FStarC_Ident.ns_of_lid lid) in
    FStarC_Ident.lid_equals uu___ ns
  else false
let try_lookup_name (any_val : Prims.bool) (exclude_interf : Prims.bool)
  (env1 : env) (lid : FStarC_Ident.lident) :
  foundname FStar_Pervasives_Native.option=
  let occurrence_range = FStarC_Ident.range_of_lid lid in
  let k_global_def source_lid uu___ =
    match uu___ with
    | (uu___2, true) when exclude_interf -> FStar_Pervasives_Native.None
    | (se, uu___2) ->
        (match se.FStarC_Syntax_Syntax.sigel with
         | FStarC_Syntax_Syntax.Sig_inductive_typ uu___3 ->
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   FStarC_Syntax_Syntax.fvar_with_dd source_lid
                     FStar_Pervasives_Native.None in
                 (uu___6, (se.FStarC_Syntax_Syntax.sigattrs)) in
               Term_name uu___5 in
             FStar_Pervasives_Native.Some uu___4
         | FStarC_Syntax_Syntax.Sig_datacon uu___3 ->
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   let uu___7 = fv_qual_of_se se in
                   FStarC_Syntax_Syntax.fvar_with_dd source_lid uu___7 in
                 (uu___6, (se.FStarC_Syntax_Syntax.sigattrs)) in
               Term_name uu___5 in
             FStar_Pervasives_Native.Some uu___4
         | FStarC_Syntax_Syntax.Sig_let
             { FStarC_Syntax_Syntax.lbs1 = (uu___3, lbs);
               FStarC_Syntax_Syntax.lids1 = uu___4;_}
             ->
             let fv = lb_fv lbs source_lid in
             let uu___5 =
               let uu___6 =
                 let uu___7 =
                   FStarC_Syntax_Syntax.fvar_with_dd source_lid
                     fv.FStarC_Syntax_Syntax.fv_qual in
                 (uu___7, (se.FStarC_Syntax_Syntax.sigattrs)) in
               Term_name uu___6 in
             FStar_Pervasives_Native.Some uu___5
         | FStarC_Syntax_Syntax.Sig_declare_typ
             { FStarC_Syntax_Syntax.lid2 = lid1;
               FStarC_Syntax_Syntax.us2 = uu___3;
               FStarC_Syntax_Syntax.t2 = uu___4;_}
             ->
             let quals = se.FStarC_Syntax_Syntax.sigquals in
             let is_assumption =
               FStarC_Util.for_some
                 (fun uu___5 ->
                    match uu___5 with
                    | FStarC_Syntax_Syntax.Assumption -> true
                    | uu___6 -> false) quals in
             if any_val || is_assumption
             then
               let lid2 =
                 FStarC_Ident.set_lid_range lid1
                   (FStarC_Ident.range_of_lid source_lid) in
               let uu___5 =
                 FStarC_Util.find_map quals
                   (fun uu___6 ->
                      match uu___6 with
                      | FStarC_Syntax_Syntax.Reflectable refl_monad ->
                          FStar_Pervasives_Native.Some refl_monad
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
                         (refl_const, (se.FStarC_Syntax_Syntax.sigattrs)))
                | uu___6 ->
                    let uu___7 =
                      let uu___8 =
                        let uu___9 =
                          let uu___10 = fv_qual_of_se se in
                          FStarC_Syntax_Syntax.fvar_with_dd lid2 uu___10 in
                        (uu___9, (se.FStarC_Syntax_Syntax.sigattrs)) in
                      Term_name uu___8 in
                    FStar_Pervasives_Native.Some uu___7)
             else FStar_Pervasives_Native.None
         | FStarC_Syntax_Syntax.Sig_new_effect ne ->
             FStar_Pervasives_Native.Some
               (Eff_name
                  (se,
                    (FStarC_Ident.set_lid_range ne.FStarC_Syntax_Syntax.mname
                       (FStarC_Ident.range_of_lid source_lid))))
         | FStarC_Syntax_Syntax.Sig_effect_abbrev uu___3 ->
             FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
         | FStarC_Syntax_Syntax.Sig_splice
             { FStarC_Syntax_Syntax.is_typed = uu___3;
               FStarC_Syntax_Syntax.lids2 = lids;
               FStarC_Syntax_Syntax.tac = t;_}
             ->
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   FStarC_Syntax_Syntax.fvar_with_dd source_lid
                     FStar_Pervasives_Native.None in
                 (uu___6, []) in
               Term_name uu___5 in
             FStar_Pervasives_Native.Some uu___4
         | uu___3 -> FStar_Pervasives_Native.None) in
  let k_local_binding r =
    let t = found_local_binding (FStarC_Ident.range_of_lid lid) r in
    FStar_Pervasives_Native.Some (Term_name (t, [])) in
  let k_rec_binding uu___ =
    match uu___ with
    | (id, l, used_marker1) ->
        (FStarC_Effect.op_Colon_Equals used_marker1 true;
         (let uu___3 =
            let uu___4 =
              let uu___5 =
                FStarC_Syntax_Syntax.fvar_with_dd
                  (FStarC_Ident.set_lid_range l
                     (FStarC_Ident.range_of_lid lid))
                  FStar_Pervasives_Native.None in
              (uu___5, []) in
            Term_name uu___4 in
          FStar_Pervasives_Native.Some uu___3)) in
  let found_unmangled =
    match FStarC_Ident.ns_of_lid lid with
    | [] ->
        let uu___ = unmangleOpName (FStarC_Ident.ident_of_lid lid) in
        (match uu___ with
         | FStar_Pervasives_Native.Some t ->
             FStar_Pervasives_Native.Some (Term_name (t, []))
         | uu___2 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  match found_unmangled with
  | FStar_Pervasives_Native.None ->
      resolve_in_open_namespaces' env1 lid k_local_binding k_rec_binding
        k_global_def
  | x -> x
let try_lookup_effect_name' (exclude_interf : Prims.bool) (env1 : env)
  (lid : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.sigelt * FStarC_Ident.lident)
    FStar_Pervasives_Native.option=
  let uu___ = try_lookup_name true exclude_interf env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some (Eff_name (o, l)) ->
      FStar_Pervasives_Native.Some (o, l)
  | uu___2 -> FStar_Pervasives_Native.None
let try_lookup_effect_name (env1 : env) (l : FStarC_Ident.lident) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  let uu___ = try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some (o, l1) -> FStar_Pervasives_Native.Some l1
  | uu___2 -> FStar_Pervasives_Native.None
let try_lookup_effect_name_and_attributes (env1 : env)
  (l : FStarC_Ident.lident) :
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.cflag Prims.list)
    FStar_Pervasives_Native.option=
  let uu___ = try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some
      ({ FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_new_effect ne;
         FStarC_Syntax_Syntax.sigrng = uu___2;
         FStarC_Syntax_Syntax.sigquals = uu___3;
         FStarC_Syntax_Syntax.sigmeta = uu___4;
         FStarC_Syntax_Syntax.sigattrs = uu___5;
         FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
         FStarC_Syntax_Syntax.sigopts = uu___7;_},
       l1)
      ->
      FStar_Pervasives_Native.Some
        (l1, (ne.FStarC_Syntax_Syntax.cattributes))
  | FStar_Pervasives_Native.Some
      ({
         FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_effect_abbrev
           { FStarC_Syntax_Syntax.lid4 = uu___2;
             FStarC_Syntax_Syntax.us4 = uu___3;
             FStarC_Syntax_Syntax.bs2 = uu___4;
             FStarC_Syntax_Syntax.comp1 = uu___5;
             FStarC_Syntax_Syntax.cflags = cattributes;_};
         FStarC_Syntax_Syntax.sigrng = uu___6;
         FStarC_Syntax_Syntax.sigquals = uu___7;
         FStarC_Syntax_Syntax.sigmeta = uu___8;
         FStarC_Syntax_Syntax.sigattrs = uu___9;
         FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___10;
         FStarC_Syntax_Syntax.sigopts = uu___11;_},
       l1)
      -> FStar_Pervasives_Native.Some (l1, cattributes)
  | uu___2 -> FStar_Pervasives_Native.None
let try_lookup_effect_defn (env1 : env) (l : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option=
  let uu___ = try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some
      ({ FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_new_effect ne;
         FStarC_Syntax_Syntax.sigrng = uu___2;
         FStarC_Syntax_Syntax.sigquals = uu___3;
         FStarC_Syntax_Syntax.sigmeta = uu___4;
         FStarC_Syntax_Syntax.sigattrs = uu___5;
         FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___6;
         FStarC_Syntax_Syntax.sigopts = uu___7;_},
       uu___8)
      -> FStar_Pervasives_Native.Some ne
  | uu___2 -> FStar_Pervasives_Native.None
let is_effect_name (env1 : env) (lid : FStarC_Ident.lident) : Prims.bool=
  let uu___ = try_lookup_effect_name env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some uu___2 -> true
let try_lookup_root_effect_name (env1 : env) (l : FStarC_Ident.lident) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  let uu___ = try_lookup_effect_name' (Prims.op_Negation env1.iface) env1 l in
  match uu___ with
  | FStar_Pervasives_Native.Some
      ({
         FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_effect_abbrev
           { FStarC_Syntax_Syntax.lid4 = l';
             FStarC_Syntax_Syntax.us4 = uu___2;
             FStarC_Syntax_Syntax.bs2 = uu___3;
             FStarC_Syntax_Syntax.comp1 = uu___4;
             FStarC_Syntax_Syntax.cflags = uu___5;_};
         FStarC_Syntax_Syntax.sigrng = uu___6;
         FStarC_Syntax_Syntax.sigquals = uu___7;
         FStarC_Syntax_Syntax.sigmeta = uu___8;
         FStarC_Syntax_Syntax.sigattrs = uu___9;
         FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___10;
         FStarC_Syntax_Syntax.sigopts = uu___11;_},
       uu___12)
      ->
      let rec aux new_name =
        let uu___13 =
          let uu___14 = sigmap env1 in
          FStarC_SMap.try_find uu___14 (FStarC_Ident.string_of_lid new_name) in
        match uu___13 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (s, uu___14) ->
            (match s.FStarC_Syntax_Syntax.sigel with
             | FStarC_Syntax_Syntax.Sig_new_effect ne ->
                 FStar_Pervasives_Native.Some
                   (FStarC_Ident.set_lid_range ne.FStarC_Syntax_Syntax.mname
                      (FStarC_Ident.range_of_lid l))
             | FStarC_Syntax_Syntax.Sig_effect_abbrev
                 { FStarC_Syntax_Syntax.lid4 = uu___15;
                   FStarC_Syntax_Syntax.us4 = uu___16;
                   FStarC_Syntax_Syntax.bs2 = uu___17;
                   FStarC_Syntax_Syntax.comp1 = cmp;
                   FStarC_Syntax_Syntax.cflags = uu___18;_}
                 ->
                 let l'' = FStarC_Syntax_Util.comp_effect_name cmp in aux l''
             | uu___15 -> FStar_Pervasives_Native.None) in
      aux l'
  | FStar_Pervasives_Native.Some (uu___2, l') ->
      FStar_Pervasives_Native.Some l'
  | uu___2 -> FStar_Pervasives_Native.None
let lookup_letbinding_quals_and_attrs (env1 : env)
  (lid : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.qualifier Prims.list * FStarC_Syntax_Syntax.attribute
    Prims.list)=
  let k_global_def lid1 uu___ =
    match uu___ with
    | ({
         FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_declare_typ
           uu___2;
         FStarC_Syntax_Syntax.sigrng = uu___3;
         FStarC_Syntax_Syntax.sigquals = quals;
         FStarC_Syntax_Syntax.sigmeta = uu___4;
         FStarC_Syntax_Syntax.sigattrs = attrs;
         FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___5;
         FStarC_Syntax_Syntax.sigopts = uu___6;_},
       uu___7) -> FStar_Pervasives_Native.Some (quals, attrs)
    | uu___2 -> FStar_Pervasives_Native.None in
  let uu___ =
    resolve_in_open_namespaces' env1 lid
      (fun uu___2 -> FStar_Pervasives_Native.None)
      (fun uu___2 -> FStar_Pervasives_Native.None) k_global_def in
  match uu___ with
  | FStar_Pervasives_Native.Some qa -> qa
  | uu___2 -> ([], [])
let try_lookup_module (env1 : env) (path : FStarC_Ident.path) :
  FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.tryFind
      (fun uu___2 ->
         match uu___2 with
         | (mlid, modul) ->
             let uu___3 = FStarC_Ident.path_of_lid mlid in uu___3 = path)
      env1.modules in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___2, modul) ->
      FStar_Pervasives_Native.Some modul
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let try_lookup_let (env1 : env) (lid : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let k_global_def lid1 uu___ =
    match uu___ with
    | ({
         FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_let
           { FStarC_Syntax_Syntax.lbs1 = (uu___2, lbs);
             FStarC_Syntax_Syntax.lids1 = uu___3;_};
         FStarC_Syntax_Syntax.sigrng = uu___4;
         FStarC_Syntax_Syntax.sigquals = uu___5;
         FStarC_Syntax_Syntax.sigmeta = uu___6;
         FStarC_Syntax_Syntax.sigattrs = uu___7;
         FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___8;
         FStarC_Syntax_Syntax.sigopts = uu___9;_},
       uu___10) ->
        let fv = lb_fv lbs lid1 in
        let uu___11 =
          FStarC_Syntax_Syntax.fvar_with_dd lid1
            fv.FStarC_Syntax_Syntax.fv_qual in
        FStar_Pervasives_Native.Some uu___11
    | uu___2 -> FStar_Pervasives_Native.None in
  resolve_in_open_namespaces' env1 lid
    (fun uu___ -> FStar_Pervasives_Native.None)
    (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let try_lookup_definition (env1 : env) (lid : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let k_global_def lid1 uu___ =
    match uu___ with
    | ({
         FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_let
           { FStarC_Syntax_Syntax.lbs1 = lbs;
             FStarC_Syntax_Syntax.lids1 = uu___2;_};
         FStarC_Syntax_Syntax.sigrng = uu___3;
         FStarC_Syntax_Syntax.sigquals = uu___4;
         FStarC_Syntax_Syntax.sigmeta = uu___5;
         FStarC_Syntax_Syntax.sigattrs = uu___6;
         FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
         FStarC_Syntax_Syntax.sigopts = uu___8;_},
       uu___9) ->
        FStarC_Util.find_map (FStar_Pervasives_Native.snd lbs)
          (fun lb ->
             match lb.FStarC_Syntax_Syntax.lbname with
             | FStar_Pervasives.Inr fv when
                 FStarC_Syntax_Syntax.fv_eq_lid fv lid1 ->
                 FStar_Pervasives_Native.Some (lb.FStarC_Syntax_Syntax.lbdef)
             | uu___10 -> FStar_Pervasives_Native.None)
    | uu___2 -> FStar_Pervasives_Native.None in
  resolve_in_open_namespaces' env1 lid
    (fun uu___ -> FStar_Pervasives_Native.None)
    (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let empty_include_smap :
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.restriction) Prims.list
    FStarC_Effect.ref FStarC_SMap.t=
  new_sigmap ()
let empty_exported_id_smap : exported_id_set FStarC_SMap.t= new_sigmap ()
let try_lookup_lid' (any_val : Prims.bool) (exclude_interface : Prims.bool)
  (env1 : env) (lid : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option=
  let uu___ = try_lookup_name any_val exclude_interface env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some (Term_name (e, attrs)) ->
      FStar_Pervasives_Native.Some (e, attrs)
  | uu___2 -> FStar_Pervasives_Native.None
let drop_attributes
  (x :
    (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.attribute Prims.list)
      FStar_Pervasives_Native.option)
  : FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match x with
  | FStar_Pervasives_Native.Some (t, uu___) -> FStar_Pervasives_Native.Some t
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let try_lookup_lid_with_attributes (env1 : env) (l : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option=
  try_lookup_lid' env1.iface false env1 l
let try_lookup_lid (env1 : env) (l : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ = try_lookup_lid_with_attributes env1 l in drop_attributes uu___
let resolve_to_fully_qualified_name (env1 : env) (l : FStarC_Ident.lident) :
  FStarC_Ident.lident FStar_Pervasives_Native.option=
  let r =
    let uu___ = try_lookup_name true false env1 l in
    match uu___ with
    | FStar_Pervasives_Native.Some (Term_name (e, attrs)) ->
        let uu___2 =
          let uu___3 = FStarC_Syntax_Subst.compress e in
          uu___3.FStarC_Syntax_Syntax.n in
        (match uu___2 with
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             FStar_Pervasives_Native.Some (fv.FStarC_Syntax_Syntax.fv_name)
         | uu___3 -> FStar_Pervasives_Native.None)
    | FStar_Pervasives_Native.Some (Eff_name (o, l1)) ->
        FStar_Pervasives_Native.Some l1
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  r
let is_abbrev (env1 : env) (lid : FStarC_Ident.lident) :
  FStarC_Ident.ipath FStar_Pervasives_Native.option=
  FStarC_List.tryPick
    (fun uu___ ->
       match uu___ with
       | Module_abbrev (id, ns) when FStarC_Ident.lid_equals lid ns ->
           FStar_Pervasives_Native.Some [id]
       | uu___2 -> FStar_Pervasives_Native.None) env1.scope_mods
let try_shorten_abbrev (env1 : env) (ns : FStarC_Ident.ipath) :
  (FStarC_Ident.ipath * FStarC_Ident.ident Prims.list)
    FStar_Pervasives_Native.option=
  let rec aux ns1 rest =
    match ns1 with
    | [] -> FStar_Pervasives_Native.None
    | hd::tl ->
        let uu___ =
          let uu___2 = FStarC_Ident.lid_of_ids (FStarC_List.rev ns1) in
          is_abbrev env1 uu___2 in
        (match uu___ with
         | FStar_Pervasives_Native.Some short ->
             FStar_Pervasives_Native.Some (short, rest)
         | uu___2 -> aux tl (hd :: rest)) in
  aux (FStarC_List.rev ns) []
let shorten_lid' (env1 : env) (lid0 : FStarC_Ident.lident) :
  FStarC_Ident.lident=
  let id0 = FStarC_Ident.ident_of_lid lid0 in
  let ns0 = FStarC_Ident.ns_of_lid lid0 in
  let uu___ =
    let uu___2 = try_shorten_abbrev env1 ns0 in
    match uu___2 with
    | FStar_Pervasives_Native.None -> ([], ns0)
    | FStar_Pervasives_Native.Some (ns, rest) -> (ns, rest) in
  match uu___ with
  | (pref, ns) ->
      let rec tails l =
        match l with | [] -> [[]] | uu___2::tl -> l :: (tails tl) in
      let suffs = FStarC_List.rev (tails ns) in
      let try1 lid' =
        let uu___2 = resolve_to_fully_qualified_name env1 lid' in
        match uu___2 with
        | FStar_Pervasives_Native.Some lid2 when
            FStarC_Ident.lid_equals lid2 lid0 -> true
        | uu___3 -> false in
      let rec go nss =
        match nss with
        | ns1::rest ->
            let lid' =
              FStarC_Ident.lid_of_ns_and_id (FStarC_List.op_At pref ns1) id0 in
            let uu___2 = try1 lid' in if uu___2 then lid' else go rest
        | [] -> lid0 in
      let r = go suffs in r
let shorten_lid (env1 : env) (lid0 : FStarC_Ident.lid) : FStarC_Ident.lid=
  match env1.curmodule with
  | FStar_Pervasives_Native.None -> lid0
  | uu___ -> shorten_lid' env1 lid0
let try_lookup_lid_with_attributes_no_resolve (env1 : env)
  (l : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option=
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
      iface_interleaving_init = (env1.iface_interleaving_init);
      syntax_only = (env1.syntax_only);
      ds_hooks = (env1.ds_hooks);
      dep_graph = (env1.dep_graph);
      no_prelude = (env1.no_prelude)
    } in
  try_lookup_lid_with_attributes env' l
let try_lookup_lid_no_resolve (env1 : env) (l : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ = try_lookup_lid_with_attributes_no_resolve env1 l in
  drop_attributes uu___
let try_lookup_datacon (env1 : env) (lid : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.sigelt)
    FStar_Pervasives_Native.option=
  let k_global_def lid1 uu___ =
    match uu___ with
    | (se, uu___2) ->
        (match se with
         | {
             FStarC_Syntax_Syntax.sigel =
               FStarC_Syntax_Syntax.Sig_declare_typ uu___3;
             FStarC_Syntax_Syntax.sigrng = uu___4;
             FStarC_Syntax_Syntax.sigquals = quals;
             FStarC_Syntax_Syntax.sigmeta = uu___5;
             FStarC_Syntax_Syntax.sigattrs = uu___6;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
             FStarC_Syntax_Syntax.sigopts = uu___8;_} ->
             let uu___9 =
               FStarC_Util.for_some
                 (fun uu___10 ->
                    match uu___10 with
                    | FStarC_Syntax_Syntax.Assumption -> true
                    | uu___11 -> false) quals in
             if uu___9
             then
               FStar_Pervasives_Native.Some
                 ((FStarC_Syntax_Syntax.lid_and_dd_as_fv lid1
                     FStar_Pervasives_Native.None), se)
             else FStar_Pervasives_Native.None
         | {
             FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_splice
               uu___3;
             FStarC_Syntax_Syntax.sigrng = uu___4;
             FStarC_Syntax_Syntax.sigquals = uu___5;
             FStarC_Syntax_Syntax.sigmeta = uu___6;
             FStarC_Syntax_Syntax.sigattrs = uu___7;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___8;
             FStarC_Syntax_Syntax.sigopts = uu___9;_} ->
             let qual1 = fv_qual_of_se se in
             FStar_Pervasives_Native.Some
               ((FStarC_Syntax_Syntax.lid_and_dd_as_fv lid1 qual1), se)
         | {
             FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
               uu___3;
             FStarC_Syntax_Syntax.sigrng = uu___4;
             FStarC_Syntax_Syntax.sigquals = uu___5;
             FStarC_Syntax_Syntax.sigmeta = uu___6;
             FStarC_Syntax_Syntax.sigattrs = uu___7;
             FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___8;
             FStarC_Syntax_Syntax.sigopts = uu___9;_} ->
             let qual1 = fv_qual_of_se se in
             FStar_Pervasives_Native.Some
               ((FStarC_Syntax_Syntax.lid_and_dd_as_fv lid1 qual1), se)
         | uu___3 -> FStar_Pervasives_Native.None) in
  resolve_in_open_namespaces' env1 lid
    (fun uu___ -> FStar_Pervasives_Native.None)
    (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let find_all_datacons (env1 : env) (lid : FStarC_Ident.lident) :
  FStarC_Ident.lident Prims.list FStar_Pervasives_Native.option=
  let k_global_def lid1 uu___ =
    match uu___ with
    | ({
         FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_inductive_typ
           { FStarC_Syntax_Syntax.lid = uu___2;
             FStarC_Syntax_Syntax.us = uu___3;
             FStarC_Syntax_Syntax.params = uu___4;
             FStarC_Syntax_Syntax.num_uniform_params = uu___5;
             FStarC_Syntax_Syntax.t = uu___6;
             FStarC_Syntax_Syntax.mutuals = datas;
             FStarC_Syntax_Syntax.ds = uu___7;
             FStarC_Syntax_Syntax.injective_type_params = uu___8;_};
         FStarC_Syntax_Syntax.sigrng = uu___9;
         FStarC_Syntax_Syntax.sigquals = uu___10;
         FStarC_Syntax_Syntax.sigmeta = uu___11;
         FStarC_Syntax_Syntax.sigattrs = uu___12;
         FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___13;
         FStarC_Syntax_Syntax.sigopts = uu___14;_},
       uu___15) -> FStar_Pervasives_Native.Some datas
    | uu___2 -> FStar_Pervasives_Native.None in
  resolve_in_open_namespaces' env1 lid
    (fun uu___ -> FStar_Pervasives_Native.None)
    (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit))=
  let record_cache = FStarC_Effect.mk_ref [[]] in
  let push uu___ =
    let uu___2 =
      let uu___3 =
        let uu___4 = FStarC_Effect.op_Bang record_cache in
        FStarC_List.hd uu___4 in
      let uu___4 = FStarC_Effect.op_Bang record_cache in uu___3 :: uu___4 in
    FStarC_Effect.op_Colon_Equals record_cache uu___2 in
  let pop uu___ =
    let uu___2 =
      let uu___3 = FStarC_Effect.op_Bang record_cache in
      FStarC_List.tl uu___3 in
    FStarC_Effect.op_Colon_Equals record_cache uu___2 in
  let snapshot uu___ =
    FStarC_Common.snapshot "DsEnv.record_cache" push record_cache () in
  let rollback depth =
    FStarC_Common.rollback "DsEnv.record_cache" pop record_cache depth in
  let peek uu___ =
    let uu___2 = FStarC_Effect.op_Bang record_cache in FStarC_List.hd uu___2 in
  let insert r =
    let uu___ =
      let uu___2 = let uu___3 = peek () in r :: uu___3 in
      let uu___3 =
        let uu___4 = FStarC_Effect.op_Bang record_cache in
        FStarC_List.tl uu___4 in
      uu___2 :: uu___3 in
    FStarC_Effect.op_Colon_Equals record_cache uu___ in
  let filter uu___ =
    let rc = peek () in
    let filtered =
      FStarC_List.filter (fun r -> Prims.op_Negation r.is_private) rc in
    let uu___2 =
      let uu___3 =
        let uu___4 = FStarC_Effect.op_Bang record_cache in
        FStarC_List.tl uu___4 in
      filtered :: uu___3 in
    FStarC_Effect.op_Colon_Equals record_cache uu___2 in
  let aux = ((push, pop), ((snapshot, rollback), (peek, insert))) in
  (aux, filter)
let record_cache_aux :
  (((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit))))=
  FStar_Pervasives_Native.fst record_cache_aux_with_filter
let filter_record_cache : unit -> unit=
  FStar_Pervasives_Native.snd record_cache_aux_with_filter
let push_record_cache : unit -> unit=
  FStar_Pervasives_Native.fst (FStar_Pervasives_Native.fst record_cache_aux)
let pop_record_cache : unit -> unit=
  FStar_Pervasives_Native.snd (FStar_Pervasives_Native.fst record_cache_aux)
let snapshot_record_cache : unit -> (Prims.int * unit)=
  FStar_Pervasives_Native.fst
    (FStar_Pervasives_Native.fst
       (FStar_Pervasives_Native.snd record_cache_aux))
let rollback_record_cache : Prims.int FStar_Pervasives_Native.option -> unit=
  FStar_Pervasives_Native.snd
    (FStar_Pervasives_Native.fst
       (FStar_Pervasives_Native.snd record_cache_aux))
let peek_record_cache : unit -> record_or_dc Prims.list=
  FStar_Pervasives_Native.fst
    (FStar_Pervasives_Native.snd
       (FStar_Pervasives_Native.snd record_cache_aux))
let insert_record_cache : record_or_dc -> unit=
  FStar_Pervasives_Native.snd
    (FStar_Pervasives_Native.snd
       (FStar_Pervasives_Native.snd record_cache_aux))
let extract_record (e : env)
  (new_globs : scope_mod Prims.list FStarC_Effect.ref)
  (se : FStarC_Syntax_Syntax.sigelt) : unit=
  match se.FStarC_Syntax_Syntax.sigel with
  | FStarC_Syntax_Syntax.Sig_bundle
      { FStarC_Syntax_Syntax.ses = sigs; FStarC_Syntax_Syntax.lids = uu___;_}
      ->
      let is_record =
        FStarC_Util.for_some
          (fun uu___2 ->
             match uu___2 with
             | FStarC_Syntax_Syntax.RecordType uu___3 -> true
             | FStarC_Syntax_Syntax.RecordConstructor uu___3 -> true
             | uu___3 -> false) in
      let find_dc dc =
        FStarC_Option.find
          (fun uu___2 ->
             match uu___2 with
             | {
                 FStarC_Syntax_Syntax.sigel =
                   FStarC_Syntax_Syntax.Sig_datacon
                   { FStarC_Syntax_Syntax.lid1 = lid;
                     FStarC_Syntax_Syntax.us1 = uu___3;
                     FStarC_Syntax_Syntax.t1 = uu___4;
                     FStarC_Syntax_Syntax.ty_lid = uu___5;
                     FStarC_Syntax_Syntax.num_ty_params = uu___6;
                     FStarC_Syntax_Syntax.mutuals1 = uu___7;
                     FStarC_Syntax_Syntax.injective_type_params1 = uu___8;
                     FStarC_Syntax_Syntax.proj_disc_lids = uu___9;_};
                 FStarC_Syntax_Syntax.sigrng = uu___10;
                 FStarC_Syntax_Syntax.sigquals = uu___11;
                 FStarC_Syntax_Syntax.sigmeta = uu___12;
                 FStarC_Syntax_Syntax.sigattrs = uu___13;
                 FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___14;
                 FStarC_Syntax_Syntax.sigopts = uu___15;_} ->
                 FStarC_Ident.lid_equals dc lid
             | uu___3 -> false) sigs in
      FStarC_List.iter
        (fun uu___2 ->
           match uu___2 with
           | {
               FStarC_Syntax_Syntax.sigel =
                 FStarC_Syntax_Syntax.Sig_inductive_typ
                 { FStarC_Syntax_Syntax.lid = typename;
                   FStarC_Syntax_Syntax.us = univs;
                   FStarC_Syntax_Syntax.params = parms;
                   FStarC_Syntax_Syntax.num_uniform_params = uu___3;
                   FStarC_Syntax_Syntax.t = uu___4;
                   FStarC_Syntax_Syntax.mutuals = uu___5;
                   FStarC_Syntax_Syntax.ds = dc::[];
                   FStarC_Syntax_Syntax.injective_type_params = uu___6;_};
               FStarC_Syntax_Syntax.sigrng = uu___7;
               FStarC_Syntax_Syntax.sigquals = typename_quals;
               FStarC_Syntax_Syntax.sigmeta = uu___8;
               FStarC_Syntax_Syntax.sigattrs = uu___9;
               FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___10;
               FStarC_Syntax_Syntax.sigopts = uu___11;_} ->
               let uu___12 =
                 let uu___13 = find_dc dc in FStarC_Option.must uu___13 in
               (match uu___12 with
                | {
                    FStarC_Syntax_Syntax.sigel =
                      FStarC_Syntax_Syntax.Sig_datacon
                      { FStarC_Syntax_Syntax.lid1 = constrname;
                        FStarC_Syntax_Syntax.us1 = uu___13;
                        FStarC_Syntax_Syntax.t1 = t;
                        FStarC_Syntax_Syntax.ty_lid = uu___14;
                        FStarC_Syntax_Syntax.num_ty_params = n;
                        FStarC_Syntax_Syntax.mutuals1 = uu___15;
                        FStarC_Syntax_Syntax.injective_type_params1 = uu___16;
                        FStarC_Syntax_Syntax.proj_disc_lids = uu___17;_};
                    FStarC_Syntax_Syntax.sigrng = uu___18;
                    FStarC_Syntax_Syntax.sigquals = uu___19;
                    FStarC_Syntax_Syntax.sigmeta = uu___20;
                    FStarC_Syntax_Syntax.sigattrs = uu___21;
                    FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___22;
                    FStarC_Syntax_Syntax.sigopts = uu___23;_} ->
                    let uu___24 = FStarC_Syntax_Util.arrow_formals t in
                    (match uu___24 with
                     | (all_formals, uu___25) ->
                         let uu___26 = FStarC_Util.first_N n all_formals in
                         (match uu___26 with
                          | (_params, formals) ->
                              let is_rec = is_record typename_quals in
                              let formals' =
                                FStarC_List.collect
                                  (fun f ->
                                     if
                                       (FStarC_Syntax_Syntax.is_null_bv
                                          f.FStarC_Syntax_Syntax.binder_bv)
                                         ||
                                         (is_rec &&
                                            (FStarC_Syntax_Syntax.is_bqual_implicit
                                               f.FStarC_Syntax_Syntax.binder_qual))
                                     then []
                                     else [f]) formals in
                              let fields' =
                                FStarC_List.map
                                  (fun f ->
                                     (((f.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname),
                                       ((f.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)))
                                  formals' in
                              let fields = fields' in
                              let record =
                                {
                                  typename;
                                  constrname =
                                    (FStarC_Ident.ident_of_lid constrname);
                                  parms;
                                  fields;
                                  is_private =
                                    (FStarC_List.contains
                                       FStarC_Syntax_Syntax.Private
                                       typename_quals);
                                  is_record = is_rec
                                } in
                              ((let uu___28 =
                                  let uu___29 =
                                    FStarC_Effect.op_Bang new_globs in
                                  (Record_or_dc record) :: uu___29 in
                                FStarC_Effect.op_Colon_Equals new_globs
                                  uu___28);
                               (match () with
                                | () ->
                                    ((let add_field uu___29 =
                                        match uu___29 with
                                        | (id, uu___30) ->
                                            let modul =
                                              let uu___31 =
                                                FStarC_Ident.lid_of_ids
                                                  (FStarC_Ident.ns_of_lid
                                                     constrname) in
                                              FStarC_Ident.string_of_lid
                                                uu___31 in
                                            let uu___31 =
                                              get_exported_id_set e modul in
                                            (match uu___31 with
                                             | FStar_Pervasives_Native.Some
                                                 my_ex ->
                                                 let my_exported_ids =
                                                   my_ex Exported_id_field in
                                                 ((let uu___33 =
                                                     let uu___34 =
                                                       FStarC_Effect.op_Bang
                                                         my_exported_ids in
                                                     Obj.magic
                                                       (FStarC_Class_Setlike.add
                                                          ()
                                                          (Obj.magic
                                                             (FStarC_RBSet.setlike_rbset
                                                                FStarC_Class_Ord.ord_string))
                                                          (FStarC_Ident.string_of_id
                                                             id)
                                                          (Obj.magic uu___34)) in
                                                   FStarC_Effect.op_Colon_Equals
                                                     my_exported_ids uu___33);
                                                  (match () with
                                                   | () ->
                                                       let projname =
                                                         let uu___33 =
                                                           let uu___34 =
                                                             FStarC_Syntax_Util.mk_field_projector_name_from_ident
                                                               constrname id in
                                                           FStarC_Ident.ident_of_lid
                                                             uu___34 in
                                                         FStarC_Ident.string_of_id
                                                           uu___33 in
                                                       let uu___34 =
                                                         let uu___35 =
                                                           FStarC_Effect.op_Bang
                                                             my_exported_ids in
                                                         Obj.magic
                                                           (FStarC_Class_Setlike.add
                                                              ()
                                                              (Obj.magic
                                                                 (FStarC_RBSet.setlike_rbset
                                                                    FStarC_Class_Ord.ord_string))
                                                              projname
                                                              (Obj.magic
                                                                 uu___35)) in
                                                       FStarC_Effect.op_Colon_Equals
                                                         my_exported_ids
                                                         uu___34))
                                             | FStar_Pervasives_Native.None
                                                 -> ()) in
                                      FStarC_List.iter add_field fields');
                                     (match () with
                                      | () -> insert_record_cache record))))))
                | uu___13 -> ())
           | uu___3 -> ()) sigs
  | uu___ -> ()
let try_lookup_record_or_dc_by_field_name (env1 : env)
  (fieldname : FStarC_Ident.lident) :
  record_or_dc FStar_Pervasives_Native.option=
  let find_in_cache fieldname1 =
    let uu___ =
      ((FStarC_Ident.ns_of_lid fieldname1),
        (FStarC_Ident.ident_of_lid fieldname1)) in
    match uu___ with
    | (ns, id) ->
        let uu___2 = peek_record_cache () in
        FStarC_Util.find_map uu___2
          (fun record ->
             let uu___3 = find_in_record ns id record (fun r -> Cont_ok r) in
             option_of_cont (fun uu___4 -> FStar_Pervasives_Native.None)
               uu___3) in
  resolve_in_open_namespaces'' env1 fieldname Exported_id_field
    (fun uu___ -> Cont_ignore) (fun uu___ -> Cont_ignore)
    (fun r -> Cont_ok r)
    (fun fn ->
       let uu___ = find_in_cache fn in cont_of_option Cont_ignore uu___)
    (fun k uu___ -> k)
let try_lookup_record_or_dc_by_field_name_many (env1 : env)
  (fieldnames : FStarC_Ident.lident Prims.list) :
  record_or_dc FStar_Pervasives_Native.option=
  match fieldnames with
  | [] -> FStar_Pervasives_Native.None
  | fn::uu___ ->
      let all_ids = FStarC_List.map FStarC_Ident.ident_of_lid fieldnames in
      let find_in_cache fieldname =
        let uu___2 =
          ((FStarC_Ident.ns_of_lid fieldname),
            (FStarC_Ident.ident_of_lid fieldname)) in
        match uu___2 with
        | (ns, id) ->
            let uu___3 = peek_record_cache () in
            FStarC_Util.find_map uu___3
              (fun record ->
                 let uu___4 =
                   find_in_record ns id record
                     (fun r ->
                        find_in_record_many all_ids record
                          (fun r1 -> Cont_ok r1)) in
                 option_of_cont (fun uu___5 -> FStar_Pervasives_Native.None)
                   uu___4) in
      resolve_in_open_namespaces'' env1 fn Exported_id_field
        (fun uu___2 -> Cont_ignore) (fun uu___2 -> Cont_ignore)
        (fun r -> find_in_record_many all_ids r (fun r1 -> Cont_ok r1))
        (fun fn1 ->
           let uu___2 = find_in_cache fn1 in
           cont_of_option Cont_ignore uu___2) (fun k uu___2 -> k)
let try_lookup_record_by_field_name (env1 : env)
  (fieldname : FStarC_Ident.lident) :
  record_or_dc FStar_Pervasives_Native.option=
  let uu___ = try_lookup_record_or_dc_by_field_name env1 fieldname in
  match uu___ with
  | FStar_Pervasives_Native.Some r when r.is_record ->
      FStar_Pervasives_Native.Some r
  | uu___2 -> FStar_Pervasives_Native.None
let try_lookup_record_by_field_name_many (env1 : env)
  (fieldnames : FStarC_Ident.lident Prims.list) :
  record_or_dc FStar_Pervasives_Native.option=
  let uu___ = try_lookup_record_or_dc_by_field_name_many env1 fieldnames in
  match uu___ with
  | FStar_Pervasives_Native.Some r when r.is_record ->
      FStar_Pervasives_Native.Some r
  | uu___2 ->
      (match fieldnames with
       | [] -> FStar_Pervasives_Native.None
       | fn::uu___3 -> try_lookup_record_by_field_name env1 fn)
let try_lookup_record_type (env1 : env) (typename : FStarC_Ident.lident) :
  record_or_dc FStar_Pervasives_Native.option=
  let find_in_cache name =
    let uu___ =
      ((FStarC_Ident.ns_of_lid name), (FStarC_Ident.ident_of_lid name)) in
    match uu___ with
    | (ns, id) ->
        let uu___2 = peek_record_cache () in
        FStarC_Util.find_map uu___2
          (fun record ->
             if
               FStarC_Ident.ident_equals
                 (FStarC_Ident.ident_of_lid record.typename) id
             then FStar_Pervasives_Native.Some record
             else FStar_Pervasives_Native.None) in
  resolve_in_open_namespaces'' env1 typename Exported_id_term_type
    (fun uu___ -> Cont_ignore) (fun uu___ -> Cont_ignore)
    (fun r -> Cont_ok r)
    (fun l -> let uu___ = find_in_cache l in cont_of_option Cont_ignore uu___)
    (fun k uu___ -> k)
let belongs_to_record (env1 : env) (lid : FStarC_Ident.lident)
  (record : record_or_dc) : Prims.bool=
  let uu___ = try_lookup_record_by_field_name env1 lid in
  match uu___ with
  | FStar_Pervasives_Native.Some record' when
      (FStarC_Ident.nsstr record.typename) =
        (FStarC_Ident.nsstr record'.typename)
      ->
      let uu___2 =
        find_in_record (FStarC_Ident.ns_of_lid record.typename)
          (FStarC_Ident.ident_of_lid lid) record (fun uu___3 -> Cont_ok ()) in
      (match uu___2 with | Cont_ok uu___3 -> true | uu___3 -> false)
  | uu___2 -> false
let try_lookup_dc_by_field_name (env1 : env)
  (fieldname : FStarC_Ident.lident) :
  (FStarC_Ident.lident * Prims.bool) FStar_Pervasives_Native.option=
  let uu___ = try_lookup_record_or_dc_by_field_name env1 fieldname in
  match uu___ with
  | FStar_Pervasives_Native.Some r ->
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_Ident.lid_of_ids
              (FStarC_List.op_At (FStarC_Ident.ns_of_lid r.typename)
                 [r.constrname]) in
          FStarC_Ident.set_lid_range uu___4
            (FStarC_Ident.range_of_lid fieldname) in
        (uu___3, (r.is_record)) in
      FStar_Pervasives_Native.Some uu___2
  | uu___2 -> FStar_Pervasives_Native.None
let string_set_ref_new (uu___ : unit) : string_set FStarC_Effect.ref=
  let uu___2 =
    Obj.magic
      (FStarC_Class_Setlike.empty ()
         (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
         ()) in
  FStarC_Effect.mk_ref uu___2
let exported_id_set_new (uu___ : unit) :
  exported_id_kind -> string_set FStarC_Effect.ref=
  let term_type_set = string_set_ref_new () in
  let field_set = string_set_ref_new () in
  fun uu___2 ->
    match uu___2 with
    | Exported_id_term_type -> term_type_set
    | Exported_id_field -> field_set
let unique (any_val : Prims.bool) (exclude_interface : Prims.bool)
  (env1 : env) (lid : FStarC_Ident.lident) : Prims.bool=
  let filter_scope_mods uu___ =
    match uu___ with | Rec_binding uu___2 -> true | uu___2 -> false in
  let this_env =
    let uu___ = FStarC_List.filter filter_scope_mods env1.scope_mods in
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
      iface_interleaving_init = (env1.iface_interleaving_init);
      syntax_only = (env1.syntax_only);
      ds_hooks = (env1.ds_hooks);
      dep_graph = (env1.dep_graph);
      no_prelude = (env1.no_prelude)
    } in
  let uu___ = try_lookup_lid' any_val exclude_interface this_env lid in
  match uu___ with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some uu___2 -> false
let push_scope_mod (env1 : env) (scope_mod1 : scope_mod) : env=
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
    iface_interleaving_init = (env1.iface_interleaving_init);
    syntax_only = (env1.syntax_only);
    ds_hooks = (env1.ds_hooks);
    dep_graph = (env1.dep_graph);
    no_prelude = (env1.no_prelude)
  }
let push_bv' (env1 : env) (x : FStarC_Ident.ident) :
  (env * FStarC_Syntax_Syntax.bv * used_marker)=
  let r = FStarC_Ident.range_of_id x in
  let bv =
    FStarC_Syntax_Syntax.gen_bv (FStarC_Ident.string_of_id x)
      (FStar_Pervasives_Native.Some r)
      {
        FStarC_Syntax_Syntax.n =
          (FStarC_Syntax_Syntax.tun.FStarC_Syntax_Syntax.n);
        FStarC_Syntax_Syntax.pos = r;
        FStarC_Syntax_Syntax.vars =
          (FStarC_Syntax_Syntax.tun.FStarC_Syntax_Syntax.vars);
        FStarC_Syntax_Syntax.hash_code =
          (FStarC_Syntax_Syntax.tun.FStarC_Syntax_Syntax.hash_code)
      } in
  let used_marker1 = FStarC_Effect.mk_ref false in
  let scope_mods =
    match env1.scope_mods with
    | (Local_bindings lbs)::rest ->
        (Local_bindings
           (FStarC_PSMap.add lbs (FStarC_Ident.string_of_id x)
              (x, bv, used_marker1)))
        :: rest
    | uu___ ->
        (Local_bindings
           (FStarC_PSMap.add (FStarC_PSMap.empty ())
              (FStarC_Ident.string_of_id x) (x, bv, used_marker1)))
        :: (env1.scope_mods) in
  ({
     curmodule = (env1.curmodule);
     curmonad = (env1.curmonad);
     modules = (env1.modules);
     scope_mods;
     exported_ids = (env1.exported_ids);
     trans_exported_ids = (env1.trans_exported_ids);
     includes = (env1.includes);
     sigaccum = (env1.sigaccum);
     sigmap = (env1.sigmap);
     iface = (env1.iface);
     admitted_iface = (env1.admitted_iface);
     expect_typ = (env1.expect_typ);
     remaining_iface_decls = (env1.remaining_iface_decls);
     iface_interleaving_init = (env1.iface_interleaving_init);
     syntax_only = (env1.syntax_only);
     ds_hooks = (env1.ds_hooks);
     dep_graph = (env1.dep_graph);
     no_prelude = (env1.no_prelude)
   }, bv, used_marker1)
let push_bv (env1 : env) (x : FStarC_Ident.ident) :
  (env * FStarC_Syntax_Syntax.bv)=
  let uu___ = push_bv' env1 x in
  match uu___ with | (env2, bv, uu___2) -> (env2, bv)
let push_top_level_rec_binding (env0 : env) (x : FStarC_Ident.ident) :
  (env * Prims.bool FStarC_Effect.ref)=
  let l = qualify env0 x in
  let uu___ =
    let uu___2 = unique false true env0 l in
    if uu___2 then true else FStarC_Options.interactive () in
  if uu___
  then
    let used_marker1 = FStarC_Effect.mk_ref false in
    let uu___2 = push_scope_mod env0 (Rec_binding (x, l, used_marker1)) in
    (uu___2, used_marker1)
  else
    FStarC_Errors.raise_error FStarC_Ident.hasrange_lident l
      FStarC_Errors_Codes.Fatal_DuplicateTopLevelNames ()
      (Obj.magic FStarC_Errors_Msg.is_error_message_string)
      (Obj.magic
         (Prims.strcat "Duplicate top-level names "
            (FStarC_Ident.string_of_lid l)))
let push_sigelt' (fail_on_dup : Prims.bool) (env1 : env)
  (s : FStarC_Syntax_Syntax.sigelt) : env=
  let err l =
    let sopt =
      let uu___ = sigmap env1 in
      FStarC_SMap.try_find uu___ (FStarC_Ident.string_of_lid l) in
    let r =
      match sopt with
      | FStar_Pervasives_Native.Some (se, uu___) ->
          let uu___2 =
            FStarC_Option.find (FStarC_Ident.lid_equals l)
              (FStarC_Syntax_Util.lids_of_sigelt se) in
          (match uu___2 with
           | FStar_Pervasives_Native.Some l1 ->
               FStarC_Range_Ops.string_of_range
                 (FStarC_Ident.range_of_lid l1)
           | FStar_Pervasives_Native.None -> "<unknown>")
      | FStar_Pervasives_Native.None -> "<unknown>" in
    FStarC_Errors.raise_error FStarC_Ident.hasrange_lident l
      FStarC_Errors_Codes.Fatal_DuplicateTopLevelNames ()
      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
      (Obj.magic
         [FStarC_Errors_Msg.text
            (FStarC_Format.fmt1 "Duplicate top-level names [%s]"
               (FStarC_Ident.string_of_lid l));
         FStarC_Errors_Msg.text
           (FStarC_Format.fmt1 "Previously declared at %s" r)]) in
  let globals = FStarC_Effect.mk_ref env1.scope_mods in
  let env2 =
    let exclude_interface =
      match s.FStarC_Syntax_Syntax.sigel with
      | FStarC_Syntax_Syntax.Sig_let uu___ -> true
      | FStarC_Syntax_Syntax.Sig_bundle uu___ -> true
      | uu___ -> false in
    let lids = FStarC_Syntax_Util.lids_of_sigelt s in
    let lids1 =
      FStarC_List.filter
        (fun lid ->
           let uu___ =
             let uu___2 =
               FStarC_Class_Show.show FStarC_Ident.showable_ident
                 (FStarC_Ident.ident_of_lid lid) in
             FStarC_Util.starts_with uu___2 "uu___is_" in
           Prims.op_Negation uu___) lids in
    let lids2 =
      FStarC_List.filter
        (fun lid ->
           let uu___ =
             let uu___2 =
               FStarC_Class_Show.show FStarC_Ident.showable_ident
                 (FStarC_Ident.ident_of_lid lid) in
             FStarC_Util.starts_with uu___2 "__proj__" in
           Prims.op_Negation uu___) lids1 in
    if fail_on_dup
    then
      (let uu___2 =
         FStarC_Util.find_map lids2
           (fun l ->
              let uu___3 =
                let uu___4 = unique false exclude_interface env1 l in
                Prims.op_Negation uu___4 in
              if uu___3
              then FStar_Pervasives_Native.Some l
              else FStar_Pervasives_Native.None) in
       match uu___2 with
       | FStar_Pervasives_Native.Some l -> err l
       | uu___3 -> ())
    else ();
    extract_record env1 globals s;
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
      iface_interleaving_init = (env1.iface_interleaving_init);
      syntax_only = (env1.syntax_only);
      ds_hooks = (env1.ds_hooks);
      dep_graph = (env1.dep_graph);
      no_prelude = (env1.no_prelude)
    } in
  let env3 =
    let uu___ = FStarC_Effect.op_Bang globals in
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
      iface_interleaving_init = (env2.iface_interleaving_init);
      syntax_only = (env2.syntax_only);
      ds_hooks = (env2.ds_hooks);
      dep_graph = (env2.dep_graph);
      no_prelude = (env2.no_prelude)
    } in
  let lss =
    match s.FStarC_Syntax_Syntax.sigel with
    | FStarC_Syntax_Syntax.Sig_bundle
        { FStarC_Syntax_Syntax.ses = ses;
          FStarC_Syntax_Syntax.lids = uu___;_}
        ->
        FStarC_List.map
          (fun se -> ((FStarC_Syntax_Util.lids_of_sigelt se), se)) ses
    | uu___ -> [((FStarC_Syntax_Util.lids_of_sigelt s), s)] in
  let push_top_level_def id stack =
    match stack with
    | (Top_level_defs ids)::rest ->
        (Top_level_defs
           (FStarC_PSMap.add ids (FStarC_Ident.string_of_id id) ()))
        :: rest
    | uu___ ->
        (Top_level_defs
           (FStarC_PSMap.add (FStarC_PSMap.empty ())
              (FStarC_Ident.string_of_id id) ()))
        :: stack in
  let add1 lid se =
    (let uu___2 =
       let uu___3 = FStarC_Effect.op_Bang globals in
       push_top_level_def (FStarC_Ident.ident_of_lid lid) uu___3 in
     FStarC_Effect.op_Colon_Equals globals uu___2);
    (match () with
     | () ->
         let modul =
           let uu___2 = FStarC_Ident.lid_of_ids (FStarC_Ident.ns_of_lid lid) in
           FStarC_Ident.string_of_lid uu___2 in
         ((let uu___3 = get_exported_id_set env3 modul in
           match uu___3 with
           | FStar_Pervasives_Native.Some f ->
               let my_exported_ids = f Exported_id_term_type in
               let uu___4 =
                 let uu___5 = FStarC_Effect.op_Bang my_exported_ids in
                 Obj.magic
                   (FStarC_Class_Setlike.add ()
                      (Obj.magic
                         (FStarC_RBSet.setlike_rbset
                            FStarC_Class_Ord.ord_string))
                      (FStarC_Ident.string_of_id
                         (FStarC_Ident.ident_of_lid lid)) (Obj.magic uu___5)) in
               FStarC_Effect.op_Colon_Equals my_exported_ids uu___4
           | FStar_Pervasives_Native.None -> ());
          (match () with
           | () ->
               let is_iface =
                 env3.iface && (Prims.op_Negation env3.admitted_iface) in
               let uu___4 = sigmap env3 in
               FStarC_SMap.add uu___4 (FStarC_Ident.string_of_lid lid)
                 (se,
                   (env3.iface && (Prims.op_Negation env3.admitted_iface)))))) in
  FStarC_List.iter
    (fun uu___2 ->
       match uu___2 with
       | (lids, se) ->
           let dummysig l =
             let se1 =
               FStarC_Syntax_Syntax.mk_sigelt
                 (FStarC_Syntax_Syntax.Sig_declare_typ
                    {
                      FStarC_Syntax_Syntax.lid2 = l;
                      FStarC_Syntax_Syntax.us2 = [];
                      FStarC_Syntax_Syntax.t2 = FStarC_Syntax_Syntax.tun
                    }) in
             {
               FStarC_Syntax_Syntax.sigel = (se1.FStarC_Syntax_Syntax.sigel);
               FStarC_Syntax_Syntax.sigrng =
                 (se1.FStarC_Syntax_Syntax.sigrng);
               FStarC_Syntax_Syntax.sigquals =
                 [FStarC_Syntax_Syntax.Assumption];
               FStarC_Syntax_Syntax.sigmeta =
                 (se1.FStarC_Syntax_Syntax.sigmeta);
               FStarC_Syntax_Syntax.sigattrs =
                 (se1.FStarC_Syntax_Syntax.sigattrs);
               FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                 (se1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
               FStarC_Syntax_Syntax.sigopts =
                 (se1.FStarC_Syntax_Syntax.sigopts)
             } in
           (FStarC_List.iter (fun lid -> add1 lid se) lids;
            (match se.FStarC_Syntax_Syntax.sigel with
             | FStarC_Syntax_Syntax.Sig_datacon
                 { FStarC_Syntax_Syntax.lid1 = lid;
                   FStarC_Syntax_Syntax.us1 = uu___5;
                   FStarC_Syntax_Syntax.t1 = uu___6;
                   FStarC_Syntax_Syntax.ty_lid = uu___7;
                   FStarC_Syntax_Syntax.num_ty_params = uu___8;
                   FStarC_Syntax_Syntax.mutuals1 = uu___9;
                   FStarC_Syntax_Syntax.injective_type_params1 = uu___10;
                   FStarC_Syntax_Syntax.proj_disc_lids = proj_disc_lids;_}
                 ->
                 FStarC_List.iter (fun lid1 -> add1 lid1 (dummysig lid1))
                   proj_disc_lids
             | uu___5 -> ()))) lss;
  (let env4 =
     let uu___2 = FStarC_Effect.op_Bang globals in
     {
       curmodule = (env3.curmodule);
       curmonad = (env3.curmonad);
       modules = (env3.modules);
       scope_mods = uu___2;
       exported_ids = (env3.exported_ids);
       trans_exported_ids = (env3.trans_exported_ids);
       includes = (env3.includes);
       sigaccum = (env3.sigaccum);
       sigmap = (env3.sigmap);
       iface = (env3.iface);
       admitted_iface = (env3.admitted_iface);
       expect_typ = (env3.expect_typ);
       remaining_iface_decls = (env3.remaining_iface_decls);
       iface_interleaving_init = (env3.iface_interleaving_init);
       syntax_only = (env3.syntax_only);
       ds_hooks = (env3.ds_hooks);
       dep_graph = (env3.dep_graph);
       no_prelude = (env3.no_prelude)
     } in
   env4)
let push_sigelt (env1 : env) (se : FStarC_Syntax_Syntax.sigelt) : env=
  push_sigelt' true env1 se
let push_sigelt_force (env1 : env) (se : FStarC_Syntax_Syntax.sigelt) : 
  env= push_sigelt' false env1 se
let find_data_constructors_for_typ (env1 : env) (lid : FStarC_Ident.lident) :
  FStarC_Ident.lident Prims.list FStar_Pervasives_Native.option=
  let k_global_def lid1 uu___ =
    match uu___ with
    | ({
         FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_inductive_typ
           { FStarC_Syntax_Syntax.lid = uu___2;
             FStarC_Syntax_Syntax.us = uu___3;
             FStarC_Syntax_Syntax.params = uu___4;
             FStarC_Syntax_Syntax.num_uniform_params = uu___5;
             FStarC_Syntax_Syntax.t = uu___6;
             FStarC_Syntax_Syntax.mutuals = uu___7;
             FStarC_Syntax_Syntax.ds = ds;
             FStarC_Syntax_Syntax.injective_type_params = uu___8;_};
         FStarC_Syntax_Syntax.sigrng = uu___9;
         FStarC_Syntax_Syntax.sigquals = uu___10;
         FStarC_Syntax_Syntax.sigmeta = uu___11;
         FStarC_Syntax_Syntax.sigattrs = uu___12;
         FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___13;
         FStarC_Syntax_Syntax.sigopts = uu___14;_},
       uu___15) -> FStar_Pervasives_Native.Some ds
    | uu___2 -> FStar_Pervasives_Native.None in
  resolve_in_open_namespaces' env1 lid
    (fun uu___ -> FStar_Pervasives_Native.None)
    (fun uu___ -> FStar_Pervasives_Native.None) k_global_def
let find_binders_for_datacons :
  env ->
    FStarC_Ident.lident ->
      FStarC_Ident.ident Prims.list FStar_Pervasives_Native.option=
  let debug = FStarC_Debug.get_toggle "open_include_restrictions" in
  fun env1 lid ->
    let ns = FStarC_Ident.ns_of_lid lid in
    let k_global_def lid1 uu___ =
      match uu___ with
      | ({
           FStarC_Syntax_Syntax.sigel = FStarC_Syntax_Syntax.Sig_datacon
             { FStarC_Syntax_Syntax.lid1 = uu___2;
               FStarC_Syntax_Syntax.us1 = uu___3;
               FStarC_Syntax_Syntax.t1 = t;
               FStarC_Syntax_Syntax.ty_lid = uu___4;
               FStarC_Syntax_Syntax.num_ty_params = num_ty_params;
               FStarC_Syntax_Syntax.mutuals1 = uu___5;
               FStarC_Syntax_Syntax.injective_type_params1 = uu___6;
               FStarC_Syntax_Syntax.proj_disc_lids = uu___7;_};
           FStarC_Syntax_Syntax.sigrng = uu___8;
           FStarC_Syntax_Syntax.sigquals = uu___9;
           FStarC_Syntax_Syntax.sigmeta = uu___10;
           FStarC_Syntax_Syntax.sigattrs = uu___11;
           FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___12;
           FStarC_Syntax_Syntax.sigopts = uu___13;_},
         uu___14) ->
          let uu___15 =
            let uu___16 =
              let uu___17 =
                let uu___18 =
                  let uu___19 = FStarC_Syntax_Util.arrow_formals_comp_ln t in
                  FStar_Pervasives_Native.fst uu___19 in
                FStarC_List.splitAt num_ty_params uu___18 in
              FStar_Pervasives_Native.snd uu___17 in
            FStarC_List.map
              (fun x ->
                 (x.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname)
              uu___16 in
          FStar_Pervasives_Native.Some uu___15
      | uu___2 -> FStar_Pervasives_Native.None in
    let result =
      resolve_in_open_namespaces' env1 lid
        (fun uu___ -> FStar_Pervasives_Native.None)
        (fun uu___ -> FStar_Pervasives_Native.None) k_global_def in
    (let uu___2 = FStarC_Effect.op_Bang debug in
     if uu___2
     then
       let uu___3 =
         let uu___4 =
           let uu___5 =
             FStarC_Class_Show.show FStarC_Ident.showable_lident lid in
           let uu___6 =
             let uu___7 =
               let uu___8 =
                 FStarC_Class_Show.show
                   (FStarC_Class_Show.show_option
                      (FStarC_Class_Show.show_list
                         FStarC_Ident.showable_ident)) result in
               Prims.strcat uu___8 "\n" in
             Prims.strcat ") = " uu___7 in
           Prims.strcat uu___5 uu___6 in
         Prims.strcat "find_binders_for_datacons(_, " uu___4 in
       FStarC_Format.print_string uu___3
     else ());
    result
let elab_restriction
  (f : env -> FStarC_Ident.lident -> FStarC_Syntax_Syntax.restriction -> env)
  (env1 : env) (ns : FStarC_Ident.lident)
  (restriction : FStarC_Syntax_Syntax.restriction) : env=
  match restriction with
  | FStarC_Syntax_Syntax.Unrestricted -> f env1 ns restriction
  | FStarC_Syntax_Syntax.AllowList l ->
      let mk_lid id =
        let uu___ =
          let uu___2 =
            let uu___3 = FStarC_Ident.qual_id ns id in
            FStarC_Ident.ids_of_lid uu___3 in
          FStarC_Ident.lid_of_ids uu___2 in
        FStarC_Ident.set_lid_range uu___ (FStarC_Ident.range_of_id id) in
      let name_exists id =
        let lid = mk_lid id in
        let uu___ = try_lookup_lid env1 lid in
        match uu___ with
        | FStar_Pervasives_Native.Some uu___2 -> true
        | FStar_Pervasives_Native.None ->
            let uu___2 = try_lookup_record_or_dc_by_field_name env1 lid in
            FStar_Pervasives_Native.uu___is_Some uu___2 in
      let l1 =
        let uu___ =
          let uu___2 =
            FStarC_List.map
              (fun uu___3 ->
                 match uu___3 with
                 | (id, renamed) ->
                     let with_id_range =
                       FStarC_Ident.set_id_range
                         (FStarC_Ident.range_of_id
                            (FStarC_Option.dflt id renamed)) in
                     let uu___4 =
                       let uu___5 = mk_lid id in
                       find_data_constructors_for_typ env1 uu___5 in
                     (match uu___4 with
                      | FStar_Pervasives_Native.Some idents ->
                          FStarC_List.map
                            (fun id1 ->
                               ((with_id_range
                                   (FStarC_Ident.ident_of_lid id1)),
                                 FStar_Pervasives_Native.None)) idents
                      | FStar_Pervasives_Native.None -> [])) l in
          FStarC_List.flatten uu___2 in
        FStarC_List.append l uu___ in
      let l2 =
        let constructor_lid_to_desugared_record_lids =
          let uu___ =
            let uu___2 =
              Obj.magic
                (FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_list
                   () () (Obj.magic env1.modules)
                   (fun uu___3 ->
                      (fun uu___3 ->
                         let uu___3 = Obj.magic uu___3 in
                         match uu___3 with
                         | (uu___4,
                            { FStarC_Syntax_Syntax.name = uu___5;
                              FStarC_Syntax_Syntax.declarations =
                                declarations;
                              FStarC_Syntax_Syntax.is_interface = uu___6;_})
                             ->
                             Obj.magic
                               (FStarC_Class_Monad.op_let_Bang
                                  FStarC_Class_Monad.monad_list () ()
                                  (Obj.magic declarations)
                                  (fun uu___7 ->
                                     (fun sigelt ->
                                        let sigelt = Obj.magic sigelt in
                                        Obj.magic
                                          (FStarC_Class_Monad.op_let_Bang
                                             FStarC_Class_Monad.monad_list ()
                                             ()
                                             (match sigelt.FStarC_Syntax_Syntax.sigel
                                              with
                                              | FStarC_Syntax_Syntax.Sig_bundle
                                                  {
                                                    FStarC_Syntax_Syntax.ses
                                                      = ses;
                                                    FStarC_Syntax_Syntax.lids
                                                      = uu___7;_}
                                                  -> Obj.magic ses
                                              | uu___7 -> Obj.magic [])
                                             (fun uu___7 ->
                                                (fun sigelt1 ->
                                                   let sigelt1 =
                                                     Obj.magic sigelt1 in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_let_Bang
                                                        FStarC_Class_Monad.monad_list
                                                        () ()
                                                        (Obj.magic
                                                           (FStarC_Syntax_Util.lids_of_sigelt
                                                              sigelt1))
                                                        (fun uu___7 ->
                                                           (fun lid ->
                                                              let lid =
                                                                Obj.magic lid in
                                                              let uu___7 =
                                                                FStarC_Syntax_Util.get_attribute
                                                                  FStarC_Parser_Const.desugar_of_variant_record_lid
                                                                  sigelt1.FStarC_Syntax_Syntax.sigattrs in
                                                              match uu___7
                                                              with
                                                              | FStar_Pervasives_Native.Some
                                                                  (({
                                                                    FStarC_Syntax_Syntax.n
                                                                    =
                                                                    FStarC_Syntax_Syntax.Tm_constant
                                                                    (FStarC_Const.Const_string
                                                                    (s,
                                                                    uu___8));
                                                                    FStarC_Syntax_Syntax.pos
                                                                    = uu___9;
                                                                    FStarC_Syntax_Syntax.vars
                                                                    = uu___10;
                                                                    FStarC_Syntax_Syntax.hash_code
                                                                    = uu___11;_},
                                                                    FStar_Pervasives_Native.None)::[])
                                                                  ->
                                                                  let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Ident.lid_of_str
                                                                    s in
                                                                    (uu___13,
                                                                    lid) in
                                                                  Obj.magic
                                                                    [uu___12]
                                                              | uu___8 ->
                                                                  Obj.magic
                                                                    [])
                                                             uu___7))) uu___7)))
                                       uu___7))) uu___3)) in
            FStarC_List.filter
              (fun uu___3 ->
                 match uu___3 with
                 | (cons, lid) ->
                     let uu___4 =
                       FStarC_Class_Deq.op_Equals_Question
                         (FStarC_Class_Ord.ord_eq
                            (FStarC_Class_Ord.ord_list
                               FStarC_Syntax_Syntax.ord_ident))
                         (FStarC_Ident.ns_of_lid cons)
                         (FStarC_Ident.ns_of_lid lid) in
                     if uu___4
                     then
                       FStarC_Class_Deq.op_Equals_Question
                         (FStarC_Class_Ord.ord_eq
                            (FStarC_Class_Ord.ord_list
                               FStarC_Syntax_Syntax.ord_ident))
                         (FStarC_Ident.ns_of_lid lid)
                         (FStarC_Ident.ids_of_lid ns)
                     else false) uu___2 in
          FStarC_List.map
            (fun uu___2 ->
               match uu___2 with
               | (cons, lid) ->
                   ((FStarC_Ident.ident_of_lid cons),
                     (FStarC_Ident.ident_of_lid lid))) uu___ in
        let uu___ =
          let uu___2 =
            FStarC_List.filter
              (fun uu___3 ->
                 match uu___3 with
                 | (cons, uu___4) ->
                     let uu___5 =
                       FStarC_List.find
                         (fun uu___6 ->
                            match uu___6 with
                            | (lid, uu___7) ->
                                FStarC_Class_Deq.op_Equals_Question
                                  FStarC_Syntax_Syntax.deq_univ_name lid cons)
                         l1 in
                     FStar_Pervasives_Native.uu___is_Some uu___5)
              constructor_lid_to_desugared_record_lids in
          FStarC_List.map
            (fun uu___3 ->
               match uu___3 with
               | (uu___4, lid) -> (lid, FStar_Pervasives_Native.None)) uu___2 in
        FStarC_List.append l1 uu___ in
      let l3 =
        let uu___ =
          let uu___2 =
            FStarC_List.map
              (fun uu___3 ->
                 match uu___3 with
                 | (id, renamed) ->
                     let with_renamed_range =
                       FStarC_Ident.set_id_range
                         (FStarC_Ident.range_of_id
                            (FStarC_Option.dflt id renamed)) in
                     let with_id_range =
                       FStarC_Ident.set_id_range
                         (FStarC_Ident.range_of_id
                            (FStarC_Option.dflt id renamed)) in
                     let lid = mk_lid id in
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = find_binders_for_datacons env1 lid in
                           match uu___7 with
                           | FStar_Pervasives_Native.None -> []
                           | FStar_Pervasives_Native.Some l4 -> l4 in
                         FStarC_List.map
                           (fun binder ->
                              let uu___7 =
                                let uu___8 =
                                  FStarC_Syntax_Util.mk_field_projector_name_from_ident
                                    lid binder in
                                FStarC_Ident.ident_of_lid uu___8 in
                              let uu___8 =
                                FStarC_Option.map
                                  (fun renamed1 ->
                                     let uu___9 =
                                       let uu___10 =
                                         FStarC_Ident.lid_of_ids [renamed1] in
                                       FStarC_Syntax_Util.mk_field_projector_name_from_ident
                                         uu___10 binder in
                                     FStarC_Ident.ident_of_lid uu___9)
                                  renamed in
                              (uu___7, uu___8)) uu___6 in
                       let uu___6 =
                         let uu___7 =
                           let uu___8 =
                             let uu___9 =
                               let uu___10 =
                                 let uu___11 =
                                   let uu___12 = FStarC_Ident.lid_of_ids [id] in
                                   FStarC_Syntax_Util.mk_discriminator
                                     uu___12 in
                                 let uu___12 =
                                   FStarC_Option.map
                                     (fun renamed1 ->
                                        let uu___13 =
                                          FStarC_Ident.lid_of_ids [renamed1] in
                                        FStarC_Syntax_Util.mk_discriminator
                                          uu___13) renamed in
                                 (uu___11, uu___12) in
                               [uu___10] in
                             FStarC_List.map
                               (fun uu___10 ->
                                  match uu___10 with
                                  | (x, y) ->
                                      let uu___11 =
                                        FStarC_Option.map
                                          FStarC_Ident.ident_of_lid y in
                                      ((FStarC_Ident.ident_of_lid x),
                                        uu___11)) uu___9 in
                           FStarC_List.filter
                             (fun uu___9 ->
                                match uu___9 with
                                | (x, uu___10) -> name_exists x) uu___8 in
                         let uu___8 =
                           let uu___9 = try_lookup_record_type env1 lid in
                           match uu___9 with
                           | FStar_Pervasives_Native.Some
                               { typename = uu___10; constrname;
                                 parms = uu___11; fields;
                                 is_private = uu___12; is_record = uu___13;_}
                               ->
                               FStarC_List.map
                                 (fun uu___14 ->
                                    match uu___14 with
                                    | (id1, uu___15) ->
                                        (id1, FStar_Pervasives_Native.None))
                                 fields
                           | FStar_Pervasives_Native.None -> [] in
                         FStarC_List.op_At uu___7 uu___8 in
                       FStarC_List.op_At uu___5 uu___6 in
                     FStarC_List.map
                       (fun uu___5 ->
                          match uu___5 with
                          | (id1, renamed1) ->
                              let uu___6 =
                                FStarC_Option.map with_renamed_range renamed1 in
                              ((with_id_range id1), uu___6)) uu___4) l2 in
          FStarC_List.flatten uu___2 in
        FStarC_List.append l2 uu___ in
      ((let final_idents =
          FStarC_List.mapi
            (fun i uu___ ->
               match uu___ with
               | (id, renamed) -> ((FStarC_Option.dflt id renamed), i)) l3 in
        let uu___ =
          FStarC_Util.find_dup
            (fun uu___2 uu___3 ->
               match (uu___2, uu___3) with
               | ((x, uu___4), (y, uu___5)) ->
                   FStarC_Class_Deq.op_Equals_Question
                     FStarC_Syntax_Syntax.deq_univ_name x y) final_idents in
        match uu___ with
        | FStar_Pervasives_Native.Some (id, i) ->
            let others =
              FStarC_List.filter
                (fun uu___2 ->
                   match uu___2 with
                   | (id', i') ->
                       let uu___3 =
                         FStarC_Class_Deq.op_Equals_Question
                           FStarC_Syntax_Syntax.deq_univ_name id id' in
                       if uu___3
                       then
                         let uu___4 =
                           FStarC_Class_Deq.op_Equals_Question
                             (FStarC_Class_Ord.ord_eq
                                FStarC_Class_Ord.ord_int) i i' in
                         Prims.op_Negation uu___4
                       else false) final_idents in
            ((let uu___3 =
                FStarC_List.mapi
                  (fun nth uu___4 ->
                     match uu___4 with
                     | (other, uu___5) ->
                         let nth1 =
                           match nth with
                           | uu___6 when uu___6 = Prims.int_zero -> "first"
                           | uu___6 when uu___6 = Prims.int_one -> "second"
                           | uu___6 when uu___6 = (Prims.of_int (2)) ->
                               "third"
                           | nth2 ->
                               let uu___6 =
                                 FStarC_Class_Show.show
                                   FStarC_Class_Show.showable_int
                                   (nth2 + Prims.int_one) in
                               Prims.strcat uu___6 "th" in
                         let uu___6 =
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Class_Show.show
                                   FStarC_Ident.showable_ident other in
                               Prims.strcat uu___9
                                 (Prims.strcat " "
                                    (Prims.strcat nth1
                                       " occurence comes from this declaration")) in
                             FStarC_Errors_Msg.text uu___8 in
                           [uu___7] in
                         {
                           FStarC_Errors.issue_msg = uu___6;
                           FStarC_Errors.issue_level = FStarC_Errors.EError;
                           FStarC_Errors.issue_range =
                             (FStar_Pervasives_Native.Some
                                (FStarC_Ident.range_of_id other));
                           FStarC_Errors.issue_number =
                             FStar_Pervasives_Native.None;
                           FStarC_Errors.issue_ctx = []
                         }) others in
              FStarC_Errors.add_issues uu___3);
             (let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      FStarC_Class_Show.show FStarC_Class_Show.showable_int
                        ((FStarC_List.length others) + Prims.int_one) in
                    Prims.strcat uu___6 " times" in
                  Prims.strcat "The name %s was imported " uu___5 in
                FStarC_Format.fmt1 uu___4 (FStarC_Ident.string_of_id id) in
              FStarC_Errors.raise_error FStarC_Ident.hasrange_ident id
                FStarC_Errors_Codes.Fatal_DuplicateTopLevelNames ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                (Obj.magic uu___3)))
        | FStar_Pervasives_Native.None -> ());
       FStarC_List.iter
         (fun uu___2 ->
            match uu___2 with
            | (id, _renamed) ->
                let uu___3 =
                  let uu___4 = name_exists id in Prims.op_Negation uu___4 in
                if uu___3
                then
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 = mk_lid id in
                          FStarC_Ident.string_of_lid uu___8 in
                        FStarC_Format.fmt1 "Definition %s cannot be found."
                          uu___7 in
                      FStarC_Errors_Msg.text uu___6 in
                    [uu___5] in
                  FStarC_Errors.raise_error FStarC_Ident.hasrange_ident id
                    FStarC_Errors_Codes.Fatal_NameNotFound ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic uu___4)
                else ()) l3;
       f env1 ns (FStarC_Syntax_Syntax.AllowList l3))
let push_namespace' (env1 : env) (ns : FStarC_Ident.lident)
  (restriction : FStarC_Syntax_Syntax.restriction) : env=
  let uu___ =
    let uu___2 = resolve_module_name env1 ns false in
    match uu___2 with
    | FStar_Pervasives_Native.None ->
        let module_names =
          FStarC_List.map FStar_Pervasives_Native.fst env1.modules in
        let module_names1 =
          match env1.curmodule with
          | FStar_Pervasives_Native.None -> module_names
          | FStar_Pervasives_Native.Some l -> l :: module_names in
        let fail uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  FStarC_List.map FStarC_Ident.string_of_lid module_names1 in
                typo_msg (FStarC_Ident.string_of_lid ns) uu___7 in
              [uu___6] in
            (FStarC_Errors_Msg.text
               (FStarC_Format.fmt1 "Namespace '%s' cannot be found."
                  (FStarC_Ident.string_of_lid ns)))
              :: uu___5 in
          FStarC_Errors.raise_error FStarC_Ident.hasrange_lident ns
            FStarC_Errors_Codes.Fatal_NameSpaceNotFound ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
            (Obj.magic uu___4) in
        let uu___3 = FStarC_Parser_Dep.fly_deps_enabled () in
        if uu___3
        then
          let uu___4 = FStarC_Parser_Dep.is_valid_namespace env1.dep_graph ns in
          (if uu___4
           then (ns, FStarC_Syntax_Syntax.Open_namespace)
           else fail ())
        else
          (let uu___5 =
             FStarC_Util.for_some
               (fun m ->
                  FStarC_Util.starts_with
                    (Prims.strcat (FStarC_Ident.string_of_lid m) ".")
                    (Prims.strcat (FStarC_Ident.string_of_lid ns) "."))
               module_names1 in
           if uu___5
           then (ns, FStarC_Syntax_Syntax.Open_namespace)
           else fail ())
    | FStar_Pervasives_Native.Some ns' ->
        (ns', FStarC_Syntax_Syntax.Open_module) in
  match uu___ with
  | (ns', kd) ->
      ((env1.ds_hooks).ds_push_open_hook env1 (ns', kd, restriction);
       push_scope_mod env1
         (Open_module_or_namespace ((ns', kd, restriction), false)))
let push_include' (env1 : env) (ns : FStarC_Ident.lident)
  (restriction : FStarC_Syntax_Syntax.restriction) : env=
  let ns0 = ns in
  let uu___ = resolve_module_name env1 ns false in
  match uu___ with
  | FStar_Pervasives_Native.Some ns1 ->
      ((env1.ds_hooks).ds_push_include_hook env1 ns1;
       (let env2 =
          push_scope_mod env1
            (Open_module_or_namespace
               ((ns1, FStarC_Syntax_Syntax.Open_module, restriction), false)) in
        let curmod =
          let uu___3 = current_module env2 in
          FStarC_Ident.string_of_lid uu___3 in
        (let uu___4 = FStarC_SMap.try_find env2.includes curmod in
         match uu___4 with
         | FStar_Pervasives_Native.None -> ()
         | FStar_Pervasives_Native.Some incl ->
             let uu___5 =
               let uu___6 = FStarC_Effect.op_Bang incl in (ns1, restriction)
                 :: uu___6 in
             FStarC_Effect.op_Colon_Equals incl uu___5);
        (match () with
         | () ->
             let uu___4 =
               get_trans_exported_id_set env2
                 (FStarC_Ident.string_of_lid ns1) in
             (match uu___4 with
              | FStar_Pervasives_Native.Some ns_trans_exports ->
                  ((let uu___6 =
                      let uu___7 = get_exported_id_set env2 curmod in
                      let uu___8 = get_trans_exported_id_set env2 curmod in
                      (uu___7, uu___8) in
                    match uu___6 with
                    | (FStar_Pervasives_Native.Some cur_exports,
                       FStar_Pervasives_Native.Some cur_trans_exports) ->
                        let update_exports k =
                          let ns_ex =
                            let uu___7 =
                              FStarC_Effect.op_Bang (ns_trans_exports k) in
                            Obj.magic
                              (FStarC_Class_Setlike.filter ()
                                 (Obj.magic
                                    (FStarC_RBSet.setlike_rbset
                                       FStarC_Class_Ord.ord_string))
                                 (fun id ->
                                    let uu___8 =
                                      FStarC_Syntax_Syntax.is_ident_allowed_by_restriction
                                        (FStarC_Ident.id_of_text id)
                                        restriction in
                                    FStar_Pervasives_Native.uu___is_Some
                                      uu___8) (Obj.magic uu___7)) in
                          let ex = cur_exports k in
                          (let uu___8 =
                             let uu___9 = FStarC_Effect.op_Bang ex in
                             Obj.magic
                               (FStarC_Class_Setlike.diff ()
                                  (Obj.magic
                                     (FStarC_RBSet.setlike_rbset
                                        FStarC_Class_Ord.ord_string))
                                  (Obj.magic uu___9) (Obj.magic ns_ex)) in
                           FStarC_Effect.op_Colon_Equals ex uu___8);
                          (match () with
                           | () ->
                               let trans_ex = cur_trans_exports k in
                               let uu___9 =
                                 let uu___10 = FStarC_Effect.op_Bang trans_ex in
                                 Obj.magic
                                   (FStarC_Class_Setlike.union ()
                                      (Obj.magic
                                         (FStarC_RBSet.setlike_rbset
                                            FStarC_Class_Ord.ord_string))
                                      (Obj.magic uu___10) (Obj.magic ns_ex)) in
                               FStarC_Effect.op_Colon_Equals trans_ex uu___9) in
                        FStarC_List.iter update_exports all_exported_id_kinds
                    | uu___7 -> ());
                   (match () with | () -> env2))
              | FStar_Pervasives_Native.None ->
                  FStarC_Errors.raise_error FStarC_Ident.hasrange_lident ns1
                    FStarC_Errors_Codes.Fatal_IncludeModuleNotPrepared ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                    (Obj.magic
                       (FStarC_Format.fmt1
                          "include: Module %s was not prepared"
                          (FStarC_Ident.string_of_lid ns1)))))))
  | uu___2 ->
      FStarC_Errors.raise_error FStarC_Ident.hasrange_lident ns
        FStarC_Errors_Codes.Fatal_ModuleNotFound ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic
           (FStarC_Format.fmt1 "include: Module %s cannot be found"
              (FStarC_Ident.string_of_lid ns)))
let push_namespace :
  env -> FStarC_Ident.lident -> FStarC_Syntax_Syntax.restriction -> env=
  elab_restriction push_namespace'
let push_include :
  env -> FStarC_Ident.lident -> FStarC_Syntax_Syntax.restriction -> env=
  elab_restriction push_include'
let push_module_abbrev (env1 : env) (x : FStarC_Ident.ident)
  (l : FStarC_Ident.lident) : env=
  let uu___ = module_is_defined env1 l in
  if uu___
  then
    ((env1.ds_hooks).ds_push_module_abbrev_hook env1 x l;
     push_scope_mod env1 (Module_abbrev (x, l)))
  else
    FStarC_Errors.raise_error FStarC_Ident.hasrange_lident l
      FStarC_Errors_Codes.Fatal_ModuleNotFound ()
      (Obj.magic FStarC_Errors_Msg.is_error_message_string)
      (Obj.magic
         (FStarC_Format.fmt1 "Module %s cannot be found"
            (FStarC_Ident.string_of_lid l)))
let check_admits (env1 : env) (m : FStarC_Syntax_Syntax.modul) :
  FStarC_Syntax_Syntax.modul=
  let mname_ids = FStarC_Ident.ids_of_lid m.FStarC_Syntax_Syntax.name in
  let admitted_sig_lids =
    FStarC_List.fold_left
      (fun lids se ->
         match se.FStarC_Syntax_Syntax.sigel with
         | FStarC_Syntax_Syntax.Sig_declare_typ
             { FStarC_Syntax_Syntax.lid2 = l; FStarC_Syntax_Syntax.us2 = u;
               FStarC_Syntax_Syntax.t2 = t;_}
             when
             (Prims.op_Negation
                (FStarC_List.contains FStarC_Syntax_Syntax.Assumption
                   se.FStarC_Syntax_Syntax.sigquals))
               && ((FStarC_Ident.ns_of_lid l) = mname_ids)
             ->
             let uu___ =
               let uu___2 = sigmap env1 in
               FStarC_SMap.try_find uu___2 (FStarC_Ident.string_of_lid l) in
             (match uu___ with
              | FStar_Pervasives_Native.Some
                  ({
                     FStarC_Syntax_Syntax.sigel =
                       FStarC_Syntax_Syntax.Sig_let uu___2;
                     FStarC_Syntax_Syntax.sigrng = uu___3;
                     FStarC_Syntax_Syntax.sigquals = uu___4;
                     FStarC_Syntax_Syntax.sigmeta = uu___5;
                     FStarC_Syntax_Syntax.sigattrs = uu___6;
                     FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
                     FStarC_Syntax_Syntax.sigopts = uu___8;_},
                   uu___9)
                  -> lids
              | FStar_Pervasives_Native.Some
                  ({
                     FStarC_Syntax_Syntax.sigel =
                       FStarC_Syntax_Syntax.Sig_inductive_typ uu___2;
                     FStarC_Syntax_Syntax.sigrng = uu___3;
                     FStarC_Syntax_Syntax.sigquals = uu___4;
                     FStarC_Syntax_Syntax.sigmeta = uu___5;
                     FStarC_Syntax_Syntax.sigattrs = uu___6;
                     FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
                     FStarC_Syntax_Syntax.sigopts = uu___8;_},
                   uu___9)
                  -> lids
              | FStar_Pervasives_Native.Some
                  ({
                     FStarC_Syntax_Syntax.sigel =
                       FStarC_Syntax_Syntax.Sig_splice uu___2;
                     FStarC_Syntax_Syntax.sigrng = uu___3;
                     FStarC_Syntax_Syntax.sigquals = uu___4;
                     FStarC_Syntax_Syntax.sigmeta = uu___5;
                     FStarC_Syntax_Syntax.sigattrs = uu___6;
                     FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___7;
                     FStarC_Syntax_Syntax.sigopts = uu___8;_},
                   uu___9)
                  -> lids
              | uu___2 ->
                  ((let uu___4 =
                      let uu___5 = FStarC_Options.interactive () in
                      Prims.op_Negation uu___5 in
                    if uu___4
                    then
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              FStarC_Class_Show.show
                                FStarC_Ident.showable_lident l in
                            FStar_Pprint.doc_of_string uu___8 in
                          FStar_Pprint.op_Hat_Slash_Hat uu___7
                            (FStarC_Errors_Msg.text
                               "is declared but no definition was found") in
                        [uu___6;
                        FStarC_Errors_Msg.text
                          "Add an 'assume' if this is intentional"] in
                      FStarC_Errors.log_issue FStarC_Ident.hasrange_lident l
                        FStarC_Errors_Codes.Error_AdmitWithoutDefinition ()
                        (Obj.magic
                           FStarC_Errors_Msg.is_error_message_list_doc)
                        (Obj.magic uu___5)
                    else ());
                   (let quals = FStarC_Syntax_Syntax.Assumption ::
                      (se.FStarC_Syntax_Syntax.sigquals) in
                    (let uu___5 = sigmap env1 in
                     FStarC_SMap.add uu___5 (FStarC_Ident.string_of_lid l)
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
let finish (env1 : env) (modul : FStarC_Syntax_Syntax.modul) : env=
  FStarC_List.iter
    (fun se ->
       let quals = se.FStarC_Syntax_Syntax.sigquals in
       match se.FStarC_Syntax_Syntax.sigel with
       | FStarC_Syntax_Syntax.Sig_bundle
           { FStarC_Syntax_Syntax.ses = ses;
             FStarC_Syntax_Syntax.lids = uu___2;_}
           ->
           if FStarC_List.contains FStarC_Syntax_Syntax.Private quals
           then
             FStarC_List.iter
               (fun se1 ->
                  match se1.FStarC_Syntax_Syntax.sigel with
                  | FStarC_Syntax_Syntax.Sig_datacon
                      { FStarC_Syntax_Syntax.lid1 = lid;
                        FStarC_Syntax_Syntax.us1 = uu___3;
                        FStarC_Syntax_Syntax.t1 = uu___4;
                        FStarC_Syntax_Syntax.ty_lid = uu___5;
                        FStarC_Syntax_Syntax.num_ty_params = uu___6;
                        FStarC_Syntax_Syntax.mutuals1 = uu___7;
                        FStarC_Syntax_Syntax.injective_type_params1 = uu___8;
                        FStarC_Syntax_Syntax.proj_disc_lids = uu___9;_}
                      ->
                      let uu___10 = sigmap env1 in
                      FStarC_SMap.remove uu___10
                        (FStarC_Ident.string_of_lid lid)
                  | FStarC_Syntax_Syntax.Sig_inductive_typ
                      { FStarC_Syntax_Syntax.lid = lid;
                        FStarC_Syntax_Syntax.us = univ_names;
                        FStarC_Syntax_Syntax.params = binders;
                        FStarC_Syntax_Syntax.num_uniform_params = uu___3;
                        FStarC_Syntax_Syntax.t = typ;
                        FStarC_Syntax_Syntax.mutuals = uu___4;
                        FStarC_Syntax_Syntax.ds = uu___5;
                        FStarC_Syntax_Syntax.injective_type_params = uu___6;_}
                      ->
                      ((let uu___8 = sigmap env1 in
                        FStarC_SMap.remove uu___8
                          (FStarC_Ident.string_of_lid lid));
                       if
                         Prims.op_Negation
                           (FStarC_List.contains FStarC_Syntax_Syntax.Private
                              quals)
                       then
                         (let sigel =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      FStarC_Syntax_Syntax.mk_Total typ in
                                    {
                                      FStarC_Syntax_Syntax.bs1 = binders;
                                      FStarC_Syntax_Syntax.comp = uu___12
                                    } in
                                  FStarC_Syntax_Syntax.Tm_arrow uu___11 in
                                FStarC_Syntax_Syntax.mk uu___10
                                  (FStarC_Ident.range_of_lid lid) in
                              {
                                FStarC_Syntax_Syntax.lid2 = lid;
                                FStarC_Syntax_Syntax.us2 = univ_names;
                                FStarC_Syntax_Syntax.t2 = uu___9
                              } in
                            FStarC_Syntax_Syntax.Sig_declare_typ uu___8 in
                          let se2 =
                            {
                              FStarC_Syntax_Syntax.sigel = sigel;
                              FStarC_Syntax_Syntax.sigrng =
                                (se1.FStarC_Syntax_Syntax.sigrng);
                              FStarC_Syntax_Syntax.sigquals =
                                (FStarC_Syntax_Syntax.Assumption :: quals);
                              FStarC_Syntax_Syntax.sigmeta =
                                (se1.FStarC_Syntax_Syntax.sigmeta);
                              FStarC_Syntax_Syntax.sigattrs =
                                (se1.FStarC_Syntax_Syntax.sigattrs);
                              FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                (se1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                              FStarC_Syntax_Syntax.sigopts =
                                (se1.FStarC_Syntax_Syntax.sigopts)
                            } in
                          let uu___8 = sigmap env1 in
                          FStarC_SMap.add uu___8
                            (FStarC_Ident.string_of_lid lid) (se2, false))
                       else ())
                  | uu___3 -> ()) ses
           else ()
       | FStarC_Syntax_Syntax.Sig_declare_typ
           { FStarC_Syntax_Syntax.lid2 = lid;
             FStarC_Syntax_Syntax.us2 = uu___2;
             FStarC_Syntax_Syntax.t2 = uu___3;_}
           ->
           if FStarC_List.contains FStarC_Syntax_Syntax.Private quals
           then
             let uu___4 = sigmap env1 in
             FStarC_SMap.remove uu___4 (FStarC_Ident.string_of_lid lid)
           else ()
       | FStarC_Syntax_Syntax.Sig_let
           { FStarC_Syntax_Syntax.lbs1 = (uu___2, lbs);
             FStarC_Syntax_Syntax.lids1 = uu___3;_}
           ->
           if FStarC_List.contains FStarC_Syntax_Syntax.Private quals
           then
             FStarC_List.iter
               (fun lb ->
                  let uu___4 = sigmap env1 in
                  FStarC_SMap.remove uu___4
                    (FStarC_Ident.string_of_lid
                       (FStar_Pervasives.__proj__Inr__item__v
                          lb.FStarC_Syntax_Syntax.lbname).FStarC_Syntax_Syntax.fv_name))
               lbs
           else ()
       | uu___2 -> ()) modul.FStarC_Syntax_Syntax.declarations;
  (let curmod =
     let uu___2 = current_module env1 in FStarC_Ident.string_of_lid uu___2 in
   (let uu___3 =
      let uu___4 = get_exported_id_set env1 curmod in
      let uu___5 = get_trans_exported_id_set env1 curmod in (uu___4, uu___5) in
    match uu___3 with
    | (FStar_Pervasives_Native.Some cur_ex, FStar_Pervasives_Native.Some
       cur_trans_ex) ->
        let update_exports eikind =
          let cur_ex_set = FStarC_Effect.op_Bang (cur_ex eikind) in
          let cur_trans_ex_set_ref = cur_trans_ex eikind in
          let uu___4 =
            let uu___5 = FStarC_Effect.op_Bang cur_trans_ex_set_ref in
            Obj.magic
              (FStarC_Class_Setlike.union ()
                 (Obj.magic
                    (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
                 (Obj.magic cur_ex_set) (Obj.magic uu___5)) in
          FStarC_Effect.op_Colon_Equals cur_trans_ex_set_ref uu___4 in
        FStarC_List.iter update_exports all_exported_id_kinds
    | uu___4 -> ());
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
                iface_interleaving_init = (env1.iface_interleaving_init);
                syntax_only = (env1.syntax_only);
                ds_hooks = (env1.ds_hooks);
                dep_graph = (env1.dep_graph);
                no_prelude = (env1.no_prelude)
              }))))
let stack : env Prims.list FStarC_Effect.ref= FStarC_Effect.mk_ref []
let push (env1 : env) : env=
  FStarC_Util.atomically
    (fun uu___ ->
       push_record_cache ();
       (let uu___4 =
          let uu___5 = FStarC_Effect.op_Bang stack in env1 :: uu___5 in
        FStarC_Effect.op_Colon_Equals stack uu___4);
       (let uu___4 = FStarC_SMap.copy env1.exported_ids in
        let uu___5 = FStarC_SMap.copy env1.trans_exported_ids in
        let uu___6 = FStarC_SMap.copy env1.includes in
        let uu___7 = FStarC_SMap.copy env1.sigmap in
        {
          curmodule = (env1.curmodule);
          curmonad = (env1.curmonad);
          modules = (env1.modules);
          scope_mods = (env1.scope_mods);
          exported_ids = uu___4;
          trans_exported_ids = uu___5;
          includes = uu___6;
          sigaccum = (env1.sigaccum);
          sigmap = uu___7;
          iface = (env1.iface);
          admitted_iface = (env1.admitted_iface);
          expect_typ = (env1.expect_typ);
          remaining_iface_decls = (env1.remaining_iface_decls);
          iface_interleaving_init = (env1.iface_interleaving_init);
          syntax_only = (env1.syntax_only);
          ds_hooks = (env1.ds_hooks);
          dep_graph = (env1.dep_graph);
          no_prelude = (env1.no_prelude)
        }))
let pop (uu___ : unit) : env=
  FStarC_Util.atomically
    (fun uu___2 ->
       let uu___3 = FStarC_Effect.op_Bang stack in
       match uu___3 with
       | env1::tl ->
           (pop_record_cache (); FStarC_Effect.op_Colon_Equals stack tl; env1)
       | uu___4 -> FStarC_Effect.failwith "Impossible: Too many pops")
let snapshot (env1 : env) : (Prims.int * env)=
  FStarC_Common.snapshot "DsEnv" push stack env1
let rollback (depth : Prims.int FStar_Pervasives_Native.option) : env=
  FStarC_Common.rollback "DsEnv" pop stack depth
let export_interface (m : FStarC_Ident.lident) (env1 : env) : env=
  let sigelt_in_m se =
    match FStarC_Syntax_Util.lids_of_sigelt se with
    | l::uu___ -> (FStarC_Ident.nsstr l) = (FStarC_Ident.string_of_lid m)
    | uu___ -> false in
  let sm = sigmap env1 in
  let env2 = pop () in
  let keys = FStarC_SMap.keys sm in
  let sm' = sigmap env2 in
  FStarC_List.iter
    (fun k ->
       let uu___2 = FStarC_SMap.try_find sm' k in
       match uu___2 with
       | FStar_Pervasives_Native.Some (se, true) when sigelt_in_m se ->
           (FStarC_SMap.remove sm' k;
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
               | uu___4 -> se in
             FStarC_SMap.add sm' k (se1, false)))
       | uu___3 -> ()) keys;
  env2
let finish_module_or_interface (env1 : env)
  (modul : FStarC_Syntax_Syntax.modul) : (env * FStarC_Syntax_Syntax.modul)=
  let modul1 =
    if Prims.op_Negation modul.FStarC_Syntax_Syntax.is_interface
    then check_admits env1 modul
    else modul in
  let uu___ = finish env1 modul1 in (uu___, modul1)
type exported_ids =
  {
  exported_id_terms: string_set ;
  exported_id_fields: string_set }
let __proj__Mkexported_ids__item__exported_id_terms
  (projectee : exported_ids) : string_set=
  match projectee with
  | { exported_id_terms; exported_id_fields;_} -> exported_id_terms
let __proj__Mkexported_ids__item__exported_id_fields
  (projectee : exported_ids) : string_set=
  match projectee with
  | { exported_id_terms; exported_id_fields;_} -> exported_id_fields
let showable_exported_ids : exported_ids FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun e ->
         let uu___ =
           FStarC_Class_Show.show
             (FStarC_RBSet.showable_rbset FStarC_Class_Show.showable_string)
             e.exported_id_terms in
         let uu___2 =
           FStarC_Class_Show.show
             (FStarC_RBSet.showable_rbset FStarC_Class_Show.showable_string)
             e.exported_id_fields in
         FStarC_Format.fmt2 "{exported_id_terms=%s\nexported_id_fields=%s}"
           uu___ uu___2)
  }
let as_exported_ids (e : exported_id_set) : exported_ids=
  let terms = FStarC_Effect.op_Bang (e Exported_id_term_type) in
  let fields = FStarC_Effect.op_Bang (e Exported_id_field) in
  { exported_id_terms = terms; exported_id_fields = fields }
let as_exported_id_set (e : exported_ids FStar_Pervasives_Native.option) :
  exported_id_kind -> string_set FStarC_Effect.ref=
  match e with
  | FStar_Pervasives_Native.None -> exported_id_set_new ()
  | FStar_Pervasives_Native.Some e1 ->
      let terms = FStarC_Effect.mk_ref e1.exported_id_terms in
      let fields = FStarC_Effect.mk_ref e1.exported_id_fields in
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
    ;
  mii_no_prelude: Prims.bool }
let __proj__Mkmodule_inclusion_info__item__mii_exported_ids
  (projectee : module_inclusion_info) :
  exported_ids FStar_Pervasives_Native.option=
  match projectee with
  | { mii_exported_ids; mii_trans_exported_ids; mii_includes;
      mii_no_prelude;_} -> mii_exported_ids
let __proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids
  (projectee : module_inclusion_info) :
  exported_ids FStar_Pervasives_Native.option=
  match projectee with
  | { mii_exported_ids; mii_trans_exported_ids; mii_includes;
      mii_no_prelude;_} -> mii_trans_exported_ids
let __proj__Mkmodule_inclusion_info__item__mii_includes
  (projectee : module_inclusion_info) :
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.restriction) Prims.list
    FStar_Pervasives_Native.option=
  match projectee with
  | { mii_exported_ids; mii_trans_exported_ids; mii_includes;
      mii_no_prelude;_} -> mii_includes
let __proj__Mkmodule_inclusion_info__item__mii_no_prelude
  (projectee : module_inclusion_info) : Prims.bool=
  match projectee with
  | { mii_exported_ids; mii_trans_exported_ids; mii_includes;
      mii_no_prelude;_} -> mii_no_prelude
let showable_mii : module_inclusion_info FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun mii ->
         let uu___ =
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_option showable_exported_ids)
             mii.mii_exported_ids in
         let uu___2 =
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_option showable_exported_ids)
             mii.mii_trans_exported_ids in
         let uu___3 =
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_option
                (FStarC_Class_Show.show_list
                   (FStarC_Class_Show.show_tuple2
                      FStarC_Ident.showable_lident
                      FStarC_Syntax_Syntax.showable_restriction)))
             mii.mii_includes in
         let uu___4 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_bool
             mii.mii_no_prelude in
         FStarC_Format.fmt4
           "{exported_ids=%s\ntrans_exported_ids=%s\nincludes:%s\nno_prelude:%s}"
           uu___ uu___2 uu___3 uu___4)
  }
let default_mii : module_inclusion_info=
  {
    mii_exported_ids = FStar_Pervasives_Native.None;
    mii_trans_exported_ids = FStar_Pervasives_Native.None;
    mii_includes = FStar_Pervasives_Native.None;
    mii_no_prelude = false
  }
let as_includes
  (uu___ :
    (FStarC_Ident.lident * FStarC_Syntax_Syntax.restriction) Prims.list
      FStar_Pervasives_Native.option)
  :
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.restriction) Prims.list
    FStarC_Effect.ref=
  match uu___ with
  | FStar_Pervasives_Native.None -> FStarC_Effect.mk_ref []
  | FStar_Pervasives_Native.Some l -> FStarC_Effect.mk_ref l
let inclusion_info (env1 : env) (l : FStarC_Ident.lident) :
  module_inclusion_info=
  let mname = FStarC_Ident.string_of_lid l in
  let as_ids_opt m =
    let uu___ = FStarC_SMap.try_find m mname in
    FStarC_Option.map as_exported_ids uu___ in
  let uu___ = as_ids_opt env1.exported_ids in
  let uu___2 = as_ids_opt env1.trans_exported_ids in
  let uu___3 =
    let uu___4 = FStarC_SMap.try_find env1.includes mname in
    FStarC_Option.map (fun r -> FStarC_Effect.op_Bang r) uu___4 in
  {
    mii_exported_ids = uu___;
    mii_trans_exported_ids = uu___2;
    mii_includes = uu___3;
    mii_no_prelude = (env1.no_prelude)
  }
let prepare_module_or_interface (no_prelude : Prims.bool) (intf : Prims.bool)
  (admitted : Prims.bool) (env1 : env) (mname : FStarC_Ident.lident)
  (mii : module_inclusion_info) : (env * Prims.bool)=
  let prep env2 =
    let auto_open =
      if mii.mii_no_prelude || no_prelude
      then []
      else FStarC_Parser_Dep.prelude in
    let auto_open1 =
      let convert_kind uu___ =
        match uu___ with
        | FStarC_Parser_Dep.Open_namespace ->
            FStarC_Syntax_Syntax.Open_namespace
        | FStarC_Parser_Dep.Open_module -> FStarC_Syntax_Syntax.Open_module in
      FStarC_List.map
        (fun uu___ ->
           match uu___ with
           | (kind, lid) ->
               (lid, (convert_kind kind), FStarC_Syntax_Syntax.Unrestricted))
        auto_open in
    let auto_open2 =
      let uu___ = namespace_scope_of_module mname in
      FStarC_List.op_At uu___ (FStarC_List.rev auto_open1) in
    (let uu___2 = as_exported_id_set mii.mii_exported_ids in
     FStarC_SMap.add env2.exported_ids (FStarC_Ident.string_of_lid mname)
       uu___2);
    (match () with
     | () ->
         ((let uu___3 = as_exported_id_set mii.mii_trans_exported_ids in
           FStarC_SMap.add env2.trans_exported_ids
             (FStarC_Ident.string_of_lid mname) uu___3);
          (match () with
           | () ->
               ((let uu___4 = as_includes mii.mii_includes in
                 FStarC_SMap.add env2.includes
                   (FStarC_Ident.string_of_lid mname) uu___4);
                (match () with
                 | () ->
                     let env' =
                       let uu___4 =
                         FStarC_List.map
                           (fun x -> Open_module_or_namespace (x, true))
                           auto_open2 in
                       {
                         curmodule = (FStar_Pervasives_Native.Some mname);
                         curmonad = (env2.curmonad);
                         modules = (env2.modules);
                         scope_mods = uu___4;
                         exported_ids = (env2.exported_ids);
                         trans_exported_ids = (env2.trans_exported_ids);
                         includes = (env2.includes);
                         sigaccum = (env2.sigaccum);
                         sigmap = (env2.sigmap);
                         iface = intf;
                         admitted_iface = admitted;
                         expect_typ = (env2.expect_typ);
                         remaining_iface_decls = (env2.remaining_iface_decls);
                         iface_interleaving_init =
                           (env2.iface_interleaving_init);
                         syntax_only = (env2.syntax_only);
                         ds_hooks = (env2.ds_hooks);
                         dep_graph = (env2.dep_graph);
                         no_prelude = (env2.no_prelude)
                       } in
                     (FStarC_List.iter
                        (fun op -> (env2.ds_hooks).ds_push_open_hook env' op)
                        (FStarC_List.rev auto_open2);
                      env')))))) in
  let uu___ =
    FStarC_Option.find
      (fun uu___2 ->
         match uu___2 with | (l, uu___3) -> FStarC_Ident.lid_equals l mname)
      env1.modules in
  match uu___ with
  | FStar_Pervasives_Native.None -> let uu___2 = prep env1 in (uu___2, false)
  | FStar_Pervasives_Native.Some (uu___2, m) ->
      ((let uu___4 =
          let uu___5 = FStarC_Options.interactive () in
          Prims.op_Negation uu___5 in
        if uu___4
        then
          (if (Prims.op_Negation m.FStarC_Syntax_Syntax.is_interface) || intf
           then
             FStarC_Errors.raise_error FStarC_Ident.hasrange_lident mname
               FStarC_Errors_Codes.Fatal_DuplicateModuleOrInterface ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic
                  (FStarC_Format.fmt1
                     "Duplicate module or interface name: %s"
                     (FStarC_Ident.string_of_lid mname)))
           else ())
        else ());
       (let uu___4 = let uu___5 = push env1 in prep uu___5 in (uu___4, true)))
let enter_monad_scope (env1 : env) (mname : FStarC_Ident.ident) : env=
  match env1.curmonad with
  | FStar_Pervasives_Native.Some mname' ->
      let uu___ =
        let uu___2 =
          let uu___3 =
            FStarC_Class_Show.show FStarC_Ident.showable_ident mname in
          let uu___4 =
            let uu___5 =
              FStarC_Class_Show.show FStarC_Ident.showable_ident mname' in
            Prims.strcat ", but already in monad scope " uu___5 in
          Prims.strcat uu___3 uu___4 in
        Prims.strcat "Trying to define monad " uu___2 in
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
        iface_interleaving_init = (env1.iface_interleaving_init);
        syntax_only = (env1.syntax_only);
        ds_hooks = (env1.ds_hooks);
        dep_graph = (env1.dep_graph);
        no_prelude = (env1.no_prelude)
      }
let fail_or (env1 : env)
  (lookup : FStarC_Ident.lident -> 'a FStar_Pervasives_Native.option)
  (lid : FStarC_Ident.lident) : 'a=
  let uu___ = lookup lid in
  match uu___ with
  | FStar_Pervasives_Native.Some r -> r
  | FStar_Pervasives_Native.None ->
      let opened_modules =
        FStarC_List.map
          (fun uu___2 ->
             match uu___2 with
             | (lid1, uu___3) -> FStarC_Ident.string_of_lid lid1)
          env1.modules in
      if (FStarC_List.length (FStarC_Ident.ns_of_lid lid)) = Prims.int_zero
      then
        ((let uu___3 = FStarC_Debug.any () in
          if uu___3
          then
            let uu___4 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                env1.iface in
            let uu___5 = FStarC_Class_Show.show showable_env env1 in
            FStarC_Format.print2 "Dump env (is iface=%s):\n%s\n" uu___4
              uu___5
          else ());
         (let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident lid in
              FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                (FStarC_Errors_Msg.text "Identifier not found:") uu___5 in
            let uu___5 =
              let uu___6 =
                let uu___7 = all_local_names env1 in
                typo_msg (FStarC_Ident.string_of_lid lid) uu___7 in
              [uu___6] in
            uu___4 :: uu___5 in
          FStarC_Errors.raise_error FStarC_Ident.hasrange_lident lid
            FStarC_Errors_Codes.Fatal_IdentifierNotFound ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
            (Obj.magic uu___3)))
      else
        (let all_ids_in_module m =
           let m1 = FStarC_Ident.string_of_lid m in
           let uu___3 = FStarC_SMap.try_find env1.trans_exported_ids m1 in
           match uu___3 with
           | FStar_Pervasives_Native.Some f ->
               let exported_ids1 =
                 FStarC_Effect.op_Bang (f Exported_id_term_type) in
               FStarC_Class_Setlike.elems ()
                 (Obj.magic
                    (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
                 (Obj.magic exported_ids1)
           | FStar_Pervasives_Native.None -> [] in
         let modul = FStarC_Ident.lid_of_ids (FStarC_Ident.ns_of_lid lid) in
         let modul1 =
           let uu___3 = FStarC_Ident.ids_of_lid modul in
           match uu___3 with
           | h::t ->
               let rng =
                 FStarC_List.fold_right
                   (fun i r ->
                      FStarC_Range_Ops.union_ranges
                        (FStarC_Ident.range_of_id i) r) t
                   (FStarC_Ident.range_of_id h) in
               FStarC_Ident.set_lid_range modul rng in
         let uu___3 = resolve_module_name env1 modul1 true in
         match uu___3 with
         | FStar_Pervasives_Native.None ->
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     let uu___8 =
                       FStarC_Class_PP.pp FStarC_Ident.pretty_lident modul1 in
                     [uu___8;
                     FStarC_Errors_Msg.text "could not be resolved."] in
                   (FStarC_Errors_Msg.text "Module name") :: uu___7 in
                 FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one) uu___6 in
               let uu___6 =
                 let uu___7 =
                   let uu___8 = all_mod_names env1 in
                   typo_msg (FStarC_Ident.string_of_lid modul1) uu___8 in
                 [uu___7] in
               uu___5 :: uu___6 in
             FStarC_Errors.raise_error FStarC_Ident.hasrange_lident modul1
               FStarC_Errors_Codes.Fatal_IdentifierNotFound ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
               (Obj.magic uu___4)
         | FStar_Pervasives_Native.Some modul' when
             let uu___4 =
               FStarC_List.existsb
                 (fun m -> m = (FStarC_Ident.string_of_lid modul'))
                 opened_modules in
             Prims.op_Negation uu___4 ->
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     let uu___8 =
                       FStarC_Class_PP.pp FStarC_Ident.pretty_lident modul1 in
                     let uu___9 =
                       let uu___10 =
                         let uu___11 =
                           FStarC_Class_PP.pp FStarC_Ident.pretty_lident
                             modul' in
                         [uu___11;
                         FStarC_Errors_Msg.text "which is not in scope."] in
                       (FStarC_Errors_Msg.text "resolved to") :: uu___10 in
                     uu___8 :: uu___9 in
                   (FStarC_Errors_Msg.text "Module name") :: uu___7 in
                 FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one) uu___6 in
               let uu___6 =
                 let uu___7 =
                   let uu___8 = FStarC_Debug.any () in
                   if uu___8
                   then
                     FStar_Pprint.op_Hat_Slash_Hat
                       (FStarC_Errors_Msg.text "Opened modules =")
                       (FStarC_Errors_Msg.text
                          (FStarC_String.concat ", " opened_modules))
                   else FStar_Pprint.empty in
                 [uu___7] in
               uu___5 :: uu___6 in
             FStarC_Errors.raise_error FStarC_Ident.hasrange_lident modul1
               FStarC_Errors_Codes.Fatal_IdentifierNotFound ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
               (Obj.magic uu___4)
         | FStar_Pervasives_Native.Some modul' ->
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     let uu___8 =
                       FStarC_Class_PP.pp FStarC_Ident.pretty_ident
                         (FStarC_Ident.ident_of_lid lid) in
                     let uu___9 =
                       let uu___10 =
                         let uu___11 =
                           FStarC_Class_PP.pp FStarC_Ident.pretty_lident
                             modul1 in
                         let uu___12 =
                           let uu___13 =
                             let uu___14 =
                               FStarC_Class_Deq.op_Less_Greater_Question
                                 FStarC_Syntax_Syntax.deq_fv modul1 modul' in
                             if uu___14
                             then
                               let uu___15 =
                                 let uu___16 =
                                   FStarC_Class_PP.pp
                                     FStarC_Ident.pretty_lident modul' in
                                 FStar_Pprint.prefix (Prims.of_int (2))
                                   Prims.int_one
                                   (FStarC_Errors_Msg.text "resolved to")
                                   uu___16 in
                               FStar_Pprint.parens uu___15
                             else FStar_Pprint.empty in
                           [uu___13] in
                         uu___11 :: uu___12 in
                       (FStarC_Errors_Msg.text "not found in module") ::
                         uu___10 in
                     uu___8 :: uu___9 in
                   (FStarC_Errors_Msg.text "Identifier") :: uu___7 in
                 FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one) uu___6 in
               let uu___6 =
                 let uu___7 =
                   let uu___8 = all_ids_in_module modul' in
                   typo_msg
                     (FStarC_Ident.string_of_id
                        (FStarC_Ident.ident_of_lid lid)) uu___8 in
                 [uu___7] in
               uu___5 :: uu___6 in
             FStarC_Errors.raise_error FStarC_Ident.hasrange_lident lid
               FStarC_Errors_Codes.Fatal_IdentifierNotFound ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
               (Obj.magic uu___4))
let fail_or2 (env1 : env)
  (lookup : FStarC_Ident.ident -> 'a FStar_Pervasives_Native.option)
  (id : FStarC_Ident.ident) : 'a=
  let uu___ = lookup id in
  match uu___ with
  | FStar_Pervasives_Native.Some r -> r
  | FStar_Pervasives_Native.None ->
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_Class_PP.pp FStarC_Ident.pretty_ident id in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one
            (FStarC_Errors_Msg.text "Identifier not found:") uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 = all_local_names env1 in
            typo_msg (FStarC_Ident.string_of_id id) uu___6 in
          [uu___5] in
        uu___3 :: uu___4 in
      FStarC_Errors.raise_error FStarC_Ident.hasrange_ident id
        FStarC_Errors_Codes.Fatal_IdentifierNotFound ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic uu___2)
let resolve_name (e : env) (name : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.bv, FStarC_Syntax_Syntax.fv) FStar_Pervasives.either
    FStar_Pervasives_Native.option=
  let uu___ = try_lookup_name false false e name in
  match uu___ with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (Term_name (e1, attrs)) ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Subst.compress e1 in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_name n ->
           FStar_Pervasives_Native.Some (FStar_Pervasives.Inl n)
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           FStar_Pervasives_Native.Some (FStar_Pervasives.Inr fv)
       | uu___3 -> FStar_Pervasives_Native.None)
  | FStar_Pervasives_Native.Some (Eff_name (se, l)) ->
      FStar_Pervasives_Native.Some
        (FStar_Pervasives.Inr
           (FStarC_Syntax_Syntax.lid_and_dd_as_fv l
              FStar_Pervasives_Native.None))
let set_no_prelude (e : env) (b : Prims.bool) : env=
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
    expect_typ = (e.expect_typ);
    remaining_iface_decls = (e.remaining_iface_decls);
    iface_interleaving_init = (e.iface_interleaving_init);
    syntax_only = (e.syntax_only);
    ds_hooks = (e.ds_hooks);
    dep_graph = (e.dep_graph);
    no_prelude = b
  }
