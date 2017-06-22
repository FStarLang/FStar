open Prims
type local_binding = (FStar_Ident.ident* FStar_Syntax_Syntax.bv* Prims.bool)
type rec_binding =
  (FStar_Ident.ident* FStar_Ident.lid* FStar_Syntax_Syntax.delta_depth)
type module_abbrev = (FStar_Ident.ident* FStar_Ident.lident)
type open_kind =
  | Open_module
  | Open_namespace
let uu___is_Open_module: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____12 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____16 -> false
type open_module_or_namespace = (FStar_Ident.lident* open_kind)
type record_or_dc =
  {
  typename: FStar_Ident.lident;
  constrname: FStar_Ident.ident;
  parms: FStar_Syntax_Syntax.binders;
  fields: (FStar_Ident.ident* FStar_Syntax_Syntax.typ) Prims.list;
  is_private_or_abstract: Prims.bool;
  is_record: Prims.bool;}
type scope_mod =
  | Local_binding of local_binding
  | Rec_binding of rec_binding
  | Module_abbrev of module_abbrev
  | Open_module_or_namespace of open_module_or_namespace
  | Top_level_def of FStar_Ident.ident
  | Record_or_dc of record_or_dc
let uu___is_Local_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Local_binding _0 -> true | uu____104 -> false
let __proj__Local_binding__item___0: scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0
let uu___is_Rec_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____116 -> false
let __proj__Rec_binding__item___0: scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____128 -> false
let __proj__Module_abbrev__item___0: scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____140 -> false
let __proj__Open_module_or_namespace__item___0:
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_def: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____152 -> false
let __proj__Top_level_def__item___0: scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0
let uu___is_Record_or_dc: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____164 -> false
let __proj__Record_or_dc__item___0: scope_mod -> record_or_dc =
  fun projectee  -> match projectee with | Record_or_dc _0 -> _0
type string_set = Prims.string FStar_Util.set
type exported_id_kind =
  | Exported_id_term_type
  | Exported_id_field
let uu___is_Exported_id_term_type: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____176 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____180 -> false
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref
type env =
  {
  curmodule: FStar_Ident.lident option;
  curmonad: FStar_Ident.ident option;
  modules: (FStar_Ident.lident* FStar_Syntax_Syntax.modul) Prims.list;
  scope_mods: scope_mod Prims.list;
  exported_ids: exported_id_set FStar_Util.smap;
  trans_exported_ids: exported_id_set FStar_Util.smap;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap;
  sigaccum: FStar_Syntax_Syntax.sigelts;
  sigmap: (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap;
  iface: Prims.bool;
  admitted_iface: Prims.bool;
  expect_typ: Prims.bool;
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap;
  remaining_iface_decls:
    (FStar_Ident.lident* FStar_Parser_AST.decl Prims.list) Prims.list;
  syntax_only: Prims.bool;}
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ* Prims.bool)
  | Eff_name of (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident)
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____381 -> false
let __proj__Term_name__item___0:
  foundname -> (FStar_Syntax_Syntax.typ* Prims.bool) =
  fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____401 -> false
let __proj__Eff_name__item___0:
  foundname -> (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___172_421 = env in
      {
        curmodule = (uu___172_421.curmodule);
        curmonad = (uu___172_421.curmonad);
        modules = (uu___172_421.modules);
        scope_mods = (uu___172_421.scope_mods);
        exported_ids = (uu___172_421.exported_ids);
        trans_exported_ids = (uu___172_421.trans_exported_ids);
        includes = (uu___172_421.includes);
        sigaccum = (uu___172_421.sigaccum);
        sigmap = (uu___172_421.sigmap);
        iface = b;
        admitted_iface = (uu___172_421.admitted_iface);
        expect_typ = (uu___172_421.expect_typ);
        docs = (uu___172_421.docs);
        remaining_iface_decls = (uu___172_421.remaining_iface_decls);
        syntax_only = (uu___172_421.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___173_431 = e in
      {
        curmodule = (uu___173_431.curmodule);
        curmonad = (uu___173_431.curmonad);
        modules = (uu___173_431.modules);
        scope_mods = (uu___173_431.scope_mods);
        exported_ids = (uu___173_431.exported_ids);
        trans_exported_ids = (uu___173_431.trans_exported_ids);
        includes = (uu___173_431.includes);
        sigaccum = (uu___173_431.sigaccum);
        sigmap = (uu___173_431.sigmap);
        iface = (uu___173_431.iface);
        admitted_iface = b;
        expect_typ = (uu___173_431.expect_typ);
        docs = (uu___173_431.docs);
        remaining_iface_decls = (uu___173_431.remaining_iface_decls);
        syntax_only = (uu___173_431.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___174_441 = e in
      {
        curmodule = (uu___174_441.curmodule);
        curmonad = (uu___174_441.curmonad);
        modules = (uu___174_441.modules);
        scope_mods = (uu___174_441.scope_mods);
        exported_ids = (uu___174_441.exported_ids);
        trans_exported_ids = (uu___174_441.trans_exported_ids);
        includes = (uu___174_441.includes);
        sigaccum = (uu___174_441.sigaccum);
        sigmap = (uu___174_441.sigmap);
        iface = (uu___174_441.iface);
        admitted_iface = (uu___174_441.admitted_iface);
        expect_typ = b;
        docs = (uu___174_441.docs);
        remaining_iface_decls = (uu___174_441.remaining_iface_decls);
        syntax_only = (uu___174_441.syntax_only)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____454 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____454 with
      | None  -> []
      | Some exported_id_set ->
          let uu____458 =
            let uu____459 = exported_id_set Exported_id_term_type in
            FStar_ST.read uu____459 in
          FStar_All.pipe_right uu____458 FStar_Util.set_elements
let open_modules:
  env -> (FStar_Ident.lident* FStar_Syntax_Syntax.modul) Prims.list =
  fun e  -> e.modules
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___175_477 = e in
      {
        curmodule = (Some l);
        curmonad = (uu___175_477.curmonad);
        modules = (uu___175_477.modules);
        scope_mods = (uu___175_477.scope_mods);
        exported_ids = (uu___175_477.exported_ids);
        trans_exported_ids = (uu___175_477.trans_exported_ids);
        includes = (uu___175_477.includes);
        sigaccum = (uu___175_477.sigaccum);
        sigmap = (uu___175_477.sigmap);
        iface = (uu___175_477.iface);
        admitted_iface = (uu___175_477.admitted_iface);
        expect_typ = (uu___175_477.expect_typ);
        docs = (uu___175_477.docs);
        remaining_iface_decls = (uu___175_477.remaining_iface_decls);
        syntax_only = (uu___175_477.syntax_only)
      }
let current_module: env -> FStar_Ident.lident =
  fun env  ->
    match env.curmodule with
    | None  -> failwith "Unset current module"
    | Some m -> m
let iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list option =
  fun env  ->
    fun l  ->
      let uu____490 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____506  ->
                match uu____506 with
                | (m,uu____511) -> FStar_Ident.lid_equals l m)) in
      match uu____490 with
      | None  -> None
      | Some (uu____520,decls) -> Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____539 =
          FStar_List.partition
            (fun uu____553  ->
               match uu____553 with
               | (m,uu____558) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____539 with
        | (uu____561,rest) ->
            let uu___176_579 = env in
            {
              curmodule = (uu___176_579.curmodule);
              curmonad = (uu___176_579.curmonad);
              modules = (uu___176_579.modules);
              scope_mods = (uu___176_579.scope_mods);
              exported_ids = (uu___176_579.exported_ids);
              trans_exported_ids = (uu___176_579.trans_exported_ids);
              includes = (uu___176_579.includes);
              sigaccum = (uu___176_579.sigaccum);
              sigmap = (uu___176_579.sigmap);
              iface = (uu___176_579.iface);
              admitted_iface = (uu___176_579.admitted_iface);
              expect_typ = (uu___176_579.expect_typ);
              docs = (uu___176_579.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___176_579.syntax_only)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | None  -> let uu____594 = current_module env in qual uu____594 id
      | Some monad ->
          let uu____596 =
            let uu____597 = current_module env in qual uu____597 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____596 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___177_607 = env in
      {
        curmodule = (uu___177_607.curmodule);
        curmonad = (uu___177_607.curmonad);
        modules = (uu___177_607.modules);
        scope_mods = (uu___177_607.scope_mods);
        exported_ids = (uu___177_607.exported_ids);
        trans_exported_ids = (uu___177_607.trans_exported_ids);
        includes = (uu___177_607.includes);
        sigaccum = (uu___177_607.sigaccum);
        sigmap = (uu___177_607.sigmap);
        iface = (uu___177_607.iface);
        admitted_iface = (uu___177_607.admitted_iface);
        expect_typ = (uu___177_607.expect_typ);
        docs = (uu___177_607.docs);
        remaining_iface_decls = (uu___177_607.remaining_iface_decls);
        syntax_only = b
      }
let new_sigmap uu____615 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____618  ->
    let uu____619 = new_sigmap () in
    let uu____621 = new_sigmap () in
    let uu____623 = new_sigmap () in
    let uu____629 = new_sigmap () in
    let uu____635 = new_sigmap () in
    {
      curmodule = None;
      curmonad = None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____619;
      trans_exported_ids = uu____621;
      includes = uu____623;
      sigaccum = [];
      sigmap = uu____629;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____635;
      remaining_iface_decls = [];
      syntax_only = false
    }
let sigmap: env -> (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap =
  fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____653  ->
         match uu____653 with
         | (m,uu____657) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___178_665 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___178_665.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___179_666 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___179_666.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___179_666.FStar_Syntax_Syntax.sort)
      }
let bv_to_name:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)
let unmangleMap:
  (Prims.string* Prims.string* FStar_Syntax_Syntax.delta_depth*
    FStar_Syntax_Syntax.fv_qual option) Prims.list
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None)]
let unmangleOpName:
  FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) option =
  fun id  ->
    let t =
      FStar_Util.find_map unmangleMap
        (fun uu____712  ->
           match uu____712 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____726 =
                   let uu____727 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____727 dd dq in
                 Some uu____726
               else None) in
    match t with | Some v1 -> Some (v1, false) | None  -> None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____758 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____782 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____793 -> false
let option_of_cont k_ignore uu___145_812 =
  match uu___145_812 with
  | Cont_ok a -> Some a
  | Cont_fail  -> None
  | Cont_ignore  -> k_ignore ()
let find_in_record ns id record cont =
  let typename' =
    FStar_Ident.lid_of_ids
      (FStar_List.append ns [(record.typename).FStar_Ident.ident]) in
  if FStar_Ident.lid_equals typename' record.typename
  then
    let fname =
      FStar_Ident.lid_of_ids
        (FStar_List.append (record.typename).FStar_Ident.ns [id]) in
    let find1 =
      FStar_Util.find_map record.fields
        (fun uu____857  ->
           match uu____857 with
           | (f,uu____862) ->
               if id.FStar_Ident.idText = f.FStar_Ident.idText
               then Some record
               else None) in
    match find1 with | Some r -> cont r | None  -> Cont_ignore
  else Cont_ignore
let get_exported_id_set: env -> Prims.string -> exported_id_set option =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname
let get_trans_exported_id_set: env -> Prims.string -> exported_id_set option
  =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname
let string_of_exported_id_kind: exported_id_kind -> Prims.string =
  fun uu___146_898  ->
    match uu___146_898 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___147_947 =
    match uu___147_947 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
          let uu____955 = get_exported_id_set env mname in
          match uu____955 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____971 = mex eikind in FStar_ST.read uu____971 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____978 = FStar_Util.smap_try_find env.includes mname in
          match uu____978 with
          | None  -> []
          | Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
          then let uu____998 = qual modul id in find_in_module uu____998
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____1001 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___148_1005  ->
    match uu___148_1005 with
    | Exported_id_field  -> true
    | uu____1006 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___149_1095 =
    match uu___149_1095 with
    | (id',uu____1097,uu____1098) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___150_1102 =
    match uu___150_1102 with
    | (id',uu____1104,uu____1105) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1108 = current_module env in FStar_Ident.ids_of_lid uu____1108 in
  let proc uu___151_1113 =
    match uu___151_1113 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____1118) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____1121 = FStar_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____1121 id
    | uu____1124 -> Cont_ignore in
  let rec aux uu___152_1130 =
    match uu___152_1130 with
    | a::q ->
        let uu____1136 = proc a in
        option_of_cont (fun uu____1138  -> aux q) uu____1136
    | [] ->
        let uu____1139 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____1141  -> None) uu____1139 in
  aux env.scope_mods
let found_local_binding r uu____1160 =
  match uu____1160 with
  | (id',x,mut) -> let uu____1167 = bv_to_name x r in (uu____1167, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____1204 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____1204 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found
let try_lookup_id:
  env -> FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) option =
  fun env  ->
    fun id  ->
      let uu____1226 = unmangleOpName id in
      match uu____1226 with
      | Some f -> Some f
      | uu____1240 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1247 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1247) (fun uu____1252  -> Cont_fail)
            (fun uu____1255  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1262  -> fun uu____1263  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1270  -> fun uu____1271  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1323 ->
        let lid = qualify env id in
        let uu____1325 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____1325 with
         | Some r -> let uu____1338 = k_global_def lid r in Some uu____1338
         | None  -> None)
    | None  -> None in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1351 = current_module env in qual uu____1351 id in
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
           let uu____1360 = current_module env in
           FStar_Ident.lid_equals lid uu____1360)
        ||
        (FStar_List.existsb (fun x  -> FStar_Ident.lid_equals lid (fst x))
           env.modules)
let resolve_module_name:
  env -> FStar_Ident.lident -> Prims.bool -> FStar_Ident.lident option =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
        let rec aux uu___153_1384 =
          match uu___153_1384 with
          | [] ->
              let uu____1387 = module_is_defined env lid in
              if uu____1387 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1394 =
                  let uu____1396 = FStar_Ident.path_of_lid ns in
                  let uu____1398 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1396 uu____1398 in
                FStar_Ident.lid_of_path uu____1394
                  (FStar_Ident.range_of_lid lid) in
              let uu____1400 = module_is_defined env new_lid in
              if uu____1400 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1405 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1409::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____1421 =
          let uu____1422 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____1422 in
        if uu____1421
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Syntax_Const.prims_lid
           then ()
           else
             (let uu____1424 =
                let uu____1425 =
                  let uu____1428 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____1428, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____1425 in
              raise uu____1424))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____1436 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____1439 = resolve_module_name env modul_orig true in
          (match uu____1439 with
           | Some modul_res -> fail_if_curmodule env modul_orig modul_res
           | uu____1442 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___154_1450  ->
           match uu___154_1450 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1452 -> false) env.scope_mods
let shorten_module_path:
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list* FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun ids  ->
      fun is_full_path  ->
        let rec aux revns id =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id in
          if namespace_is_open env lid
          then Some ((FStar_List.rev (id :: revns)), [])
          else
            (match revns with
             | [] -> None
             | ns_last_id::rev_ns_prefix ->
                 let uu____1507 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____1507
                   (FStar_Util.map_option
                      (fun uu____1531  ->
                         match uu____1531 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____1548 =
          is_full_path &&
            (let uu____1549 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____1549) in
        if uu____1548
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1566 = aux ns_rev_prefix ns_last_id in
               (match uu____1566 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____1600 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____1600 with
      | (uu____1605,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1696::uu____1697 ->
      let uu____1699 =
        let uu____1701 =
          let uu____1702 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____1702 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____1701 true in
      (match uu____1699 with
       | None  -> None
       | Some modul ->
           let uu____1705 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____1707  -> None) uu____1705)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___155_1722 =
  match uu___155_1722 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1801 = k_global_def lid1 def in cont_of_option k uu____1801 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1822 = k_local_binding l in
       cont_of_option Cont_fail uu____1822)
    (fun r  ->
       let uu____1825 = k_rec_binding r in
       cont_of_option Cont_fail uu____1825) (fun uu____1827  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1833,uu____1834,uu____1835,l,uu____1837,uu____1838) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___156_1843  ->
               match uu___156_1843 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1845,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1852 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____1856,uu____1857,uu____1858)
        -> None
    | uu____1859 -> None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1868 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____1872 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____1872 then Some fv else None) in
      FStar_All.pipe_right uu____1868 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1886 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____1886 ns)
let try_lookup_name:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> foundname option =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___160_1911 =
            match uu___160_1911 with
            | (uu____1915,true ) when exclude_interf -> None
            | (se,uu____1917) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1919 ->
                     let uu____1928 =
                       let uu____1929 =
                         let uu____1932 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____1932, false) in
                       Term_name uu____1929 in
                     Some uu____1928
                 | FStar_Syntax_Syntax.Sig_datacon uu____1933 ->
                     let uu____1941 =
                       let uu____1942 =
                         let uu____1945 =
                           let uu____1946 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1946 in
                         (uu____1945, false) in
                       Term_name uu____1942 in
                     Some uu____1941
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1948,lbs),uu____1950,uu____1951) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____1962 =
                       let uu____1963 =
                         let uu____1966 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____1966, false) in
                       Term_name uu____1963 in
                     Some uu____1962
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1968,uu____1969) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____1972 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___157_1974  ->
                                  match uu___157_1974 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1975 -> false))) in
                     if uu____1972
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____1979 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___158_1981  ->
                                         match uu___158_1981 with
                                         | FStar_Syntax_Syntax.Projector
                                             uu____1982 -> true
                                         | FStar_Syntax_Syntax.Discriminator
                                             uu____1985 -> true
                                         | uu____1986 -> false)))) in
                         if uu____1979
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____1988 =
                         FStar_Util.find_map quals
                           (fun uu___159_1990  ->
                              match uu___159_1990 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1993 -> None) in
                       (match uu____1988 with
                        | Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
                        | uu____2005 ->
                            let uu____2007 =
                              let uu____2008 =
                                let uu____2011 =
                                  let uu____2012 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____2012 in
                                (uu____2011, false) in
                              Term_name uu____2008 in
                            Some uu____2007)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2017 ->
                     Some (Eff_name (se, source_lid))
                 | uu____2024 -> None) in
          let k_local_binding r =
            let uu____2036 =
              let uu____2037 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____2037 in
            Some uu____2036 in
          let k_rec_binding uu____2047 =
            match uu____2047 with
            | (id,l,dd) ->
                let uu____2055 =
                  let uu____2056 =
                    let uu____2059 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____2059, false) in
                  Term_name uu____2056 in
                Some uu____2055 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2063 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2063 with
                 | Some f -> Some (Term_name f)
                 | uu____2073 -> None)
            | uu____2077 -> None in
          match found_unmangled with
          | None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
let try_lookup_effect_name':
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident) option
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____2097 = try_lookup_name true exclude_interf env lid in
        match uu____2097 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____2106 -> None
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2117 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2117 with | Some (o,l1) -> Some l1 | uu____2126 -> None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list) option
  =
  fun env  ->
    fun l  ->
      let uu____2140 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2140 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2149;
             FStar_Syntax_Syntax.sigquals = uu____2150;
             FStar_Syntax_Syntax.sigmeta = uu____2151;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2161;
             FStar_Syntax_Syntax.sigquals = uu____2162;
             FStar_Syntax_Syntax.sigmeta = uu____2163;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____2172,uu____2173,uu____2174,uu____2175,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2177;
             FStar_Syntax_Syntax.sigquals = uu____2178;
             FStar_Syntax_Syntax.sigmeta = uu____2179;_},l1)
          -> Some (l1, cattributes)
      | uu____2190 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl option =
  fun env  ->
    fun l  ->
      let uu____2204 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2204 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2210;
             FStar_Syntax_Syntax.sigquals = uu____2211;
             FStar_Syntax_Syntax.sigmeta = uu____2212;_},uu____2213)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2218;
             FStar_Syntax_Syntax.sigquals = uu____2219;
             FStar_Syntax_Syntax.sigmeta = uu____2220;_},uu____2221)
          -> Some ne
      | uu____2225 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2235 = try_lookup_effect_name env lid in
      match uu____2235 with | None  -> false | Some uu____2237 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2245 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2245 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____2251,uu____2252,uu____2253,uu____2254);
             FStar_Syntax_Syntax.sigrng = uu____2255;
             FStar_Syntax_Syntax.sigquals = uu____2256;
             FStar_Syntax_Syntax.sigmeta = uu____2257;_},uu____2258)
          ->
          let rec aux new_name =
            let uu____2269 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2269 with
            | None  -> None
            | Some (s,uu____2279) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____2285,uu____2286,uu____2287,cmp,uu____2289) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2293 -> None) in
          aux l'
      | Some (uu____2294,l') -> Some l'
      | uu____2298 -> None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___161_2319 =
        match uu___161_2319 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2324,uu____2325,uu____2326);
             FStar_Syntax_Syntax.sigrng = uu____2327;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2329;_},uu____2330)
            -> Some quals
        | uu____2333 -> None in
      let uu____2337 =
        resolve_in_open_namespaces' env lid (fun uu____2341  -> None)
          (fun uu____2343  -> None) k_global_def in
      match uu____2337 with | Some quals -> quals | uu____2349 -> []
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul option =
  fun env  ->
    fun path  ->
      let uu____2361 =
        FStar_List.tryFind
          (fun uu____2367  ->
             match uu____2367 with
             | (mlid,modul) ->
                 let uu____2372 = FStar_Ident.path_of_lid mlid in
                 uu____2372 = path) env.modules in
      match uu____2361 with
      | Some (uu____2376,modul) -> Some modul
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___162_2398 =
        match uu___162_2398 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2402,lbs),uu____2404,uu____2405);
             FStar_Syntax_Syntax.sigrng = uu____2406;
             FStar_Syntax_Syntax.sigquals = uu____2407;
             FStar_Syntax_Syntax.sigmeta = uu____2408;_},uu____2409)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2421 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2421
        | uu____2422 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2425  -> None)
        (fun uu____2426  -> None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___163_2445 =
        match uu___163_2445 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2452,uu____2453);
             FStar_Syntax_Syntax.sigrng = uu____2454;
             FStar_Syntax_Syntax.sigquals = uu____2455;
             FStar_Syntax_Syntax.sigmeta = uu____2456;_},uu____2457)
            ->
            FStar_Util.find_map (snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2473 -> None)
        | uu____2478 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2485  -> None)
        (fun uu____2488  -> None) k_global_def
let empty_include_smap:
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = new_sigmap ()
let empty_exported_id_smap: exported_id_set FStar_Util.smap = new_sigmap ()
let try_lookup_lid':
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let uu____2515 = try_lookup_name any_val exclude_interf env lid in
          match uu____2515 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2524 -> None
let try_lookup_lid:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2544 = try_lookup_lid env l in
      match uu____2544 with
      | None  -> None
      | Some (e,uu____2552) ->
          let uu____2555 =
            let uu____2556 = FStar_Syntax_Subst.compress e in
            uu____2556.FStar_Syntax_Syntax.n in
          (match uu____2555 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2565 -> None)
let try_lookup_lid_no_resolve:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___180_2576 = env in
        {
          curmodule = (uu___180_2576.curmodule);
          curmonad = (uu___180_2576.curmonad);
          modules = (uu___180_2576.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___180_2576.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___180_2576.sigaccum);
          sigmap = (uu___180_2576.sigmap);
          iface = (uu___180_2576.iface);
          admitted_iface = (uu___180_2576.admitted_iface);
          expect_typ = (uu___180_2576.expect_typ);
          docs = (uu___180_2576.docs);
          remaining_iface_decls = (uu___180_2576.remaining_iface_decls);
          syntax_only = (uu___180_2576.syntax_only)
        } in
      try_lookup_lid env' l
let try_lookup_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___165_2600 =
        match uu___165_2600 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2604,uu____2605,uu____2606);
             FStar_Syntax_Syntax.sigrng = uu____2607;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2609;_},uu____2610)
            ->
            let uu____2612 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___164_2614  ->
                      match uu___164_2614 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2615 -> false)) in
            if uu____2612
            then
              let uu____2617 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2617
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2619;
             FStar_Syntax_Syntax.sigrng = uu____2620;
             FStar_Syntax_Syntax.sigquals = uu____2621;
             FStar_Syntax_Syntax.sigmeta = uu____2622;_},uu____2623)
            ->
            let uu____2632 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2632
        | uu____2633 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2636  -> None)
        (fun uu____2637  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___166_2656 =
        match uu___166_2656 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2661,uu____2662,uu____2663,uu____2664,datas,uu____2666);
             FStar_Syntax_Syntax.sigrng = uu____2667;
             FStar_Syntax_Syntax.sigquals = uu____2668;
             FStar_Syntax_Syntax.sigmeta = uu____2669;_},uu____2670)
            -> Some datas
        | uu____2677 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2682  -> None)
        (fun uu____2684  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____2718 =
    let uu____2719 =
      let uu____2722 =
        let uu____2724 = FStar_ST.read record_cache in
        FStar_List.hd uu____2724 in
      let uu____2732 = FStar_ST.read record_cache in uu____2722 :: uu____2732 in
    FStar_ST.write record_cache uu____2719 in
  let pop1 uu____2747 =
    let uu____2748 =
      let uu____2751 = FStar_ST.read record_cache in FStar_List.tl uu____2751 in
    FStar_ST.write record_cache uu____2748 in
  let peek uu____2767 =
    let uu____2768 = FStar_ST.read record_cache in FStar_List.hd uu____2768 in
  let insert r =
    let uu____2780 =
      let uu____2783 = let uu____2785 = peek () in r :: uu____2785 in
      let uu____2787 =
        let uu____2790 = FStar_ST.read record_cache in
        FStar_List.tl uu____2790 in
      uu____2783 :: uu____2787 in
    FStar_ST.write record_cache uu____2780 in
  let commit1 uu____2806 =
    let uu____2807 = FStar_ST.read record_cache in
    match uu____2807 with
    | hd1::uu____2815::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2828 -> failwith "Impossible" in
  let filter1 uu____2834 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____2841 =
           let uu____2844 = FStar_ST.read record_cache in filtered ::
             uu____2844 in
         FStar_ST.write record_cache uu____2841) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____2918 = record_cache_aux_with_filter in
  match uu____2918 with | (aux,uu____2956) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____2995 = record_cache_aux_with_filter in
  match uu____2995 with | (uu____3018,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____3058 = record_cache_aux in
  match uu____3058 with
  | (push1,uu____3078,uu____3079,uu____3080,uu____3081) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3106 = record_cache_aux in
  match uu____3106 with
  | (uu____3125,pop1,uu____3127,uu____3128,uu____3129) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____3155 = record_cache_aux in
  match uu____3155 with
  | (uu____3175,uu____3176,peek,uu____3178,uu____3179) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____3204 = record_cache_aux in
  match uu____3204 with
  | (uu____3223,uu____3224,uu____3225,insert,uu____3227) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____3252 = record_cache_aux in
  match uu____3252 with
  | (uu____3271,uu____3272,uu____3273,uu____3274,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3314) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___167_3323  ->
                   match uu___167_3323 with
                   | FStar_Syntax_Syntax.RecordType uu____3324 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____3329 -> true
                   | uu____3334 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___168_3342  ->
                      match uu___168_3342 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3344,uu____3345,uu____3346,uu____3347,uu____3348);
                          FStar_Syntax_Syntax.sigrng = uu____3349;
                          FStar_Syntax_Syntax.sigquals = uu____3350;
                          FStar_Syntax_Syntax.sigmeta = uu____3351;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3355 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___169_3357  ->
                    match uu___169_3357 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____3361,uu____3362,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____3364;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____3366;_} ->
                        let uu____3371 =
                          let uu____3372 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3372 in
                        (match uu____3371 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3376,t,uu____3378,uu____3379,uu____3380);
                             FStar_Syntax_Syntax.sigrng = uu____3381;
                             FStar_Syntax_Syntax.sigquals = uu____3382;
                             FStar_Syntax_Syntax.sigmeta = uu____3383;_} ->
                             let uu____3387 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3387 with
                              | (formals,uu____3396) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3422  ->
                                            match uu____3422 with
                                            | (x,q) ->
                                                let uu____3430 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3430
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3461  ->
                                            match uu____3461 with
                                            | (x,q) ->
                                                let uu____3470 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____3470,
                                                  (x.FStar_Syntax_Syntax.sort)))) in
                                  let fields = fields' in
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
                                    } in
                                  ((let uu____3482 =
                                      let uu____3484 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3484 in
                                    FStar_ST.write new_globs uu____3482);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3500 =
                                            match uu____3500 with
                                            | (id,uu____3506) ->
                                                let modul =
                                                  let uu____3512 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3512.FStar_Ident.str in
                                                let uu____3513 =
                                                  get_exported_id_set e modul in
                                                (match uu____3513 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____3529 =
                                                         let uu____3530 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3530 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3529);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3537 =
                                                               let uu____3538
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____3538.FStar_Ident.ident in
                                                             uu____3537.FStar_Ident.idText in
                                                           let uu____3540 =
                                                             let uu____3541 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3541 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3540))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3554 -> ())
                    | uu____3555 -> ()))
        | uu____3556 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3569 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3569 with
        | (ns,id) ->
            let uu____3579 = peek_record_cache () in
            FStar_Util.find_map uu____3579
              (fun record  ->
                 let uu____3582 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3585  -> None) uu____3582) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3586  -> Cont_ignore) (fun uu____3587  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3590 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3590)
        (fun k  -> fun uu____3593  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let uu____3602 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3602 with
      | Some r when r.is_record -> Some r
      | uu____3606 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3617 = try_lookup_record_by_field_name env lid in
        match uu____3617 with
        | Some record' when
            let uu____3620 =
              let uu____3621 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3621 in
            let uu____3623 =
              let uu____3624 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3624 in
            uu____3620 = uu____3623 ->
            let uu____3626 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3628  -> Cont_ok ()) in
            (match uu____3626 with
             | Cont_ok uu____3629 -> true
             | uu____3630 -> false)
        | uu____3632 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) option =
  fun env  ->
    fun fieldname  ->
      let uu____3643 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3643 with
      | Some r ->
          let uu____3649 =
            let uu____3652 =
              let uu____3653 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3653
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3652, (r.is_record)) in
          Some uu____3649
      | uu____3656 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3665  ->
    let uu____3666 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3666
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3677  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___170_3686  ->
      match uu___170_3686 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___171_3706 =
            match uu___171_3706 with
            | Rec_binding uu____3707 -> true
            | uu____3708 -> false in
          let this_env =
            let uu___181_3710 = env in
            let uu____3711 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___181_3710.curmodule);
              curmonad = (uu___181_3710.curmonad);
              modules = (uu___181_3710.modules);
              scope_mods = uu____3711;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___181_3710.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___181_3710.sigaccum);
              sigmap = (uu___181_3710.sigmap);
              iface = (uu___181_3710.iface);
              admitted_iface = (uu___181_3710.admitted_iface);
              expect_typ = (uu___181_3710.expect_typ);
              docs = (uu___181_3710.docs);
              remaining_iface_decls = (uu___181_3710.remaining_iface_decls);
              syntax_only = (uu___181_3710.syntax_only)
            } in
          let uu____3713 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3713 with | None  -> true | Some uu____3719 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___182_3730 = env in
      {
        curmodule = (uu___182_3730.curmodule);
        curmonad = (uu___182_3730.curmonad);
        modules = (uu___182_3730.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___182_3730.exported_ids);
        trans_exported_ids = (uu___182_3730.trans_exported_ids);
        includes = (uu___182_3730.includes);
        sigaccum = (uu___182_3730.sigaccum);
        sigmap = (uu___182_3730.sigmap);
        iface = (uu___182_3730.iface);
        admitted_iface = (uu___182_3730.admitted_iface);
        expect_typ = (uu___182_3730.expect_typ);
        docs = (uu___182_3730.docs);
        remaining_iface_decls = (uu___182_3730.remaining_iface_decls);
        syntax_only = (uu___182_3730.syntax_only)
      }
let push_bv':
  env -> FStar_Ident.ident -> Prims.bool -> (env* FStar_Syntax_Syntax.bv) =
  fun env  ->
    fun x  ->
      fun is_mutable  ->
        let bv =
          FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
            (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun in
        ((push_scope_mod env (Local_binding (x, bv, is_mutable))), bv)
let push_bv_mutable:
  env -> FStar_Ident.ident -> (env* FStar_Syntax_Syntax.bv) =
  fun env  -> fun x  -> push_bv' env x true
let push_bv: env -> FStar_Ident.ident -> (env* FStar_Syntax_Syntax.bv) =
  fun env  -> fun x  -> push_bv' env x false
let push_top_level_rec_binding:
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x in
        let uu____3769 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____3769
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          raise
            (FStar_Errors.Error
               ((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str),
                 (FStar_Ident.range_of_lid l)))
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let err1 l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str in
        let r =
          match sopt with
          | Some (se,uu____3789) ->
              let uu____3792 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____3792 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____3797 =
          let uu____3798 =
            let uu____3801 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____3801, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____3798 in
        raise uu____3797 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____3808 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3813 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3819 -> (true, true)
          | uu____3824 -> (false, false) in
        match uu____3808 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____3829 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3832 =
                     let uu____3833 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____3833 in
                   if uu____3832 then Some l else None) in
            (match uu____3829 with
             | Some l when
                 let uu____3837 = FStar_Options.interactive () in
                 Prims.op_Negation uu____3837 -> err1 l
             | uu____3838 ->
                 (extract_record env globals s;
                  (let uu___183_3843 = env in
                   {
                     curmodule = (uu___183_3843.curmodule);
                     curmonad = (uu___183_3843.curmonad);
                     modules = (uu___183_3843.modules);
                     scope_mods = (uu___183_3843.scope_mods);
                     exported_ids = (uu___183_3843.exported_ids);
                     trans_exported_ids = (uu___183_3843.trans_exported_ids);
                     includes = (uu___183_3843.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___183_3843.sigmap);
                     iface = (uu___183_3843.iface);
                     admitted_iface = (uu___183_3843.admitted_iface);
                     expect_typ = (uu___183_3843.expect_typ);
                     docs = (uu___183_3843.docs);
                     remaining_iface_decls =
                       (uu___183_3843.remaining_iface_decls);
                     syntax_only = (uu___183_3843.syntax_only)
                   }))) in
      let env2 =
        let uu___184_3845 = env1 in
        let uu____3846 = FStar_ST.read globals in
        {
          curmodule = (uu___184_3845.curmodule);
          curmonad = (uu___184_3845.curmonad);
          modules = (uu___184_3845.modules);
          scope_mods = uu____3846;
          exported_ids = (uu___184_3845.exported_ids);
          trans_exported_ids = (uu___184_3845.trans_exported_ids);
          includes = (uu___184_3845.includes);
          sigaccum = (uu___184_3845.sigaccum);
          sigmap = (uu___184_3845.sigmap);
          iface = (uu___184_3845.iface);
          admitted_iface = (uu___184_3845.admitted_iface);
          expect_typ = (uu___184_3845.expect_typ);
          docs = (uu___184_3845.docs);
          remaining_iface_decls = (uu___184_3845.remaining_iface_decls);
          syntax_only = (uu___184_3845.syntax_only)
        } in
      let uu____3851 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3865) ->
            let uu____3870 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____3870)
        | uu____3884 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____3851 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3914  ->
                   match uu____3914 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3925 =
                                  let uu____3927 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3927 in
                                FStar_ST.write globals uu____3925);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3936 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____3936.FStar_Ident.str in
                                    ((let uu____3938 =
                                        get_exported_id_set env3 modul in
                                      match uu____3938 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____3953 =
                                            let uu____3954 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3954 in
                                          FStar_ST.write my_exported_ids
                                            uu____3953
                                      | None  -> ());
                                     (match () with
                                      | () ->
                                          FStar_Util.smap_add (sigmap env3)
                                            lid.FStar_Ident.str
                                            (se,
                                              (env3.iface &&
                                                 (Prims.op_Negation
                                                    env3.admitted_iface))))))))));
           (let env4 =
              let uu___185_3966 = env3 in
              let uu____3967 = FStar_ST.read globals in
              {
                curmodule = (uu___185_3966.curmodule);
                curmonad = (uu___185_3966.curmonad);
                modules = (uu___185_3966.modules);
                scope_mods = uu____3967;
                exported_ids = (uu___185_3966.exported_ids);
                trans_exported_ids = (uu___185_3966.trans_exported_ids);
                includes = (uu___185_3966.includes);
                sigaccum = (uu___185_3966.sigaccum);
                sigmap = (uu___185_3966.sigmap);
                iface = (uu___185_3966.iface);
                admitted_iface = (uu___185_3966.admitted_iface);
                expect_typ = (uu___185_3966.expect_typ);
                docs = (uu___185_3966.docs);
                remaining_iface_decls = (uu___185_3966.remaining_iface_decls);
                syntax_only = (uu___185_3966.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3978 =
        let uu____3981 = resolve_module_name env ns false in
        match uu____3981 with
        | None  ->
            let modules = env.modules in
            let uu____3989 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3995  ->
                      match uu____3995 with
                      | (m,uu____3999) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____3989
            then (ns, Open_namespace)
            else
              (let uu____4003 =
                 let uu____4004 =
                   let uu____4007 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____4007, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____4004 in
               raise uu____4003)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____3978 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____4021 = resolve_module_name env ns false in
      match uu____4021 with
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____4027 = current_module env1 in
              uu____4027.FStar_Ident.str in
            (let uu____4029 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____4029 with
             | None  -> ()
             | Some incl ->
                 let uu____4042 =
                   let uu____4044 = FStar_ST.read incl in ns1 :: uu____4044 in
                 FStar_ST.write incl uu____4042);
            (match () with
             | () ->
                 let uu____4052 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____4052 with
                  | Some ns_trans_exports ->
                      ((let uu____4065 =
                          let uu____4076 = get_exported_id_set env1 curmod in
                          let uu____4081 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____4076, uu____4081) in
                        match uu____4065 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____4121 = ns_trans_exports k in
                                FStar_ST.read uu____4121 in
                              let ex = cur_exports k in
                              (let uu____4130 =
                                 let uu____4131 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____4131 ns_ex in
                               FStar_ST.write ex uu____4130);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____4141 =
                                     let uu____4142 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____4142 ns_ex in
                                   FStar_ST.write trans_ex uu____4141) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____4148 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____4162 =
                        let uu____4163 =
                          let uu____4166 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____4166, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____4163 in
                      raise uu____4162))))
      | uu____4167 ->
          let uu____4169 =
            let uu____4170 =
              let uu____4173 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____4173, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____4170 in
          raise uu____4169
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____4183 = module_is_defined env l in
        if uu____4183
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____4186 =
             let uu____4187 =
               let uu____4190 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____4190, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____4187 in
           raise uu____4186)
let push_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____4204 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____4204 with
              | None  -> ()
              | Some old_doc ->
                  let uu____4207 =
                    let uu____4208 = FStar_Ident.string_of_lid l in
                    let uu____4209 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____4210 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____4208 uu____4209 uu____4210 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____4207);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____4219 = try_lookup_lid env l in
                (match uu____4219 with
                 | None  ->
                     ((let uu____4226 =
                         let uu____4227 = FStar_Options.interactive () in
                         Prims.op_Negation uu____4227 in
                       if uu____4226
                       then
                         let uu____4228 =
                           let uu____4229 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____4230 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____4229 uu____4230 in
                         FStar_Util.print_string uu____4228
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___186_4236 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___186_4236.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___186_4236.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___186_4236.FStar_Syntax_Syntax.sigmeta)
                           }), false)))
                 | Some uu____4237 -> ())
            | uu____4242 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4254) ->
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
                                (lid,uu____4262,uu____4263,uu____4264,uu____4265,uu____4266)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4271 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4274,uu____4275) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4279,lbs),uu____4281,uu____4282) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4295 =
                               let uu____4296 =
                                 let uu____4297 =
                                   let uu____4302 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4302.FStar_Syntax_Syntax.fv_name in
                                 uu____4297.FStar_Syntax_Syntax.v in
                               uu____4296.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4295))
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
                               let uu____4312 =
                                 let uu____4317 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4317.FStar_Syntax_Syntax.fv_name in
                               uu____4312.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___187_4324 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___187_4324.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___187_4324.FStar_Syntax_Syntax.sigmeta)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4331 -> ()));
      (let curmod =
         let uu____4333 = current_module env in uu____4333.FStar_Ident.str in
       (let uu____4335 =
          let uu____4346 = get_exported_id_set env curmod in
          let uu____4351 = get_trans_exported_id_set env curmod in
          (uu____4346, uu____4351) in
        match uu____4335 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4391 = cur_ex eikind in FStar_ST.read uu____4391 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4399 =
                let uu____4400 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4400 in
              FStar_ST.write cur_trans_ex_set_ref uu____4399 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4406 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___188_4418 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___188_4418.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___188_4418.exported_ids);
                    trans_exported_ids = (uu___188_4418.trans_exported_ids);
                    includes = (uu___188_4418.includes);
                    sigaccum = [];
                    sigmap = (uu___188_4418.sigmap);
                    iface = (uu___188_4418.iface);
                    admitted_iface = (uu___188_4418.admitted_iface);
                    expect_typ = (uu___188_4418.expect_typ);
                    docs = (uu___188_4418.docs);
                    remaining_iface_decls =
                      (uu___188_4418.remaining_iface_decls);
                    syntax_only = (uu___188_4418.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4431 =
       let uu____4433 = FStar_ST.read stack in env :: uu____4433 in
     FStar_ST.write stack uu____4431);
    (let uu___189_4441 = env in
     let uu____4442 = FStar_Util.smap_copy (sigmap env) in
     let uu____4448 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___189_4441.curmodule);
       curmonad = (uu___189_4441.curmonad);
       modules = (uu___189_4441.modules);
       scope_mods = (uu___189_4441.scope_mods);
       exported_ids = (uu___189_4441.exported_ids);
       trans_exported_ids = (uu___189_4441.trans_exported_ids);
       includes = (uu___189_4441.includes);
       sigaccum = (uu___189_4441.sigaccum);
       sigmap = uu____4442;
       iface = (uu___189_4441.iface);
       admitted_iface = (uu___189_4441.admitted_iface);
       expect_typ = (uu___189_4441.expect_typ);
       docs = uu____4448;
       remaining_iface_decls = (uu___189_4441.remaining_iface_decls);
       syntax_only = (uu___189_4441.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____4452  ->
    let uu____4453 = FStar_ST.read stack in
    match uu____4453 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4466 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4472 = FStar_ST.read stack in
     match uu____4472 with
     | uu____4477::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4484 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4491  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4503 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4505 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4523 = FStar_Util.smap_try_find sm' k in
              match uu____4523 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___190_4539 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___190_4539.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___190_4539.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___190_4539.FStar_Syntax_Syntax.sigmeta)
                          }
                      | uu____4540 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4543 -> ()));
      env1
let finish_module_or_interface: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
      then check_admits env
      else ();
      finish env modul
let prepare_module_or_interface:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> (env* Prims.bool)
  =
  fun intf  ->
    fun admitted  ->
      fun env  ->
        fun mname  ->
          let prep env1 =
            let open_ns =
              if FStar_Ident.lid_equals mname FStar_Parser_Const.prims_lid
              then []
              else
                if
                  FStar_Util.starts_with "FStar."
                    (FStar_Ident.text_of_lid mname)
                then
                  [FStar_Parser_Const.prims_lid;
                  FStar_Parser_Const.pervasives_lid;
                  FStar_Parser_Const.fstar_ns_lid]
                else
                  [FStar_Parser_Const.prims_lid;
                  FStar_Parser_Const.pervasives_lid;
                  FStar_Parser_Const.st_lid;
                  FStar_Parser_Const.all_lid;
                  FStar_Parser_Const.fstar_ns_lid] in
            let open_ns1 =
              if
                (FStar_List.length mname.FStar_Ident.ns) <>
                  (Prims.parse_int "0")
              then
                let ns = FStar_Ident.lid_of_ids mname.FStar_Ident.ns in ns ::
                  open_ns
              else open_ns in
            (let uu____4587 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4587);
            (match () with
             | () ->
                 ((let uu____4592 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4592);
                  (match () with
                   | () ->
                       ((let uu____4597 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4597);
                        (match () with
                         | () ->
                             let uu___191_4606 = env1 in
                             let uu____4607 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___191_4606.curmonad);
                               modules = (uu___191_4606.modules);
                               scope_mods = uu____4607;
                               exported_ids = (uu___191_4606.exported_ids);
                               trans_exported_ids =
                                 (uu___191_4606.trans_exported_ids);
                               includes = (uu___191_4606.includes);
                               sigaccum = (uu___191_4606.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___191_4606.expect_typ);
                               docs = (uu___191_4606.docs);
                               remaining_iface_decls =
                                 (uu___191_4606.remaining_iface_decls);
                               syntax_only = (uu___191_4606.syntax_only)
                             }))))) in
          let uu____4610 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4622  ->
                    match uu____4622 with
                    | (l,uu____4626) -> FStar_Ident.lid_equals l mname)) in
          match uu____4610 with
          | None  -> let uu____4631 = prep env in (uu____4631, false)
          | Some (uu____4632,m) ->
              ((let uu____4637 =
                  (let uu____4638 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4638) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4637
                then
                  let uu____4639 =
                    let uu____4640 =
                      let uu____4643 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4643, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4640 in
                  raise uu____4639
                else ());
               (let uu____4645 = let uu____4646 = push env in prep uu____4646 in
                (uu____4645, true)))
let enter_monad_scope: env -> FStar_Ident.ident -> env =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | Some mname' ->
          raise
            (FStar_Errors.Error
               ((Prims.strcat "Trying to define monad "
                   (Prims.strcat mname.FStar_Ident.idText
                      (Prims.strcat ", but already in monad scope "
                         mname'.FStar_Ident.idText))),
                 (mname.FStar_Ident.idRange)))
      | None  ->
          let uu___192_4654 = env in
          {
            curmodule = (uu___192_4654.curmodule);
            curmonad = (Some mname);
            modules = (uu___192_4654.modules);
            scope_mods = (uu___192_4654.scope_mods);
            exported_ids = (uu___192_4654.exported_ids);
            trans_exported_ids = (uu___192_4654.trans_exported_ids);
            includes = (uu___192_4654.includes);
            sigaccum = (uu___192_4654.sigaccum);
            sigmap = (uu___192_4654.sigmap);
            iface = (uu___192_4654.iface);
            admitted_iface = (uu___192_4654.admitted_iface);
            expect_typ = (uu___192_4654.expect_typ);
            docs = (uu___192_4654.docs);
            remaining_iface_decls = (uu___192_4654.remaining_iface_decls);
            syntax_only = (uu___192_4654.syntax_only)
          }
let fail_or env lookup lid =
  let uu____4679 = lookup lid in
  match uu____4679 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4685  ->
             match uu____4685 with
             | (lid1,uu____4689) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4696 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4696
               (FStar_Ident.range_of_lid lid) in
           let uu____4697 = resolve_module_name env modul true in
           match uu____4697 with
           | None  ->
               let opened_modules1 = FStar_String.concat ", " opened_modules in
               FStar_Util.format3
                 "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str opened_modules1
           | Some modul' when
               Prims.op_Negation
                 (FStar_List.existsb (fun m  -> m = modul'.FStar_Ident.str)
                    opened_modules)
               ->
               let opened_modules1 = FStar_String.concat ", " opened_modules in
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 opened_modules1
           | Some modul' ->
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, definition %s not found"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 (lid.FStar_Ident.ident).FStar_Ident.idText) in
      raise (FStar_Errors.Error (msg1, (FStar_Ident.range_of_lid lid)))
  | Some r -> r
let fail_or2 lookup id =
  let uu____4724 = lookup id in
  match uu____4724 with
  | None  ->
      raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r