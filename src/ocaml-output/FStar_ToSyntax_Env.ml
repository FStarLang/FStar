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
      let uu___173_421 = env in
      {
        curmodule = (uu___173_421.curmodule);
        curmonad = (uu___173_421.curmonad);
        modules = (uu___173_421.modules);
        scope_mods = (uu___173_421.scope_mods);
        exported_ids = (uu___173_421.exported_ids);
        trans_exported_ids = (uu___173_421.trans_exported_ids);
        includes = (uu___173_421.includes);
        sigaccum = (uu___173_421.sigaccum);
        sigmap = (uu___173_421.sigmap);
        iface = b;
        admitted_iface = (uu___173_421.admitted_iface);
        expect_typ = (uu___173_421.expect_typ);
        docs = (uu___173_421.docs);
        remaining_iface_decls = (uu___173_421.remaining_iface_decls);
        syntax_only = (uu___173_421.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___174_431 = e in
      {
        curmodule = (uu___174_431.curmodule);
        curmonad = (uu___174_431.curmonad);
        modules = (uu___174_431.modules);
        scope_mods = (uu___174_431.scope_mods);
        exported_ids = (uu___174_431.exported_ids);
        trans_exported_ids = (uu___174_431.trans_exported_ids);
        includes = (uu___174_431.includes);
        sigaccum = (uu___174_431.sigaccum);
        sigmap = (uu___174_431.sigmap);
        iface = (uu___174_431.iface);
        admitted_iface = b;
        expect_typ = (uu___174_431.expect_typ);
        docs = (uu___174_431.docs);
        remaining_iface_decls = (uu___174_431.remaining_iface_decls);
        syntax_only = (uu___174_431.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___175_441 = e in
      {
        curmodule = (uu___175_441.curmodule);
        curmonad = (uu___175_441.curmonad);
        modules = (uu___175_441.modules);
        scope_mods = (uu___175_441.scope_mods);
        exported_ids = (uu___175_441.exported_ids);
        trans_exported_ids = (uu___175_441.trans_exported_ids);
        includes = (uu___175_441.includes);
        sigaccum = (uu___175_441.sigaccum);
        sigmap = (uu___175_441.sigmap);
        iface = (uu___175_441.iface);
        admitted_iface = (uu___175_441.admitted_iface);
        expect_typ = b;
        docs = (uu___175_441.docs);
        remaining_iface_decls = (uu___175_441.remaining_iface_decls);
        syntax_only = (uu___175_441.syntax_only)
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
      let uu___176_477 = e in
      {
        curmodule = (Some l);
        curmonad = (uu___176_477.curmonad);
        modules = (uu___176_477.modules);
        scope_mods = (uu___176_477.scope_mods);
        exported_ids = (uu___176_477.exported_ids);
        trans_exported_ids = (uu___176_477.trans_exported_ids);
        includes = (uu___176_477.includes);
        sigaccum = (uu___176_477.sigaccum);
        sigmap = (uu___176_477.sigmap);
        iface = (uu___176_477.iface);
        admitted_iface = (uu___176_477.admitted_iface);
        expect_typ = (uu___176_477.expect_typ);
        docs = (uu___176_477.docs);
        remaining_iface_decls = (uu___176_477.remaining_iface_decls);
        syntax_only = (uu___176_477.syntax_only)
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
            let uu___177_579 = env in
            {
              curmodule = (uu___177_579.curmodule);
              curmonad = (uu___177_579.curmonad);
              modules = (uu___177_579.modules);
              scope_mods = (uu___177_579.scope_mods);
              exported_ids = (uu___177_579.exported_ids);
              trans_exported_ids = (uu___177_579.trans_exported_ids);
              includes = (uu___177_579.includes);
              sigaccum = (uu___177_579.sigaccum);
              sigmap = (uu___177_579.sigmap);
              iface = (uu___177_579.iface);
              admitted_iface = (uu___177_579.admitted_iface);
              expect_typ = (uu___177_579.expect_typ);
              docs = (uu___177_579.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___177_579.syntax_only)
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
      let uu___178_607 = env in
      {
        curmodule = (uu___178_607.curmodule);
        curmonad = (uu___178_607.curmonad);
        modules = (uu___178_607.modules);
        scope_mods = (uu___178_607.scope_mods);
        exported_ids = (uu___178_607.exported_ids);
        trans_exported_ids = (uu___178_607.trans_exported_ids);
        includes = (uu___178_607.includes);
        sigaccum = (uu___178_607.sigaccum);
        sigmap = (uu___178_607.sigmap);
        iface = (uu___178_607.iface);
        admitted_iface = (uu___178_607.admitted_iface);
        expect_typ = (uu___178_607.expect_typ);
        docs = (uu___178_607.docs);
        remaining_iface_decls = (uu___178_607.remaining_iface_decls);
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
        let uu___179_665 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___179_665.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___180_666 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___180_666.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___180_666.FStar_Syntax_Syntax.sort)
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
let option_of_cont k_ignore uu___146_812 =
  match uu___146_812 with
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
  fun uu___147_898  ->
    match uu___147_898 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___148_947 =
    match uu___148_947 with
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
  fun uu___149_1005  ->
    match uu___149_1005 with
    | Exported_id_field  -> true
    | uu____1006 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___150_1095 =
    match uu___150_1095 with
    | (id',uu____1097,uu____1098) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___151_1102 =
    match uu___151_1102 with
    | (id',uu____1104,uu____1105) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1108 = current_module env in FStar_Ident.ids_of_lid uu____1108 in
  let proc uu___152_1113 =
    match uu___152_1113 with
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
  let rec aux uu___153_1130 =
    match uu___153_1130 with
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
        let rec aux uu___154_1385 =
          match uu___154_1385 with
          | [] ->
              let uu____1388 = module_is_defined env lid in
              if uu____1388 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1395 =
                  let uu____1397 = FStar_Ident.path_of_lid ns in
                  let uu____1399 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1397 uu____1399 in
                FStar_Ident.lid_of_path uu____1395
                  (FStar_Ident.range_of_lid lid) in
              let uu____1401 = module_is_defined env new_lid in
              if uu____1401 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1406 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1412::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____1424 =
          let uu____1425 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____1425 in
        if uu____1424
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Syntax_Const.prims_lid
           then ()
           else
             (let uu____1427 =
                let uu____1428 =
                  let uu____1431 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____1431, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____1428 in
              raise uu____1427))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____1439 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____1442 = resolve_module_name env modul_orig true in
          (match uu____1442 with
           | Some modul_res -> fail_if_curmodule env modul_orig modul_res
           | uu____1445 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___155_1453  ->
           match uu___155_1453 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1455 -> false) env.scope_mods
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
                 let uu____1510 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____1510
                   (FStar_Util.map_option
                      (fun uu____1534  ->
                         match uu____1534 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____1551 =
          is_full_path &&
            (let uu____1552 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____1552) in
        if uu____1551
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1569 = aux ns_rev_prefix ns_last_id in
               (match uu____1569 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____1603 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____1603 with
      | (uu____1608,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1699::uu____1700 ->
      let uu____1702 =
        let uu____1704 =
          let uu____1705 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____1705 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____1704 true in
      (match uu____1702 with
       | None  -> None
       | Some modul ->
           let uu____1708 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____1710  -> None) uu____1708)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___156_1725 =
  match uu___156_1725 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1804 = k_global_def lid1 def in cont_of_option k uu____1804 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1825 = k_local_binding l in
       cont_of_option Cont_fail uu____1825)
    (fun r  ->
       let uu____1828 = k_rec_binding r in
       cont_of_option Cont_fail uu____1828) (fun uu____1830  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1836,uu____1837,uu____1838,l,uu____1840,uu____1841) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___157_1846  ->
               match uu___157_1846 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1848,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1855 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____1859,uu____1860,uu____1861)
        -> None
    | uu____1862 -> None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1871 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____1875 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____1875 then Some fv else None) in
      FStar_All.pipe_right uu____1871 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1893 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____1893 ns)
let try_lookup_name:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> foundname option =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___161_1918 =
            match uu___161_1918 with
            | (uu____1922,true ) when exclude_interf -> None
            | (se,uu____1924) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1926 ->
                     let uu____1935 =
                       let uu____1936 =
                         let uu____1939 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____1939, false) in
                       Term_name uu____1936 in
                     Some uu____1935
                 | FStar_Syntax_Syntax.Sig_datacon uu____1940 ->
                     let uu____1948 =
                       let uu____1949 =
                         let uu____1952 =
                           let uu____1953 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1953 in
                         (uu____1952, false) in
                       Term_name uu____1949 in
                     Some uu____1948
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1955,lbs),uu____1957,uu____1958) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____1969 =
                       let uu____1970 =
                         let uu____1973 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____1973, false) in
                       Term_name uu____1970 in
                     Some uu____1969
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1975,uu____1976) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____1979 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___158_1981  ->
                                  match uu___158_1981 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1982 -> false))) in
                     if uu____1979
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____1986 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___159_1988  ->
                                      match uu___159_1988 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____1989 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____1992 -> true
                                      | uu____1993 -> false))) in
                         if uu____1986
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____1995 =
                         FStar_Util.find_map quals
                           (fun uu___160_1997  ->
                              match uu___160_1997 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____2000 -> None) in
                       (match uu____1995 with
                        | Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
                        | uu____2012 ->
                            let uu____2014 =
                              let uu____2015 =
                                let uu____2018 =
                                  let uu____2019 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____2019 in
                                (uu____2018, false) in
                              Term_name uu____2015 in
                            Some uu____2014)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2024 ->
                     Some (Eff_name (se, source_lid))
                 | uu____2031 -> None) in
          let k_local_binding r =
            let uu____2043 =
              let uu____2044 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____2044 in
            Some uu____2043 in
          let k_rec_binding uu____2054 =
            match uu____2054 with
            | (id,l,dd) ->
                let uu____2062 =
                  let uu____2063 =
                    let uu____2066 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____2066, false) in
                  Term_name uu____2063 in
                Some uu____2062 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2070 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2070 with
                 | Some f -> Some (Term_name f)
                 | uu____2080 -> None)
            | uu____2084 -> None in
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
        let uu____2104 = try_lookup_name true exclude_interf env lid in
        match uu____2104 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____2113 -> None
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2124 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2124 with | Some (o,l1) -> Some l1 | uu____2133 -> None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list) option
  =
  fun env  ->
    fun l  ->
      let uu____2147 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2147 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2156;
             FStar_Syntax_Syntax.sigquals = uu____2157;
             FStar_Syntax_Syntax.sigmeta = uu____2158;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2168;
             FStar_Syntax_Syntax.sigquals = uu____2169;
             FStar_Syntax_Syntax.sigmeta = uu____2170;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____2179,uu____2180,uu____2181,uu____2182,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2184;
             FStar_Syntax_Syntax.sigquals = uu____2185;
             FStar_Syntax_Syntax.sigmeta = uu____2186;_},l1)
          -> Some (l1, cattributes)
      | uu____2197 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl option =
  fun env  ->
    fun l  ->
      let uu____2211 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2211 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2217;
             FStar_Syntax_Syntax.sigquals = uu____2218;
             FStar_Syntax_Syntax.sigmeta = uu____2219;_},uu____2220)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2225;
             FStar_Syntax_Syntax.sigquals = uu____2226;
             FStar_Syntax_Syntax.sigmeta = uu____2227;_},uu____2228)
          -> Some ne
      | uu____2232 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2242 = try_lookup_effect_name env lid in
      match uu____2242 with | None  -> false | Some uu____2244 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2252 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2252 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____2258,uu____2259,uu____2260,uu____2261);
             FStar_Syntax_Syntax.sigrng = uu____2262;
             FStar_Syntax_Syntax.sigquals = uu____2263;
             FStar_Syntax_Syntax.sigmeta = uu____2264;_},uu____2265)
          ->
          let rec aux new_name =
            let uu____2276 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2276 with
            | None  -> None
            | Some (s,uu____2286) ->
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
                     (uu____2292,uu____2293,uu____2294,cmp,uu____2296) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2300 -> None) in
          aux l'
      | Some (uu____2301,l') -> Some l'
      | uu____2305 -> None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___162_2326 =
        match uu___162_2326 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2331,uu____2332,uu____2333);
             FStar_Syntax_Syntax.sigrng = uu____2334;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2336;_},uu____2337)
            -> Some quals
        | uu____2340 -> None in
      let uu____2344 =
        resolve_in_open_namespaces' env lid (fun uu____2348  -> None)
          (fun uu____2350  -> None) k_global_def in
      match uu____2344 with | Some quals -> quals | uu____2356 -> []
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul option =
  fun env  ->
    fun path  ->
      let uu____2368 =
        FStar_List.tryFind
          (fun uu____2374  ->
             match uu____2374 with
             | (mlid,modul) ->
                 let uu____2379 = FStar_Ident.path_of_lid mlid in
                 uu____2379 = path) env.modules in
      match uu____2368 with
      | Some (uu____2383,modul) -> Some modul
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___163_2405 =
        match uu___163_2405 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2409,lbs),uu____2411,uu____2412);
             FStar_Syntax_Syntax.sigrng = uu____2413;
             FStar_Syntax_Syntax.sigquals = uu____2414;
             FStar_Syntax_Syntax.sigmeta = uu____2415;_},uu____2416)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2428 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2428
        | uu____2429 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2432  -> None)
        (fun uu____2433  -> None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___164_2452 =
        match uu___164_2452 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2459,uu____2460);
             FStar_Syntax_Syntax.sigrng = uu____2461;
             FStar_Syntax_Syntax.sigquals = uu____2462;
             FStar_Syntax_Syntax.sigmeta = uu____2463;_},uu____2464)
            ->
            FStar_Util.find_map (snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2480 -> None)
        | uu____2485 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2492  -> None)
        (fun uu____2495  -> None) k_global_def
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
          let uu____2522 = try_lookup_name any_val exclude_interf env lid in
          match uu____2522 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2531 -> None
let try_lookup_lid:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2551 = try_lookup_lid env l in
      match uu____2551 with
      | None  -> None
      | Some (e,uu____2559) ->
          let uu____2562 =
            let uu____2563 = FStar_Syntax_Subst.compress e in
            uu____2563.FStar_Syntax_Syntax.n in
          (match uu____2562 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2572 -> None)
let try_lookup_lid_no_resolve:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___181_2583 = env in
        {
          curmodule = (uu___181_2583.curmodule);
          curmonad = (uu___181_2583.curmonad);
          modules = (uu___181_2583.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___181_2583.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___181_2583.sigaccum);
          sigmap = (uu___181_2583.sigmap);
          iface = (uu___181_2583.iface);
          admitted_iface = (uu___181_2583.admitted_iface);
          expect_typ = (uu___181_2583.expect_typ);
          docs = (uu___181_2583.docs);
          remaining_iface_decls = (uu___181_2583.remaining_iface_decls);
          syntax_only = (uu___181_2583.syntax_only)
        } in
      try_lookup_lid env' l
let try_lookup_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___166_2607 =
        match uu___166_2607 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2611,uu____2612,uu____2613);
             FStar_Syntax_Syntax.sigrng = uu____2614;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2616;_},uu____2617)
            ->
            let uu____2619 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___165_2621  ->
                      match uu___165_2621 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2622 -> false)) in
            if uu____2619
            then
              let uu____2624 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2624
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2626;
             FStar_Syntax_Syntax.sigrng = uu____2627;
             FStar_Syntax_Syntax.sigquals = uu____2628;
             FStar_Syntax_Syntax.sigmeta = uu____2629;_},uu____2630)
            ->
            let uu____2639 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2639
        | uu____2640 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2643  -> None)
        (fun uu____2644  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___167_2663 =
        match uu___167_2663 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2668,uu____2669,uu____2670,uu____2671,datas,uu____2673);
             FStar_Syntax_Syntax.sigrng = uu____2674;
             FStar_Syntax_Syntax.sigquals = uu____2675;
             FStar_Syntax_Syntax.sigmeta = uu____2676;_},uu____2677)
            -> Some datas
        | uu____2684 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2689  -> None)
        (fun uu____2691  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____2725 =
    let uu____2726 =
      let uu____2729 =
        let uu____2731 = FStar_ST.read record_cache in
        FStar_List.hd uu____2731 in
      let uu____2739 = FStar_ST.read record_cache in uu____2729 :: uu____2739 in
    FStar_ST.write record_cache uu____2726 in
  let pop1 uu____2754 =
    let uu____2755 =
      let uu____2758 = FStar_ST.read record_cache in FStar_List.tl uu____2758 in
    FStar_ST.write record_cache uu____2755 in
  let peek uu____2774 =
    let uu____2775 = FStar_ST.read record_cache in FStar_List.hd uu____2775 in
  let insert r =
    let uu____2787 =
      let uu____2790 = let uu____2792 = peek () in r :: uu____2792 in
      let uu____2794 =
        let uu____2797 = FStar_ST.read record_cache in
        FStar_List.tl uu____2797 in
      uu____2790 :: uu____2794 in
    FStar_ST.write record_cache uu____2787 in
  let commit1 uu____2813 =
    let uu____2814 = FStar_ST.read record_cache in
    match uu____2814 with
    | hd1::uu____2822::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2835 -> failwith "Impossible" in
  let filter1 uu____2841 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____2848 =
           let uu____2851 = FStar_ST.read record_cache in filtered ::
             uu____2851 in
         FStar_ST.write record_cache uu____2848) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____2925 = record_cache_aux_with_filter in
  match uu____2925 with | (aux,uu____2963) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____3002 = record_cache_aux_with_filter in
  match uu____3002 with | (uu____3025,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____3065 = record_cache_aux in
  match uu____3065 with
  | (push1,uu____3085,uu____3086,uu____3087,uu____3088) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3113 = record_cache_aux in
  match uu____3113 with
  | (uu____3132,pop1,uu____3134,uu____3135,uu____3136) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____3162 = record_cache_aux in
  match uu____3162 with
  | (uu____3182,uu____3183,peek,uu____3185,uu____3186) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____3211 = record_cache_aux in
  match uu____3211 with
  | (uu____3230,uu____3231,uu____3232,insert,uu____3234) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____3259 = record_cache_aux in
  match uu____3259 with
  | (uu____3278,uu____3279,uu____3280,uu____3281,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3321) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___168_3330  ->
                   match uu___168_3330 with
                   | FStar_Syntax_Syntax.RecordType uu____3331 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____3336 -> true
                   | uu____3341 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___169_3349  ->
                      match uu___169_3349 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3351,uu____3352,uu____3353,uu____3354,uu____3355);
                          FStar_Syntax_Syntax.sigrng = uu____3356;
                          FStar_Syntax_Syntax.sigquals = uu____3357;
                          FStar_Syntax_Syntax.sigmeta = uu____3358;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3362 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___170_3364  ->
                    match uu___170_3364 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____3368,uu____3369,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____3371;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____3373;_} ->
                        let uu____3378 =
                          let uu____3379 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3379 in
                        (match uu____3378 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3383,t,uu____3385,uu____3386,uu____3387);
                             FStar_Syntax_Syntax.sigrng = uu____3388;
                             FStar_Syntax_Syntax.sigquals = uu____3389;
                             FStar_Syntax_Syntax.sigmeta = uu____3390;_} ->
                             let uu____3394 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3394 with
                              | (formals,uu____3403) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3429  ->
                                            match uu____3429 with
                                            | (x,q) ->
                                                let uu____3437 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3437
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3468  ->
                                            match uu____3468 with
                                            | (x,q) ->
                                                let uu____3477 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____3477,
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
                                  ((let uu____3489 =
                                      let uu____3491 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3491 in
                                    FStar_ST.write new_globs uu____3489);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3507 =
                                            match uu____3507 with
                                            | (id,uu____3513) ->
                                                let modul =
                                                  let uu____3519 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3519.FStar_Ident.str in
                                                let uu____3520 =
                                                  get_exported_id_set e modul in
                                                (match uu____3520 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____3536 =
                                                         let uu____3537 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3537 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3536);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3544 =
                                                               let uu____3545
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____3545.FStar_Ident.ident in
                                                             uu____3544.FStar_Ident.idText in
                                                           let uu____3547 =
                                                             let uu____3548 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3548 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3547))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3561 -> ())
                    | uu____3562 -> ()))
        | uu____3563 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3576 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3576 with
        | (ns,id) ->
            let uu____3586 = peek_record_cache () in
            FStar_Util.find_map uu____3586
              (fun record  ->
                 let uu____3589 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3592  -> None) uu____3589) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3593  -> Cont_ignore) (fun uu____3594  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3597 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3597)
        (fun k  -> fun uu____3600  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let uu____3609 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3609 with
      | Some r when r.is_record -> Some r
      | uu____3613 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3624 = try_lookup_record_by_field_name env lid in
        match uu____3624 with
        | Some record' when
            let uu____3627 =
              let uu____3628 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3628 in
            let uu____3630 =
              let uu____3631 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3631 in
            uu____3627 = uu____3630 ->
            let uu____3633 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3635  -> Cont_ok ()) in
            (match uu____3633 with
             | Cont_ok uu____3636 -> true
             | uu____3637 -> false)
        | uu____3639 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) option =
  fun env  ->
    fun fieldname  ->
      let uu____3650 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3650 with
      | Some r ->
          let uu____3656 =
            let uu____3659 =
              let uu____3660 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3660
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3659, (r.is_record)) in
          Some uu____3656
      | uu____3663 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3672  ->
    let uu____3673 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3673
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3684  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___171_3693  ->
      match uu___171_3693 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___172_3713 =
            match uu___172_3713 with
            | Rec_binding uu____3714 -> true
            | uu____3715 -> false in
          let this_env =
            let uu___182_3717 = env in
            let uu____3718 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___182_3717.curmodule);
              curmonad = (uu___182_3717.curmonad);
              modules = (uu___182_3717.modules);
              scope_mods = uu____3718;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___182_3717.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___182_3717.sigaccum);
              sigmap = (uu___182_3717.sigmap);
              iface = (uu___182_3717.iface);
              admitted_iface = (uu___182_3717.admitted_iface);
              expect_typ = (uu___182_3717.expect_typ);
              docs = (uu___182_3717.docs);
              remaining_iface_decls = (uu___182_3717.remaining_iface_decls);
              syntax_only = (uu___182_3717.syntax_only)
            } in
          let uu____3720 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3720 with | None  -> true | Some uu____3726 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___183_3737 = env in
      {
        curmodule = (uu___183_3737.curmodule);
        curmonad = (uu___183_3737.curmonad);
        modules = (uu___183_3737.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___183_3737.exported_ids);
        trans_exported_ids = (uu___183_3737.trans_exported_ids);
        includes = (uu___183_3737.includes);
        sigaccum = (uu___183_3737.sigaccum);
        sigmap = (uu___183_3737.sigmap);
        iface = (uu___183_3737.iface);
        admitted_iface = (uu___183_3737.admitted_iface);
        expect_typ = (uu___183_3737.expect_typ);
        docs = (uu___183_3737.docs);
        remaining_iface_decls = (uu___183_3737.remaining_iface_decls);
        syntax_only = (uu___183_3737.syntax_only)
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
        let uu____3776 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____3776
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
          | Some (se,uu____3796) ->
              let uu____3799 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____3799 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____3804 =
          let uu____3805 =
            let uu____3808 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____3808, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____3805 in
        raise uu____3804 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____3815 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3820 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3826 -> (true, true)
          | uu____3831 -> (false, false) in
        match uu____3815 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____3836 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3839 =
                     let uu____3840 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____3840 in
                   if uu____3839 then Some l else None) in
            (match uu____3836 with
             | Some l when
                 let uu____3844 = FStar_Options.interactive () in
                 Prims.op_Negation uu____3844 -> err1 l
             | uu____3845 ->
                 (extract_record env globals s;
                  (let uu___184_3850 = env in
                   {
                     curmodule = (uu___184_3850.curmodule);
                     curmonad = (uu___184_3850.curmonad);
                     modules = (uu___184_3850.modules);
                     scope_mods = (uu___184_3850.scope_mods);
                     exported_ids = (uu___184_3850.exported_ids);
                     trans_exported_ids = (uu___184_3850.trans_exported_ids);
                     includes = (uu___184_3850.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___184_3850.sigmap);
                     iface = (uu___184_3850.iface);
                     admitted_iface = (uu___184_3850.admitted_iface);
                     expect_typ = (uu___184_3850.expect_typ);
                     docs = (uu___184_3850.docs);
                     remaining_iface_decls =
                       (uu___184_3850.remaining_iface_decls);
                     syntax_only = (uu___184_3850.syntax_only)
                   }))) in
      let env2 =
        let uu___185_3852 = env1 in
        let uu____3853 = FStar_ST.read globals in
        {
          curmodule = (uu___185_3852.curmodule);
          curmonad = (uu___185_3852.curmonad);
          modules = (uu___185_3852.modules);
          scope_mods = uu____3853;
          exported_ids = (uu___185_3852.exported_ids);
          trans_exported_ids = (uu___185_3852.trans_exported_ids);
          includes = (uu___185_3852.includes);
          sigaccum = (uu___185_3852.sigaccum);
          sigmap = (uu___185_3852.sigmap);
          iface = (uu___185_3852.iface);
          admitted_iface = (uu___185_3852.admitted_iface);
          expect_typ = (uu___185_3852.expect_typ);
          docs = (uu___185_3852.docs);
          remaining_iface_decls = (uu___185_3852.remaining_iface_decls);
          syntax_only = (uu___185_3852.syntax_only)
        } in
      let uu____3858 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3872) ->
            let uu____3877 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____3877)
        | uu____3891 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____3858 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3921  ->
                   match uu____3921 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3932 =
                                  let uu____3934 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3934 in
                                FStar_ST.write globals uu____3932);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3943 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____3943.FStar_Ident.str in
                                    ((let uu____3945 =
                                        get_exported_id_set env3 modul in
                                      match uu____3945 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____3960 =
                                            let uu____3961 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3961 in
                                          FStar_ST.write my_exported_ids
                                            uu____3960
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
              let uu___186_3973 = env3 in
              let uu____3974 = FStar_ST.read globals in
              {
                curmodule = (uu___186_3973.curmodule);
                curmonad = (uu___186_3973.curmonad);
                modules = (uu___186_3973.modules);
                scope_mods = uu____3974;
                exported_ids = (uu___186_3973.exported_ids);
                trans_exported_ids = (uu___186_3973.trans_exported_ids);
                includes = (uu___186_3973.includes);
                sigaccum = (uu___186_3973.sigaccum);
                sigmap = (uu___186_3973.sigmap);
                iface = (uu___186_3973.iface);
                admitted_iface = (uu___186_3973.admitted_iface);
                expect_typ = (uu___186_3973.expect_typ);
                docs = (uu___186_3973.docs);
                remaining_iface_decls = (uu___186_3973.remaining_iface_decls);
                syntax_only = (uu___186_3973.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3985 =
        let uu____3988 = resolve_module_name env ns false in
        match uu____3988 with
        | None  ->
            let modules = env.modules in
            let uu____3996 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____4002  ->
                      match uu____4002 with
                      | (m,uu____4006) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____3996
            then (ns, Open_namespace)
            else
              (let uu____4010 =
                 let uu____4011 =
                   let uu____4014 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____4014, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____4011 in
               raise uu____4010)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____3985 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____4028 = resolve_module_name env ns false in
      match uu____4028 with
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____4034 = current_module env1 in
              uu____4034.FStar_Ident.str in
            (let uu____4036 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____4036 with
             | None  -> ()
             | Some incl ->
                 let uu____4049 =
                   let uu____4051 = FStar_ST.read incl in ns1 :: uu____4051 in
                 FStar_ST.write incl uu____4049);
            (match () with
             | () ->
                 let uu____4059 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____4059 with
                  | Some ns_trans_exports ->
                      ((let uu____4072 =
                          let uu____4083 = get_exported_id_set env1 curmod in
                          let uu____4088 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____4083, uu____4088) in
                        match uu____4072 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____4128 = ns_trans_exports k in
                                FStar_ST.read uu____4128 in
                              let ex = cur_exports k in
                              (let uu____4137 =
                                 let uu____4138 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____4138 ns_ex in
                               FStar_ST.write ex uu____4137);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____4148 =
                                     let uu____4149 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____4149 ns_ex in
                                   FStar_ST.write trans_ex uu____4148) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____4155 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____4169 =
                        let uu____4170 =
                          let uu____4173 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____4173, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____4170 in
                      raise uu____4169))))
      | uu____4174 ->
          let uu____4176 =
            let uu____4177 =
              let uu____4180 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____4180, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____4177 in
          raise uu____4176
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____4190 = module_is_defined env l in
        if uu____4190
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____4193 =
             let uu____4194 =
               let uu____4197 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____4197, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____4194 in
           raise uu____4193)
let push_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____4211 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____4211 with
              | None  -> ()
              | Some old_doc ->
                  let uu____4214 =
                    let uu____4215 = FStar_Ident.string_of_lid l in
                    let uu____4216 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____4217 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____4215 uu____4216 uu____4217 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____4214);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____4226 = try_lookup_lid env l in
                (match uu____4226 with
                 | None  ->
                     ((let uu____4233 =
                         let uu____4234 = FStar_Options.interactive () in
                         Prims.op_Negation uu____4234 in
                       if uu____4233
                       then
                         let uu____4235 =
                           let uu____4236 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____4237 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____4236 uu____4237 in
                         FStar_Util.print_string uu____4235
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___187_4243 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___187_4243.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___187_4243.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___187_4243.FStar_Syntax_Syntax.sigmeta)
                           }), false)))
                 | Some uu____4244 -> ())
            | uu____4249 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4261) ->
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
                                (lid,uu____4269,uu____4270,uu____4271,uu____4272,uu____4273)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4278 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4281,uu____4282) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4286,lbs),uu____4288,uu____4289) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4302 =
                               let uu____4303 =
                                 let uu____4304 =
                                   let uu____4309 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4309.FStar_Syntax_Syntax.fv_name in
                                 uu____4304.FStar_Syntax_Syntax.v in
                               uu____4303.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4302))
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
                               let uu____4319 =
                                 let uu____4324 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4324.FStar_Syntax_Syntax.fv_name in
                               uu____4319.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___188_4331 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___188_4331.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___188_4331.FStar_Syntax_Syntax.sigmeta)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4338 -> ()));
      (let curmod =
         let uu____4340 = current_module env in uu____4340.FStar_Ident.str in
       (let uu____4342 =
          let uu____4353 = get_exported_id_set env curmod in
          let uu____4358 = get_trans_exported_id_set env curmod in
          (uu____4353, uu____4358) in
        match uu____4342 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4398 = cur_ex eikind in FStar_ST.read uu____4398 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4406 =
                let uu____4407 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4407 in
              FStar_ST.write cur_trans_ex_set_ref uu____4406 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4413 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___189_4425 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___189_4425.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___189_4425.exported_ids);
                    trans_exported_ids = (uu___189_4425.trans_exported_ids);
                    includes = (uu___189_4425.includes);
                    sigaccum = [];
                    sigmap = (uu___189_4425.sigmap);
                    iface = (uu___189_4425.iface);
                    admitted_iface = (uu___189_4425.admitted_iface);
                    expect_typ = (uu___189_4425.expect_typ);
                    docs = (uu___189_4425.docs);
                    remaining_iface_decls =
                      (uu___189_4425.remaining_iface_decls);
                    syntax_only = (uu___189_4425.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4438 =
       let uu____4440 = FStar_ST.read stack in env :: uu____4440 in
     FStar_ST.write stack uu____4438);
    (let uu___190_4448 = env in
     let uu____4449 = FStar_Util.smap_copy (sigmap env) in
     let uu____4455 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___190_4448.curmodule);
       curmonad = (uu___190_4448.curmonad);
       modules = (uu___190_4448.modules);
       scope_mods = (uu___190_4448.scope_mods);
       exported_ids = (uu___190_4448.exported_ids);
       trans_exported_ids = (uu___190_4448.trans_exported_ids);
       includes = (uu___190_4448.includes);
       sigaccum = (uu___190_4448.sigaccum);
       sigmap = uu____4449;
       iface = (uu___190_4448.iface);
       admitted_iface = (uu___190_4448.admitted_iface);
       expect_typ = (uu___190_4448.expect_typ);
       docs = uu____4455;
       remaining_iface_decls = (uu___190_4448.remaining_iface_decls);
       syntax_only = (uu___190_4448.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____4459  ->
    let uu____4460 = FStar_ST.read stack in
    match uu____4460 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4473 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4479 = FStar_ST.read stack in
     match uu____4479 with
     | uu____4484::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4491 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4498  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4510 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4512 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4530 = FStar_Util.smap_try_find sm' k in
              match uu____4530 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___191_4546 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___191_4546.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___191_4546.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___191_4546.FStar_Syntax_Syntax.sigmeta)
                          }
                      | uu____4547 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4550 -> ()));
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
            (let uu____4596 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4596);
            (match () with
             | () ->
                 ((let uu____4601 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4601);
                  (match () with
                   | () ->
                       ((let uu____4606 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4606);
                        (match () with
                         | () ->
                             let uu___192_4615 = env1 in
                             let uu____4616 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___192_4615.curmonad);
                               modules = (uu___192_4615.modules);
                               scope_mods = uu____4616;
                               exported_ids = (uu___192_4615.exported_ids);
                               trans_exported_ids =
                                 (uu___192_4615.trans_exported_ids);
                               includes = (uu___192_4615.includes);
                               sigaccum = (uu___192_4615.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___192_4615.expect_typ);
                               docs = (uu___192_4615.docs);
                               remaining_iface_decls =
                                 (uu___192_4615.remaining_iface_decls);
                               syntax_only = (uu___192_4615.syntax_only)
                             }))))) in
          let uu____4619 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4631  ->
                    match uu____4631 with
                    | (l,uu____4635) -> FStar_Ident.lid_equals l mname)) in
          match uu____4619 with
          | None  -> let uu____4640 = prep env in (uu____4640, false)
          | Some (uu____4641,m) ->
              ((let uu____4646 =
                  (let uu____4647 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4647) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4646
                then
                  let uu____4648 =
                    let uu____4649 =
                      let uu____4652 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4652, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4649 in
                  raise uu____4648
                else ());
               (let uu____4654 = let uu____4655 = push env in prep uu____4655 in
                (uu____4654, true)))
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
          let uu___193_4663 = env in
          {
            curmodule = (uu___193_4663.curmodule);
            curmonad = (Some mname);
            modules = (uu___193_4663.modules);
            scope_mods = (uu___193_4663.scope_mods);
            exported_ids = (uu___193_4663.exported_ids);
            trans_exported_ids = (uu___193_4663.trans_exported_ids);
            includes = (uu___193_4663.includes);
            sigaccum = (uu___193_4663.sigaccum);
            sigmap = (uu___193_4663.sigmap);
            iface = (uu___193_4663.iface);
            admitted_iface = (uu___193_4663.admitted_iface);
            expect_typ = (uu___193_4663.expect_typ);
            docs = (uu___193_4663.docs);
            remaining_iface_decls = (uu___193_4663.remaining_iface_decls);
            syntax_only = (uu___193_4663.syntax_only)
          }
let fail_or env lookup lid =
  let uu____4688 = lookup lid in
  match uu____4688 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4694  ->
             match uu____4694 with
             | (lid1,uu____4698) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4707 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4707
               (FStar_Ident.range_of_lid lid) in
           let uu____4708 = resolve_module_name env modul true in
           match uu____4708 with
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
  let uu____4735 = lookup id in
  match uu____4735 with
  | None  ->
      raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r