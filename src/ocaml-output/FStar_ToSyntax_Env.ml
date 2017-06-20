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
    match projectee with | Open_module  -> true | uu____13 -> false
let uu___is_Open_namespace: open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____18 -> false
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
    match projectee with | Local_binding _0 -> true | uu____113 -> false
let __proj__Local_binding__item___0: scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0
let uu___is_Rec_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____127 -> false
let __proj__Rec_binding__item___0: scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____141 -> false
let __proj__Module_abbrev__item___0: scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____155 -> false
let __proj__Open_module_or_namespace__item___0:
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_def: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____169 -> false
let __proj__Top_level_def__item___0: scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0
let uu___is_Record_or_dc: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____183 -> false
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
    | uu____197 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____202 -> false
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
    match projectee with | Term_name _0 -> true | uu____419 -> false
let __proj__Term_name__item___0:
  foundname -> (FStar_Syntax_Syntax.typ* Prims.bool) =
  fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____441 -> false
let __proj__Eff_name__item___0:
  foundname -> (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___174_464 = env in
      {
        curmodule = (uu___174_464.curmodule);
        curmonad = (uu___174_464.curmonad);
        modules = (uu___174_464.modules);
        scope_mods = (uu___174_464.scope_mods);
        exported_ids = (uu___174_464.exported_ids);
        trans_exported_ids = (uu___174_464.trans_exported_ids);
        includes = (uu___174_464.includes);
        sigaccum = (uu___174_464.sigaccum);
        sigmap = (uu___174_464.sigmap);
        iface = b;
        admitted_iface = (uu___174_464.admitted_iface);
        expect_typ = (uu___174_464.expect_typ);
        docs = (uu___174_464.docs);
        remaining_iface_decls = (uu___174_464.remaining_iface_decls);
        syntax_only = (uu___174_464.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___175_477 = e in
      {
        curmodule = (uu___175_477.curmodule);
        curmonad = (uu___175_477.curmonad);
        modules = (uu___175_477.modules);
        scope_mods = (uu___175_477.scope_mods);
        exported_ids = (uu___175_477.exported_ids);
        trans_exported_ids = (uu___175_477.trans_exported_ids);
        includes = (uu___175_477.includes);
        sigaccum = (uu___175_477.sigaccum);
        sigmap = (uu___175_477.sigmap);
        iface = (uu___175_477.iface);
        admitted_iface = b;
        expect_typ = (uu___175_477.expect_typ);
        docs = (uu___175_477.docs);
        remaining_iface_decls = (uu___175_477.remaining_iface_decls);
        syntax_only = (uu___175_477.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___176_490 = e in
      {
        curmodule = (uu___176_490.curmodule);
        curmonad = (uu___176_490.curmonad);
        modules = (uu___176_490.modules);
        scope_mods = (uu___176_490.scope_mods);
        exported_ids = (uu___176_490.exported_ids);
        trans_exported_ids = (uu___176_490.trans_exported_ids);
        includes = (uu___176_490.includes);
        sigaccum = (uu___176_490.sigaccum);
        sigmap = (uu___176_490.sigmap);
        iface = (uu___176_490.iface);
        admitted_iface = (uu___176_490.admitted_iface);
        expect_typ = b;
        docs = (uu___176_490.docs);
        remaining_iface_decls = (uu___176_490.remaining_iface_decls);
        syntax_only = (uu___176_490.syntax_only)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____506 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____506 with
      | None  -> []
      | Some exported_id_set ->
          let uu____510 =
            let uu____511 = exported_id_set Exported_id_term_type in
            FStar_ST.read uu____511 in
          FStar_All.pipe_right uu____510 FStar_Util.set_elements
let open_modules:
  env -> (FStar_Ident.lident* FStar_Syntax_Syntax.modul) Prims.list =
  fun e  -> e.modules
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___177_532 = e in
      {
        curmodule = (Some l);
        curmonad = (uu___177_532.curmonad);
        modules = (uu___177_532.modules);
        scope_mods = (uu___177_532.scope_mods);
        exported_ids = (uu___177_532.exported_ids);
        trans_exported_ids = (uu___177_532.trans_exported_ids);
        includes = (uu___177_532.includes);
        sigaccum = (uu___177_532.sigaccum);
        sigmap = (uu___177_532.sigmap);
        iface = (uu___177_532.iface);
        admitted_iface = (uu___177_532.admitted_iface);
        expect_typ = (uu___177_532.expect_typ);
        docs = (uu___177_532.docs);
        remaining_iface_decls = (uu___177_532.remaining_iface_decls);
        syntax_only = (uu___177_532.syntax_only)
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
      let uu____548 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____564  ->
                match uu____564 with
                | (m,uu____569) -> FStar_Ident.lid_equals l m)) in
      match uu____548 with
      | None  -> None
      | Some (uu____578,decls) -> Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____600 =
          FStar_List.partition
            (fun uu____614  ->
               match uu____614 with
               | (m,uu____619) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____600 with
        | (uu____622,rest) ->
            let uu___178_640 = env in
            {
              curmodule = (uu___178_640.curmodule);
              curmonad = (uu___178_640.curmonad);
              modules = (uu___178_640.modules);
              scope_mods = (uu___178_640.scope_mods);
              exported_ids = (uu___178_640.exported_ids);
              trans_exported_ids = (uu___178_640.trans_exported_ids);
              includes = (uu___178_640.includes);
              sigaccum = (uu___178_640.sigaccum);
              sigmap = (uu___178_640.sigmap);
              iface = (uu___178_640.iface);
              admitted_iface = (uu___178_640.admitted_iface);
              expect_typ = (uu___178_640.expect_typ);
              docs = (uu___178_640.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___178_640.syntax_only)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | None  -> let uu____659 = current_module env in qual uu____659 id
      | Some monad ->
          let uu____661 =
            let uu____662 = current_module env in qual uu____662 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____661 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___179_675 = env in
      {
        curmodule = (uu___179_675.curmodule);
        curmonad = (uu___179_675.curmonad);
        modules = (uu___179_675.modules);
        scope_mods = (uu___179_675.scope_mods);
        exported_ids = (uu___179_675.exported_ids);
        trans_exported_ids = (uu___179_675.trans_exported_ids);
        includes = (uu___179_675.includes);
        sigaccum = (uu___179_675.sigaccum);
        sigmap = (uu___179_675.sigmap);
        iface = (uu___179_675.iface);
        admitted_iface = (uu___179_675.admitted_iface);
        expect_typ = (uu___179_675.expect_typ);
        docs = (uu___179_675.docs);
        remaining_iface_decls = (uu___179_675.remaining_iface_decls);
        syntax_only = b
      }
let new_sigmap uu____685 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____689  ->
    let uu____690 = new_sigmap () in
    let uu____692 = new_sigmap () in
    let uu____694 = new_sigmap () in
    let uu____700 = new_sigmap () in
    let uu____706 = new_sigmap () in
    {
      curmodule = None;
      curmonad = None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____690;
      trans_exported_ids = uu____692;
      includes = uu____694;
      sigaccum = [];
      sigmap = uu____700;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____706;
      remaining_iface_decls = [];
      syntax_only = false
    }
let sigmap: env -> (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap =
  fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____726  ->
         match uu____726 with
         | (m,uu____730) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___180_740 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___180_740.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___181_741 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___181_741.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___181_741.FStar_Syntax_Syntax.sort)
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
        (fun uu____790  ->
           match uu____790 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____804 =
                   let uu____805 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____805 dd dq in
                 Some uu____804
               else None) in
    match t with | Some v1 -> Some (v1, false) | None  -> None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____838 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____866 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____879 -> false
let option_of_cont k_ignore uu___147_901 =
  match uu___147_901 with
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
        (fun uu____951  ->
           match uu____951 with
           | (f,uu____956) ->
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
  fun uu___148_997  ->
    match uu___148_997 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___149_1053 =
    match uu___149_1053 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
          let uu____1061 = get_exported_id_set env mname in
          match uu____1061 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____1077 = mex eikind in FStar_ST.read uu____1077 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____1084 = FStar_Util.smap_try_find env.includes mname in
          match uu____1084 with
          | None  -> []
          | Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
          then let uu____1104 = qual modul id in find_in_module uu____1104
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____1107 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___150_1112  ->
    match uu___150_1112 with
    | Exported_id_field  -> true
    | uu____1113 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___151_1211 =
    match uu___151_1211 with
    | (id',uu____1213,uu____1214) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___152_1218 =
    match uu___152_1218 with
    | (id',uu____1220,uu____1221) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1224 = current_module env in FStar_Ident.ids_of_lid uu____1224 in
  let proc uu___153_1229 =
    match uu___153_1229 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____1234) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____1237 = FStar_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____1237 id
    | uu____1240 -> Cont_ignore in
  let rec aux uu___154_1246 =
    match uu___154_1246 with
    | a::q ->
        let uu____1252 = proc a in
        option_of_cont (fun uu____1254  -> aux q) uu____1252
    | [] ->
        let uu____1255 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____1257  -> None) uu____1255 in
  aux env.scope_mods
let found_local_binding r uu____1280 =
  match uu____1280 with
  | (id',x,mut) -> let uu____1287 = bv_to_name x r in (uu____1287, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____1329 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____1329 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found
let try_lookup_id:
  env -> FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) option =
  fun env  ->
    fun id  ->
      let uu____1353 = unmangleOpName id in
      match uu____1353 with
      | Some f -> Some f
      | uu____1367 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1374 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1374) (fun uu____1379  -> Cont_fail)
            (fun uu____1382  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1389  -> fun uu____1390  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1397  -> fun uu____1398  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1455 ->
        let lid = qualify env id in
        let uu____1457 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____1457 with
         | Some r -> let uu____1470 = k_global_def lid r in Some uu____1470
         | None  -> None)
    | None  -> None in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1483 = current_module env in qual uu____1483 id in
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
           let uu____1494 = current_module env in
           FStar_Ident.lid_equals lid uu____1494)
        ||
        (FStar_List.existsb (fun x  -> FStar_Ident.lid_equals lid (fst x))
           env.modules)
let resolve_module_name:
  env -> FStar_Ident.lident -> Prims.bool -> FStar_Ident.lident option =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
        let rec aux uu___155_1522 =
          match uu___155_1522 with
          | [] ->
              let uu____1525 = module_is_defined env lid in
              if uu____1525 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1532 =
                  let uu____1534 = FStar_Ident.path_of_lid ns in
                  let uu____1536 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1534 uu____1536 in
                FStar_Ident.lid_of_path uu____1532
                  (FStar_Ident.range_of_lid lid) in
              let uu____1538 = module_is_defined env new_lid in
              if uu____1538 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1543 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1549::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____1564 =
          let uu____1565 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____1565 in
        if uu____1564
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Syntax_Const.prims_lid
           then ()
           else
             (let uu____1567 =
                let uu____1568 =
                  let uu____1571 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____1571, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____1568 in
              raise uu____1567))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____1581 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____1584 = resolve_module_name env modul_orig true in
          (match uu____1584 with
           | Some modul_res -> fail_if_curmodule env modul_orig modul_res
           | uu____1587 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___156_1597  ->
           match uu___156_1597 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1599 -> false) env.scope_mods
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
                 let uu____1657 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____1657
                   (FStar_Util.map_option
                      (fun uu____1681  ->
                         match uu____1681 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____1698 =
          is_full_path &&
            (let uu____1699 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____1699) in
        if uu____1698
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1716 = aux ns_rev_prefix ns_last_id in
               (match uu____1716 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____1752 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____1752 with
      | (uu____1757,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1857::uu____1858 ->
      let uu____1860 =
        let uu____1862 =
          let uu____1863 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____1863 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____1862 true in
      (match uu____1860 with
       | None  -> None
       | Some modul ->
           let uu____1866 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____1868  -> None) uu____1866)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___157_1886 =
  match uu___157_1886 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1971 = k_global_def lid1 def in cont_of_option k uu____1971 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1992 = k_local_binding l in
       cont_of_option Cont_fail uu____1992)
    (fun r  ->
       let uu____1995 = k_rec_binding r in
       cont_of_option Cont_fail uu____1995) (fun uu____1997  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____2004,uu____2005,uu____2006,l,uu____2008,uu____2009) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___158_2014  ->
               match uu___158_2014 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____2016,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____2023 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____2027,uu____2028,uu____2029)
        -> None
    | uu____2030 -> None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____2041 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____2045 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____2045 then Some fv else None) in
      FStar_All.pipe_right uu____2041 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____2065 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____2065 ns)
let try_lookup_name:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> foundname option =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___162_2094 =
            match uu___162_2094 with
            | (uu____2098,true ) when exclude_interf -> None
            | (se,uu____2100) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____2102 ->
                     let uu____2111 =
                       let uu____2112 =
                         let uu____2115 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____2115, false) in
                       Term_name uu____2112 in
                     Some uu____2111
                 | FStar_Syntax_Syntax.Sig_datacon uu____2116 ->
                     let uu____2124 =
                       let uu____2125 =
                         let uu____2128 =
                           let uu____2129 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____2129 in
                         (uu____2128, false) in
                       Term_name uu____2125 in
                     Some uu____2124
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____2131,lbs),uu____2133,uu____2134) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____2145 =
                       let uu____2146 =
                         let uu____2149 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____2149, false) in
                       Term_name uu____2146 in
                     Some uu____2145
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____2151,uu____2152) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____2155 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___159_2157  ->
                                  match uu___159_2157 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____2158 -> false))) in
                     if uu____2155
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____2162 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             (FStar_All.pipe_right quals
                                (FStar_Util.for_some
                                   (fun uu___160_2164  ->
                                      match uu___160_2164 with
                                      | FStar_Syntax_Syntax.Projector
                                          uu____2165 -> true
                                      | FStar_Syntax_Syntax.Discriminator
                                          uu____2168 -> true
                                      | uu____2169 -> false))) in
                         if uu____2162
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____2171 =
                         FStar_Util.find_map quals
                           (fun uu___161_2173  ->
                              match uu___161_2173 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____2176 -> None) in
                       (match uu____2171 with
                        | Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
                        | uu____2188 ->
                            let uu____2190 =
                              let uu____2191 =
                                let uu____2194 =
                                  let uu____2195 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____2195 in
                                (uu____2194, false) in
                              Term_name uu____2191 in
                            Some uu____2190)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____2200 ->
                     Some (Eff_name (se, source_lid))
                 | uu____2207 -> None) in
          let k_local_binding r =
            let uu____2219 =
              let uu____2220 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____2220 in
            Some uu____2219 in
          let k_rec_binding uu____2230 =
            match uu____2230 with
            | (id,l,dd) ->
                let uu____2238 =
                  let uu____2239 =
                    let uu____2242 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____2242, false) in
                  Term_name uu____2239 in
                Some uu____2238 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2246 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2246 with
                 | Some f -> Some (Term_name f)
                 | uu____2256 -> None)
            | uu____2260 -> None in
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
        let uu____2283 = try_lookup_name true exclude_interf env lid in
        match uu____2283 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____2292 -> None
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2305 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2305 with | Some (o,l1) -> Some l1 | uu____2314 -> None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list) option
  =
  fun env  ->
    fun l  ->
      let uu____2330 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2330 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2339;
             FStar_Syntax_Syntax.sigquals = uu____2340;
             FStar_Syntax_Syntax.sigmeta = uu____2341;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2351;
             FStar_Syntax_Syntax.sigquals = uu____2352;
             FStar_Syntax_Syntax.sigmeta = uu____2353;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____2362,uu____2363,uu____2364,uu____2365,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2367;
             FStar_Syntax_Syntax.sigquals = uu____2368;
             FStar_Syntax_Syntax.sigmeta = uu____2369;_},l1)
          -> Some (l1, cattributes)
      | uu____2380 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl option =
  fun env  ->
    fun l  ->
      let uu____2396 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2396 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2402;
             FStar_Syntax_Syntax.sigquals = uu____2403;
             FStar_Syntax_Syntax.sigmeta = uu____2404;_},uu____2405)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2410;
             FStar_Syntax_Syntax.sigquals = uu____2411;
             FStar_Syntax_Syntax.sigmeta = uu____2412;_},uu____2413)
          -> Some ne
      | uu____2417 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2429 = try_lookup_effect_name env lid in
      match uu____2429 with | None  -> false | Some uu____2431 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2441 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2441 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____2447,uu____2448,uu____2449,uu____2450);
             FStar_Syntax_Syntax.sigrng = uu____2451;
             FStar_Syntax_Syntax.sigquals = uu____2452;
             FStar_Syntax_Syntax.sigmeta = uu____2453;_},uu____2454)
          ->
          let rec aux new_name =
            let uu____2465 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2465 with
            | None  -> None
            | Some (s,uu____2475) ->
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
                     (uu____2481,uu____2482,uu____2483,cmp,uu____2485) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2489 -> None) in
          aux l'
      | Some (uu____2490,l') -> Some l'
      | uu____2494 -> None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___163_2517 =
        match uu___163_2517 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2522,uu____2523,uu____2524);
             FStar_Syntax_Syntax.sigrng = uu____2525;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2527;_},uu____2528)
            -> Some quals
        | uu____2531 -> None in
      let uu____2535 =
        resolve_in_open_namespaces' env lid (fun uu____2539  -> None)
          (fun uu____2541  -> None) k_global_def in
      match uu____2535 with | Some quals -> quals | uu____2547 -> []
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul option =
  fun env  ->
    fun path  ->
      let uu____2561 =
        FStar_List.tryFind
          (fun uu____2567  ->
             match uu____2567 with
             | (mlid,modul) ->
                 let uu____2572 = FStar_Ident.path_of_lid mlid in
                 uu____2572 = path) env.modules in
      match uu____2561 with
      | Some (uu____2576,modul) -> Some modul
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___164_2600 =
        match uu___164_2600 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2604,lbs),uu____2606,uu____2607);
             FStar_Syntax_Syntax.sigrng = uu____2608;
             FStar_Syntax_Syntax.sigquals = uu____2609;
             FStar_Syntax_Syntax.sigmeta = uu____2610;_},uu____2611)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2623 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2623
        | uu____2624 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2627  -> None)
        (fun uu____2628  -> None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___165_2649 =
        match uu___165_2649 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2656,uu____2657);
             FStar_Syntax_Syntax.sigrng = uu____2658;
             FStar_Syntax_Syntax.sigquals = uu____2659;
             FStar_Syntax_Syntax.sigmeta = uu____2660;_},uu____2661)
            ->
            FStar_Util.find_map (snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2677 -> None)
        | uu____2682 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2689  -> None)
        (fun uu____2692  -> None) k_global_def
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
          let uu____2723 = try_lookup_name any_val exclude_interf env lid in
          match uu____2723 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2732 -> None
let try_lookup_lid:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2756 = try_lookup_lid env l in
      match uu____2756 with
      | None  -> None
      | Some (e,uu____2764) ->
          let uu____2767 =
            let uu____2768 = FStar_Syntax_Subst.compress e in
            uu____2768.FStar_Syntax_Syntax.n in
          (match uu____2767 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2777 -> None)
let try_lookup_lid_no_resolve:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___182_2790 = env in
        {
          curmodule = (uu___182_2790.curmodule);
          curmonad = (uu___182_2790.curmonad);
          modules = (uu___182_2790.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___182_2790.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___182_2790.sigaccum);
          sigmap = (uu___182_2790.sigmap);
          iface = (uu___182_2790.iface);
          admitted_iface = (uu___182_2790.admitted_iface);
          expect_typ = (uu___182_2790.expect_typ);
          docs = (uu___182_2790.docs);
          remaining_iface_decls = (uu___182_2790.remaining_iface_decls);
          syntax_only = (uu___182_2790.syntax_only)
        } in
      try_lookup_lid env' l
let try_lookup_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___167_2818 =
        match uu___167_2818 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2822,uu____2823,uu____2824);
             FStar_Syntax_Syntax.sigrng = uu____2825;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2827;_},uu____2828)
            ->
            let uu____2830 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___166_2832  ->
                      match uu___166_2832 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2833 -> false)) in
            if uu____2830
            then
              let uu____2835 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2835
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2837;
             FStar_Syntax_Syntax.sigrng = uu____2838;
             FStar_Syntax_Syntax.sigquals = uu____2839;
             FStar_Syntax_Syntax.sigmeta = uu____2840;_},uu____2841)
            ->
            let uu____2850 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2850
        | uu____2851 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2854  -> None)
        (fun uu____2855  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___168_2876 =
        match uu___168_2876 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2881,uu____2882,uu____2883,uu____2884,datas,uu____2886);
             FStar_Syntax_Syntax.sigrng = uu____2887;
             FStar_Syntax_Syntax.sigquals = uu____2888;
             FStar_Syntax_Syntax.sigmeta = uu____2889;_},uu____2890)
            -> Some datas
        | uu____2897 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2902  -> None)
        (fun uu____2904  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____2938 =
    let uu____2939 =
      let uu____2942 =
        let uu____2944 = FStar_ST.read record_cache in
        FStar_List.hd uu____2944 in
      let uu____2952 = FStar_ST.read record_cache in uu____2942 :: uu____2952 in
    FStar_ST.write record_cache uu____2939 in
  let pop1 uu____2967 =
    let uu____2968 =
      let uu____2971 = FStar_ST.read record_cache in FStar_List.tl uu____2971 in
    FStar_ST.write record_cache uu____2968 in
  let peek uu____2987 =
    let uu____2988 = FStar_ST.read record_cache in FStar_List.hd uu____2988 in
  let insert r =
    let uu____3000 =
      let uu____3003 = let uu____3005 = peek () in r :: uu____3005 in
      let uu____3007 =
        let uu____3010 = FStar_ST.read record_cache in
        FStar_List.tl uu____3010 in
      uu____3003 :: uu____3007 in
    FStar_ST.write record_cache uu____3000 in
  let commit1 uu____3026 =
    let uu____3027 = FStar_ST.read record_cache in
    match uu____3027 with
    | hd1::uu____3035::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____3048 -> failwith "Impossible" in
  let filter1 uu____3054 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____3061 =
           let uu____3064 = FStar_ST.read record_cache in filtered ::
             uu____3064 in
         FStar_ST.write record_cache uu____3061) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____3138 = record_cache_aux_with_filter in
  match uu____3138 with | (aux,uu____3176) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____3216 = record_cache_aux_with_filter in
  match uu____3216 with | (uu____3239,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____3280 = record_cache_aux in
  match uu____3280 with
  | (push1,uu____3300,uu____3301,uu____3302,uu____3303) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3329 = record_cache_aux in
  match uu____3329 with
  | (uu____3348,pop1,uu____3350,uu____3351,uu____3352) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____3379 = record_cache_aux in
  match uu____3379 with
  | (uu____3399,uu____3400,peek,uu____3402,uu____3403) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____3429 = record_cache_aux in
  match uu____3429 with
  | (uu____3448,uu____3449,uu____3450,insert,uu____3452) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____3478 = record_cache_aux in
  match uu____3478 with
  | (uu____3497,uu____3498,uu____3499,uu____3500,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3543) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___169_3552  ->
                   match uu___169_3552 with
                   | FStar_Syntax_Syntax.RecordType uu____3553 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____3558 -> true
                   | uu____3563 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___170_3571  ->
                      match uu___170_3571 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3573,uu____3574,uu____3575,uu____3576,uu____3577);
                          FStar_Syntax_Syntax.sigrng = uu____3578;
                          FStar_Syntax_Syntax.sigquals = uu____3579;
                          FStar_Syntax_Syntax.sigmeta = uu____3580;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3584 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___171_3586  ->
                    match uu___171_3586 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____3590,uu____3591,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____3593;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____3595;_} ->
                        let uu____3600 =
                          let uu____3601 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3601 in
                        (match uu____3600 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3605,t,uu____3607,uu____3608,uu____3609);
                             FStar_Syntax_Syntax.sigrng = uu____3610;
                             FStar_Syntax_Syntax.sigquals = uu____3611;
                             FStar_Syntax_Syntax.sigmeta = uu____3612;_} ->
                             let uu____3616 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3616 with
                              | (formals,uu____3625) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3651  ->
                                            match uu____3651 with
                                            | (x,q) ->
                                                let uu____3659 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3659
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3690  ->
                                            match uu____3690 with
                                            | (x,q) ->
                                                let uu____3699 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____3699,
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
                                  ((let uu____3711 =
                                      let uu____3713 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3713 in
                                    FStar_ST.write new_globs uu____3711);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3729 =
                                            match uu____3729 with
                                            | (id,uu____3735) ->
                                                let modul =
                                                  let uu____3741 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3741.FStar_Ident.str in
                                                let uu____3742 =
                                                  get_exported_id_set e modul in
                                                (match uu____3742 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____3758 =
                                                         let uu____3759 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3759 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3758);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3766 =
                                                               let uu____3767
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____3767.FStar_Ident.ident in
                                                             uu____3766.FStar_Ident.idText in
                                                           let uu____3769 =
                                                             let uu____3770 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3770 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3769))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3783 -> ())
                    | uu____3784 -> ()))
        | uu____3785 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3800 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3800 with
        | (ns,id) ->
            let uu____3810 = peek_record_cache () in
            FStar_Util.find_map uu____3810
              (fun record  ->
                 let uu____3813 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3816  -> None) uu____3813) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3817  -> Cont_ignore) (fun uu____3818  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3821 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3821)
        (fun k  -> fun uu____3824  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let uu____3835 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3835 with
      | Some r when r.is_record -> Some r
      | uu____3839 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3853 = try_lookup_record_by_field_name env lid in
        match uu____3853 with
        | Some record' when
            let uu____3856 =
              let uu____3857 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3857 in
            let uu____3859 =
              let uu____3860 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3860 in
            uu____3856 = uu____3859 ->
            let uu____3862 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3864  -> Cont_ok ()) in
            (match uu____3862 with
             | Cont_ok uu____3865 -> true
             | uu____3866 -> false)
        | uu____3868 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) option =
  fun env  ->
    fun fieldname  ->
      let uu____3881 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3881 with
      | Some r ->
          let uu____3887 =
            let uu____3890 =
              let uu____3891 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3891
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3890, (r.is_record)) in
          Some uu____3887
      | uu____3894 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3904  ->
    let uu____3905 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3905
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3917  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___172_3926  ->
      match uu___172_3926 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___173_3950 =
            match uu___173_3950 with
            | Rec_binding uu____3951 -> true
            | uu____3952 -> false in
          let this_env =
            let uu___183_3954 = env in
            let uu____3955 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___183_3954.curmodule);
              curmonad = (uu___183_3954.curmonad);
              modules = (uu___183_3954.modules);
              scope_mods = uu____3955;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___183_3954.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___183_3954.sigaccum);
              sigmap = (uu___183_3954.sigmap);
              iface = (uu___183_3954.iface);
              admitted_iface = (uu___183_3954.admitted_iface);
              expect_typ = (uu___183_3954.expect_typ);
              docs = (uu___183_3954.docs);
              remaining_iface_decls = (uu___183_3954.remaining_iface_decls);
              syntax_only = (uu___183_3954.syntax_only)
            } in
          let uu____3957 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3957 with | None  -> true | Some uu____3963 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___184_3976 = env in
      {
        curmodule = (uu___184_3976.curmodule);
        curmonad = (uu___184_3976.curmonad);
        modules = (uu___184_3976.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___184_3976.exported_ids);
        trans_exported_ids = (uu___184_3976.trans_exported_ids);
        includes = (uu___184_3976.includes);
        sigaccum = (uu___184_3976.sigaccum);
        sigmap = (uu___184_3976.sigmap);
        iface = (uu___184_3976.iface);
        admitted_iface = (uu___184_3976.admitted_iface);
        expect_typ = (uu___184_3976.expect_typ);
        docs = (uu___184_3976.docs);
        remaining_iface_decls = (uu___184_3976.remaining_iface_decls);
        syntax_only = (uu___184_3976.syntax_only)
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
        let uu____4025 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____4025
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
          | Some (se,uu____4047) ->
              let uu____4050 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____4050 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____4055 =
          let uu____4056 =
            let uu____4059 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____4059, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____4056 in
        raise uu____4055 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____4066 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____4071 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____4077 -> (true, true)
          | uu____4082 -> (false, false) in
        match uu____4066 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____4087 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____4090 =
                     let uu____4091 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____4091 in
                   if uu____4090 then Some l else None) in
            (match uu____4087 with
             | Some l when
                 let uu____4095 = FStar_Options.interactive () in
                 Prims.op_Negation uu____4095 -> err1 l
             | uu____4096 ->
                 (extract_record env globals s;
                  (let uu___185_4101 = env in
                   {
                     curmodule = (uu___185_4101.curmodule);
                     curmonad = (uu___185_4101.curmonad);
                     modules = (uu___185_4101.modules);
                     scope_mods = (uu___185_4101.scope_mods);
                     exported_ids = (uu___185_4101.exported_ids);
                     trans_exported_ids = (uu___185_4101.trans_exported_ids);
                     includes = (uu___185_4101.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___185_4101.sigmap);
                     iface = (uu___185_4101.iface);
                     admitted_iface = (uu___185_4101.admitted_iface);
                     expect_typ = (uu___185_4101.expect_typ);
                     docs = (uu___185_4101.docs);
                     remaining_iface_decls =
                       (uu___185_4101.remaining_iface_decls);
                     syntax_only = (uu___185_4101.syntax_only)
                   }))) in
      let env2 =
        let uu___186_4103 = env1 in
        let uu____4104 = FStar_ST.read globals in
        {
          curmodule = (uu___186_4103.curmodule);
          curmonad = (uu___186_4103.curmonad);
          modules = (uu___186_4103.modules);
          scope_mods = uu____4104;
          exported_ids = (uu___186_4103.exported_ids);
          trans_exported_ids = (uu___186_4103.trans_exported_ids);
          includes = (uu___186_4103.includes);
          sigaccum = (uu___186_4103.sigaccum);
          sigmap = (uu___186_4103.sigmap);
          iface = (uu___186_4103.iface);
          admitted_iface = (uu___186_4103.admitted_iface);
          expect_typ = (uu___186_4103.expect_typ);
          docs = (uu___186_4103.docs);
          remaining_iface_decls = (uu___186_4103.remaining_iface_decls);
          syntax_only = (uu___186_4103.syntax_only)
        } in
      let uu____4109 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4123) ->
            let uu____4128 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____4128)
        | uu____4142 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____4109 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____4172  ->
                   match uu____4172 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____4183 =
                                  let uu____4185 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____4185 in
                                FStar_ST.write globals uu____4183);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____4194 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____4194.FStar_Ident.str in
                                    ((let uu____4196 =
                                        get_exported_id_set env3 modul in
                                      match uu____4196 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____4211 =
                                            let uu____4212 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____4212 in
                                          FStar_ST.write my_exported_ids
                                            uu____4211
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
              let uu___187_4224 = env3 in
              let uu____4225 = FStar_ST.read globals in
              {
                curmodule = (uu___187_4224.curmodule);
                curmonad = (uu___187_4224.curmonad);
                modules = (uu___187_4224.modules);
                scope_mods = uu____4225;
                exported_ids = (uu___187_4224.exported_ids);
                trans_exported_ids = (uu___187_4224.trans_exported_ids);
                includes = (uu___187_4224.includes);
                sigaccum = (uu___187_4224.sigaccum);
                sigmap = (uu___187_4224.sigmap);
                iface = (uu___187_4224.iface);
                admitted_iface = (uu___187_4224.admitted_iface);
                expect_typ = (uu___187_4224.expect_typ);
                docs = (uu___187_4224.docs);
                remaining_iface_decls = (uu___187_4224.remaining_iface_decls);
                syntax_only = (uu___187_4224.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____4238 =
        let uu____4241 = resolve_module_name env ns false in
        match uu____4241 with
        | None  ->
            let modules = env.modules in
            let uu____4249 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____4255  ->
                      match uu____4255 with
                      | (m,uu____4259) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____4249
            then (ns, Open_namespace)
            else
              (let uu____4263 =
                 let uu____4264 =
                   let uu____4267 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____4267, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____4264 in
               raise uu____4263)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____4238 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____4283 = resolve_module_name env ns false in
      match uu____4283 with
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____4289 = current_module env1 in
              uu____4289.FStar_Ident.str in
            (let uu____4291 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____4291 with
             | None  -> ()
             | Some incl ->
                 let uu____4304 =
                   let uu____4306 = FStar_ST.read incl in ns1 :: uu____4306 in
                 FStar_ST.write incl uu____4304);
            (match () with
             | () ->
                 let uu____4314 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____4314 with
                  | Some ns_trans_exports ->
                      ((let uu____4327 =
                          let uu____4338 = get_exported_id_set env1 curmod in
                          let uu____4343 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____4338, uu____4343) in
                        match uu____4327 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____4383 = ns_trans_exports k in
                                FStar_ST.read uu____4383 in
                              let ex = cur_exports k in
                              (let uu____4392 =
                                 let uu____4393 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____4393 ns_ex in
                               FStar_ST.write ex uu____4392);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____4403 =
                                     let uu____4404 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____4404 ns_ex in
                                   FStar_ST.write trans_ex uu____4403) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____4410 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____4424 =
                        let uu____4425 =
                          let uu____4428 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____4428, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____4425 in
                      raise uu____4424))))
      | uu____4429 ->
          let uu____4431 =
            let uu____4432 =
              let uu____4435 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____4435, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____4432 in
          raise uu____4431
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____4448 = module_is_defined env l in
        if uu____4448
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____4451 =
             let uu____4452 =
               let uu____4455 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____4455, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____4452 in
           raise uu____4451)
let push_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____4472 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____4472 with
              | None  -> ()
              | Some old_doc ->
                  let uu____4475 =
                    let uu____4476 = FStar_Ident.string_of_lid l in
                    let uu____4477 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____4478 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____4476 uu____4477 uu____4478 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____4475);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____4488 = try_lookup_lid env l in
                (match uu____4488 with
                 | None  ->
                     ((let uu____4495 =
                         let uu____4496 = FStar_Options.interactive () in
                         Prims.op_Negation uu____4496 in
                       if uu____4495
                       then
                         let uu____4497 =
                           let uu____4498 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____4499 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____4498 uu____4499 in
                         FStar_Util.print_string uu____4497
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___188_4505 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___188_4505.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___188_4505.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___188_4505.FStar_Syntax_Syntax.sigmeta)
                           }), false)))
                 | Some uu____4506 -> ())
            | uu____4511 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4525) ->
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
                                (lid,uu____4533,uu____4534,uu____4535,uu____4536,uu____4537)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4542 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4545,uu____4546) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4550,lbs),uu____4552,uu____4553) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4566 =
                               let uu____4567 =
                                 let uu____4568 =
                                   let uu____4573 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4573.FStar_Syntax_Syntax.fv_name in
                                 uu____4568.FStar_Syntax_Syntax.v in
                               uu____4567.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4566))
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
                               let uu____4583 =
                                 let uu____4588 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4588.FStar_Syntax_Syntax.fv_name in
                               uu____4583.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___189_4595 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___189_4595.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___189_4595.FStar_Syntax_Syntax.sigmeta)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4602 -> ()));
      (let curmod =
         let uu____4604 = current_module env in uu____4604.FStar_Ident.str in
       (let uu____4606 =
          let uu____4617 = get_exported_id_set env curmod in
          let uu____4622 = get_trans_exported_id_set env curmod in
          (uu____4617, uu____4622) in
        match uu____4606 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4662 = cur_ex eikind in FStar_ST.read uu____4662 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4670 =
                let uu____4671 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4671 in
              FStar_ST.write cur_trans_ex_set_ref uu____4670 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4677 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___190_4689 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___190_4689.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___190_4689.exported_ids);
                    trans_exported_ids = (uu___190_4689.trans_exported_ids);
                    includes = (uu___190_4689.includes);
                    sigaccum = [];
                    sigmap = (uu___190_4689.sigmap);
                    iface = (uu___190_4689.iface);
                    admitted_iface = (uu___190_4689.admitted_iface);
                    expect_typ = (uu___190_4689.expect_typ);
                    docs = (uu___190_4689.docs);
                    remaining_iface_decls =
                      (uu___190_4689.remaining_iface_decls);
                    syntax_only = (uu___190_4689.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4703 =
       let uu____4705 = FStar_ST.read stack in env :: uu____4705 in
     FStar_ST.write stack uu____4703);
    (let uu___191_4713 = env in
     let uu____4714 = FStar_Util.smap_copy (sigmap env) in
     let uu____4720 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___191_4713.curmodule);
       curmonad = (uu___191_4713.curmonad);
       modules = (uu___191_4713.modules);
       scope_mods = (uu___191_4713.scope_mods);
       exported_ids = (uu___191_4713.exported_ids);
       trans_exported_ids = (uu___191_4713.trans_exported_ids);
       includes = (uu___191_4713.includes);
       sigaccum = (uu___191_4713.sigaccum);
       sigmap = uu____4714;
       iface = (uu___191_4713.iface);
       admitted_iface = (uu___191_4713.admitted_iface);
       expect_typ = (uu___191_4713.expect_typ);
       docs = uu____4720;
       remaining_iface_decls = (uu___191_4713.remaining_iface_decls);
       syntax_only = (uu___191_4713.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____4725  ->
    let uu____4726 = FStar_ST.read stack in
    match uu____4726 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4739 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4746 = FStar_ST.read stack in
     match uu____4746 with
     | uu____4751::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4758 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4767  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4781 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4783 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4801 = FStar_Util.smap_try_find sm' k in
              match uu____4801 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___192_4817 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___192_4817.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___192_4817.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___192_4817.FStar_Syntax_Syntax.sigmeta)
                          }
                      | uu____4818 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4821 -> ()));
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
            (let uu____4873 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4873);
            (match () with
             | () ->
                 ((let uu____4878 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4878);
                  (match () with
                   | () ->
                       ((let uu____4883 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4883);
                        (match () with
                         | () ->
                             let uu___193_4892 = env1 in
                             let uu____4893 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___193_4892.curmonad);
                               modules = (uu___193_4892.modules);
                               scope_mods = uu____4893;
                               exported_ids = (uu___193_4892.exported_ids);
                               trans_exported_ids =
                                 (uu___193_4892.trans_exported_ids);
                               includes = (uu___193_4892.includes);
                               sigaccum = (uu___193_4892.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___193_4892.expect_typ);
                               docs = (uu___193_4892.docs);
                               remaining_iface_decls =
                                 (uu___193_4892.remaining_iface_decls);
                               syntax_only = (uu___193_4892.syntax_only)
                             }))))) in
          let uu____4896 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4908  ->
                    match uu____4908 with
                    | (l,uu____4912) -> FStar_Ident.lid_equals l mname)) in
          match uu____4896 with
          | None  -> let uu____4917 = prep env in (uu____4917, false)
          | Some (uu____4918,m) ->
              ((let uu____4923 =
                  (let uu____4924 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4924) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4923
                then
                  let uu____4925 =
                    let uu____4926 =
                      let uu____4929 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4929, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4926 in
                  raise uu____4925
                else ());
               (let uu____4931 = let uu____4932 = push env in prep uu____4932 in
                (uu____4931, true)))
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
          let uu___194_4942 = env in
          {
            curmodule = (uu___194_4942.curmodule);
            curmonad = (Some mname);
            modules = (uu___194_4942.modules);
            scope_mods = (uu___194_4942.scope_mods);
            exported_ids = (uu___194_4942.exported_ids);
            trans_exported_ids = (uu___194_4942.trans_exported_ids);
            includes = (uu___194_4942.includes);
            sigaccum = (uu___194_4942.sigaccum);
            sigmap = (uu___194_4942.sigmap);
            iface = (uu___194_4942.iface);
            admitted_iface = (uu___194_4942.admitted_iface);
            expect_typ = (uu___194_4942.expect_typ);
            docs = (uu___194_4942.docs);
            remaining_iface_decls = (uu___194_4942.remaining_iface_decls);
            syntax_only = (uu___194_4942.syntax_only)
          }
let fail_or env lookup lid =
  let uu____4971 = lookup lid in
  match uu____4971 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4977  ->
             match uu____4977 with
             | (lid1,uu____4981) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4990 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4990
               (FStar_Ident.range_of_lid lid) in
           let uu____4991 = resolve_module_name env modul true in
           match uu____4991 with
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
  let uu____5021 = lookup id in
  match uu____5021 with
  | None  ->
      raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r