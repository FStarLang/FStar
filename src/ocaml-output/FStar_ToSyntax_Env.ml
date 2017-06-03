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
    match projectee with | Local_binding _0 -> true | uu____92 -> false
let __proj__Local_binding__item___0: scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0
let uu___is_Rec_binding: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____104 -> false
let __proj__Rec_binding__item___0: scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0
let uu___is_Module_abbrev: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____116 -> false
let __proj__Module_abbrev__item___0: scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0
let uu___is_Open_module_or_namespace: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____128 -> false
let __proj__Open_module_or_namespace__item___0:
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0
let uu___is_Top_level_def: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____140 -> false
let __proj__Top_level_def__item___0: scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0
let uu___is_Record_or_dc: scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____152 -> false
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
    | uu____164 -> false
let uu___is_Exported_id_field: exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____168 -> false
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
    match projectee with | Term_name _0 -> true | uu____350 -> false
let __proj__Term_name__item___0:
  foundname -> (FStar_Syntax_Syntax.typ* Prims.bool) =
  fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____370 -> false
let __proj__Eff_name__item___0:
  foundname -> (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___173_390 = env in
      {
        curmodule = (uu___173_390.curmodule);
        curmonad = (uu___173_390.curmonad);
        modules = (uu___173_390.modules);
        scope_mods = (uu___173_390.scope_mods);
        exported_ids = (uu___173_390.exported_ids);
        trans_exported_ids = (uu___173_390.trans_exported_ids);
        includes = (uu___173_390.includes);
        sigaccum = (uu___173_390.sigaccum);
        sigmap = (uu___173_390.sigmap);
        iface = b;
        admitted_iface = (uu___173_390.admitted_iface);
        expect_typ = (uu___173_390.expect_typ);
        docs = (uu___173_390.docs);
        remaining_iface_decls = (uu___173_390.remaining_iface_decls);
        syntax_only = (uu___173_390.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___174_400 = e in
      {
        curmodule = (uu___174_400.curmodule);
        curmonad = (uu___174_400.curmonad);
        modules = (uu___174_400.modules);
        scope_mods = (uu___174_400.scope_mods);
        exported_ids = (uu___174_400.exported_ids);
        trans_exported_ids = (uu___174_400.trans_exported_ids);
        includes = (uu___174_400.includes);
        sigaccum = (uu___174_400.sigaccum);
        sigmap = (uu___174_400.sigmap);
        iface = (uu___174_400.iface);
        admitted_iface = b;
        expect_typ = (uu___174_400.expect_typ);
        docs = (uu___174_400.docs);
        remaining_iface_decls = (uu___174_400.remaining_iface_decls);
        syntax_only = (uu___174_400.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___175_410 = e in
      {
        curmodule = (uu___175_410.curmodule);
        curmonad = (uu___175_410.curmonad);
        modules = (uu___175_410.modules);
        scope_mods = (uu___175_410.scope_mods);
        exported_ids = (uu___175_410.exported_ids);
        trans_exported_ids = (uu___175_410.trans_exported_ids);
        includes = (uu___175_410.includes);
        sigaccum = (uu___175_410.sigaccum);
        sigmap = (uu___175_410.sigmap);
        iface = (uu___175_410.iface);
        admitted_iface = (uu___175_410.admitted_iface);
        expect_typ = b;
        docs = (uu___175_410.docs);
        remaining_iface_decls = (uu___175_410.remaining_iface_decls);
        syntax_only = (uu___175_410.syntax_only)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____423 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____423 with
      | None  -> []
      | Some exported_id_set ->
          let uu____427 =
            let uu____428 = exported_id_set Exported_id_term_type in
            FStar_ST.read uu____428 in
          FStar_All.pipe_right uu____427 FStar_Util.set_elements
let open_modules:
  env -> (FStar_Ident.lident* FStar_Syntax_Syntax.modul) Prims.list =
  fun e  -> e.modules
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___176_446 = e in
      {
        curmodule = (Some l);
        curmonad = (uu___176_446.curmonad);
        modules = (uu___176_446.modules);
        scope_mods = (uu___176_446.scope_mods);
        exported_ids = (uu___176_446.exported_ids);
        trans_exported_ids = (uu___176_446.trans_exported_ids);
        includes = (uu___176_446.includes);
        sigaccum = (uu___176_446.sigaccum);
        sigmap = (uu___176_446.sigmap);
        iface = (uu___176_446.iface);
        admitted_iface = (uu___176_446.admitted_iface);
        expect_typ = (uu___176_446.expect_typ);
        docs = (uu___176_446.docs);
        remaining_iface_decls = (uu___176_446.remaining_iface_decls);
        syntax_only = (uu___176_446.syntax_only)
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
      let uu____459 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____475  ->
                match uu____475 with
                | (m,uu____480) -> FStar_Ident.lid_equals l m)) in
      match uu____459 with
      | None  -> None
      | Some (uu____489,decls) -> Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____508 =
          FStar_List.partition
            (fun uu____522  ->
               match uu____522 with
               | (m,uu____527) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____508 with
        | (uu____530,rest) ->
            let uu___177_548 = env in
            {
              curmodule = (uu___177_548.curmodule);
              curmonad = (uu___177_548.curmonad);
              modules = (uu___177_548.modules);
              scope_mods = (uu___177_548.scope_mods);
              exported_ids = (uu___177_548.exported_ids);
              trans_exported_ids = (uu___177_548.trans_exported_ids);
              includes = (uu___177_548.includes);
              sigaccum = (uu___177_548.sigaccum);
              sigmap = (uu___177_548.sigmap);
              iface = (uu___177_548.iface);
              admitted_iface = (uu___177_548.admitted_iface);
              expect_typ = (uu___177_548.expect_typ);
              docs = (uu___177_548.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___177_548.syntax_only)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | None  -> let uu____563 = current_module env in qual uu____563 id
      | Some monad ->
          let uu____565 =
            let uu____566 = current_module env in qual uu____566 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____565 id
let syntax_only: env -> Prims.bool = fun env  -> env.syntax_only
let set_syntax_only: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___178_576 = env in
      {
        curmodule = (uu___178_576.curmodule);
        curmonad = (uu___178_576.curmonad);
        modules = (uu___178_576.modules);
        scope_mods = (uu___178_576.scope_mods);
        exported_ids = (uu___178_576.exported_ids);
        trans_exported_ids = (uu___178_576.trans_exported_ids);
        includes = (uu___178_576.includes);
        sigaccum = (uu___178_576.sigaccum);
        sigmap = (uu___178_576.sigmap);
        iface = (uu___178_576.iface);
        admitted_iface = (uu___178_576.admitted_iface);
        expect_typ = (uu___178_576.expect_typ);
        docs = (uu___178_576.docs);
        remaining_iface_decls = (uu___178_576.remaining_iface_decls);
        syntax_only = b
      }
let new_sigmap uu____584 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____587  ->
    let uu____588 = new_sigmap () in
    let uu____590 = new_sigmap () in
    let uu____592 = new_sigmap () in
    let uu____598 = new_sigmap () in
    let uu____604 = new_sigmap () in
    {
      curmodule = None;
      curmonad = None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____588;
      trans_exported_ids = uu____590;
      includes = uu____592;
      sigaccum = [];
      sigmap = uu____598;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____604;
      remaining_iface_decls = [];
      syntax_only = false
    }
let sigmap: env -> (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap =
  fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____622  ->
         match uu____622 with
         | (m,uu____626) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___179_634 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___179_634.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___180_635 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___180_635.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___180_635.FStar_Syntax_Syntax.sort)
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
        (fun uu____681  ->
           match uu____681 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____695 =
                   let uu____696 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____696 dd dq in
                 Some uu____695
               else None) in
    match t with | Some v1 -> Some (v1, false) | None  -> None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____726 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____750 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____761 -> false
let option_of_cont k_ignore uu___146_780 =
  match uu___146_780 with
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
        (fun uu____825  ->
           match uu____825 with
           | (f,uu____830) ->
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
  fun uu___147_866  ->
    match uu___147_866 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___148_915 =
    match uu___148_915 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
          let uu____923 = get_exported_id_set env mname in
          match uu____923 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____939 = mex eikind in FStar_ST.read uu____939 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____946 = FStar_Util.smap_try_find env.includes mname in
          match uu____946 with
          | None  -> []
          | Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
          then let uu____966 = qual modul id in find_in_module uu____966
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____969 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___149_973  ->
    match uu___149_973 with | Exported_id_field  -> true | uu____974 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___150_1063 =
    match uu___150_1063 with
    | (id',uu____1065,uu____1066) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___151_1070 =
    match uu___151_1070 with
    | (id',uu____1072,uu____1073) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1076 = current_module env in FStar_Ident.ids_of_lid uu____1076 in
  let proc uu___152_1081 =
    match uu___152_1081 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____1086) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____1089 = FStar_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____1089 id
    | uu____1092 -> Cont_ignore in
  let rec aux uu___153_1098 =
    match uu___153_1098 with
    | a::q ->
        let uu____1104 = proc a in
        option_of_cont (fun uu____1106  -> aux q) uu____1104
    | [] ->
        let uu____1107 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____1109  -> None) uu____1107 in
  aux env.scope_mods
let found_local_binding r uu____1128 =
  match uu____1128 with
  | (id',x,mut) -> let uu____1135 = bv_to_name x r in (uu____1135, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____1172 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____1172 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found
let try_lookup_id:
  env -> FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) option =
  fun env  ->
    fun id  ->
      let uu____1194 = unmangleOpName id in
      match uu____1194 with
      | Some f -> Some f
      | uu____1208 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1215 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1215) (fun uu____1220  -> Cont_fail)
            (fun uu____1223  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1230  -> fun uu____1231  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1238  -> fun uu____1239  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1291 ->
        let lid = qualify env id in
        let uu____1293 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____1293 with
         | Some r -> let uu____1306 = k_global_def lid r in Some uu____1306
         | None  -> None)
    | None  -> None in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1319 = current_module env in qual uu____1319 id in
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
           let uu____1328 = current_module env in
           FStar_Ident.lid_equals lid uu____1328)
        ||
        (FStar_List.existsb (fun x  -> FStar_Ident.lid_equals lid (fst x))
           env.modules)
let resolve_module_name:
  env -> FStar_Ident.lident -> Prims.bool -> FStar_Ident.lident option =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
        let rec aux uu___154_1353 =
          match uu___154_1353 with
          | [] ->
              let uu____1356 = module_is_defined env lid in
              if uu____1356 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1363 =
                  let uu____1365 = FStar_Ident.path_of_lid ns in
                  let uu____1367 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1365 uu____1367 in
                FStar_Ident.lid_of_path uu____1363
                  (FStar_Ident.range_of_lid lid) in
              let uu____1369 = module_is_defined env new_lid in
              if uu____1369 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1374 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1380::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____1392 =
          let uu____1393 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____1393 in
        if uu____1392
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Syntax_Const.prims_lid
           then ()
           else
             (let uu____1395 =
                let uu____1396 =
                  let uu____1399 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____1399, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____1396 in
              raise uu____1395))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____1407 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____1410 = resolve_module_name env modul_orig true in
          (match uu____1410 with
           | Some modul_res -> fail_if_curmodule env modul_orig modul_res
           | uu____1413 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___155_1421  ->
           match uu___155_1421 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1423 -> false) env.scope_mods
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
                 let uu____1478 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____1478
                   (FStar_Util.map_option
                      (fun uu____1502  ->
                         match uu____1502 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____1519 =
          is_full_path &&
            (let uu____1520 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____1520) in
        if uu____1519
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1537 = aux ns_rev_prefix ns_last_id in
               (match uu____1537 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____1571 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____1571 with
      | (uu____1576,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1667::uu____1668 ->
      let uu____1670 =
        let uu____1672 =
          let uu____1673 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____1673 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____1672 true in
      (match uu____1670 with
       | None  -> None
       | Some modul ->
           let uu____1676 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____1678  -> None) uu____1676)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___156_1693 =
  match uu___156_1693 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1772 = k_global_def lid1 def in cont_of_option k uu____1772 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1793 = k_local_binding l in
       cont_of_option Cont_fail uu____1793)
    (fun r  ->
       let uu____1796 = k_rec_binding r in
       cont_of_option Cont_fail uu____1796) (fun uu____1798  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1804,uu____1805,uu____1806,l,uu____1808,uu____1809) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___157_1814  ->
               match uu___157_1814 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1816,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1823 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____1827,uu____1828,uu____1829)
        -> None
    | uu____1830 -> None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1839 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____1843 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____1843 then Some fv else None) in
      FStar_All.pipe_right uu____1839 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1861 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____1861 ns)
let try_lookup_name:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> foundname option =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___161_1886 =
            match uu___161_1886 with
            | (uu____1890,true ) when exclude_interf -> None
            | (se,uu____1892) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1894 ->
                     let uu____1903 =
                       let uu____1904 =
                         let uu____1907 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____1907, false) in
                       Term_name uu____1904 in
                     Some uu____1903
                 | FStar_Syntax_Syntax.Sig_datacon uu____1908 ->
                     let uu____1916 =
                       let uu____1917 =
                         let uu____1920 =
                           let uu____1921 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1921 in
                         (uu____1920, false) in
                       Term_name uu____1917 in
                     Some uu____1916
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1923,lbs),uu____1925,uu____1926) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____1937 =
                       let uu____1938 =
                         let uu____1941 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____1941, false) in
                       Term_name uu____1938 in
                     Some uu____1937
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1943,uu____1944) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____1947 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___158_1949  ->
                                  match uu___158_1949 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1950 -> false))) in
                     if uu____1947
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____1954 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___159_1956  ->
                                         match uu___159_1956 with
                                         | FStar_Syntax_Syntax.Projector
                                             uu____1957 -> true
                                         | FStar_Syntax_Syntax.Discriminator
                                             uu____1960 -> true
                                         | uu____1961 -> false)))) in
                         if uu____1954
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____1963 =
                         FStar_Util.find_map quals
                           (fun uu___160_1965  ->
                              match uu___160_1965 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1968 -> None) in
                       (match uu____1963 with
                        | Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
                        | uu____1980 ->
                            let uu____1982 =
                              let uu____1983 =
                                let uu____1986 =
                                  let uu____1987 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____1987 in
                                (uu____1986, false) in
                              Term_name uu____1983 in
                            Some uu____1982)
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
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1992 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1999 -> None) in
          let k_local_binding r =
            let uu____2011 =
              let uu____2012 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____2012 in
            Some uu____2011 in
          let k_rec_binding uu____2022 =
            match uu____2022 with
            | (id,l,dd) ->
                let uu____2030 =
                  let uu____2031 =
                    let uu____2034 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____2034, false) in
                  Term_name uu____2031 in
                Some uu____2030 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2038 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2038 with
                 | Some f -> Some (Term_name f)
                 | uu____2048 -> None)
            | uu____2052 -> None in
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
        let uu____2072 = try_lookup_name true exclude_interf env lid in
        match uu____2072 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____2081 -> None
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2092 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2092 with | Some (o,l1) -> Some l1 | uu____2101 -> None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list) option
  =
  fun env  ->
    fun l  ->
      let uu____2115 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2115 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2124;
             FStar_Syntax_Syntax.sigquals = uu____2125;
             FStar_Syntax_Syntax.sigmeta = uu____2126;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2136;
             FStar_Syntax_Syntax.sigquals = uu____2137;
             FStar_Syntax_Syntax.sigmeta = uu____2138;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____2147,uu____2148,uu____2149,uu____2150,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2152;
             FStar_Syntax_Syntax.sigquals = uu____2153;
             FStar_Syntax_Syntax.sigmeta = uu____2154;_},l1)
          -> Some (l1, cattributes)
      | uu____2165 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl option =
  fun env  ->
    fun l  ->
      let uu____2179 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2179 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2185;
             FStar_Syntax_Syntax.sigquals = uu____2186;
             FStar_Syntax_Syntax.sigmeta = uu____2187;_},uu____2188)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2193;
             FStar_Syntax_Syntax.sigquals = uu____2194;
             FStar_Syntax_Syntax.sigmeta = uu____2195;_},uu____2196)
          -> Some ne
      | uu____2200 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2210 = try_lookup_effect_name env lid in
      match uu____2210 with | None  -> false | Some uu____2212 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2220 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2220 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____2226,uu____2227,uu____2228,uu____2229);
             FStar_Syntax_Syntax.sigrng = uu____2230;
             FStar_Syntax_Syntax.sigquals = uu____2231;
             FStar_Syntax_Syntax.sigmeta = uu____2232;_},uu____2233)
          ->
          let rec aux new_name =
            let uu____2244 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2244 with
            | None  -> None
            | Some (s,uu____2254) ->
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
                     (uu____2260,uu____2261,uu____2262,cmp,uu____2264) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2268 -> None) in
          aux l'
      | Some (uu____2269,l') -> Some l'
      | uu____2273 -> None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___162_2294 =
        match uu___162_2294 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2299,uu____2300,uu____2301);
             FStar_Syntax_Syntax.sigrng = uu____2302;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2304;_},uu____2305)
            -> Some quals
        | uu____2308 -> None in
      let uu____2312 =
        resolve_in_open_namespaces' env lid (fun uu____2316  -> None)
          (fun uu____2318  -> None) k_global_def in
      match uu____2312 with | Some quals -> quals | uu____2324 -> []
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul option =
  fun env  ->
    fun path  ->
      let uu____2336 =
        FStar_List.tryFind
          (fun uu____2342  ->
             match uu____2342 with
             | (mlid,modul) ->
                 let uu____2347 = FStar_Ident.path_of_lid mlid in
                 uu____2347 = path) env.modules in
      match uu____2336 with
      | Some (uu____2351,modul) -> Some modul
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___163_2373 =
        match uu___163_2373 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2377,lbs),uu____2379,uu____2380);
             FStar_Syntax_Syntax.sigrng = uu____2381;
             FStar_Syntax_Syntax.sigquals = uu____2382;
             FStar_Syntax_Syntax.sigmeta = uu____2383;_},uu____2384)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2396 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2396
        | uu____2397 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2400  -> None)
        (fun uu____2401  -> None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___164_2420 =
        match uu___164_2420 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2427,uu____2428);
             FStar_Syntax_Syntax.sigrng = uu____2429;
             FStar_Syntax_Syntax.sigquals = uu____2430;
             FStar_Syntax_Syntax.sigmeta = uu____2431;_},uu____2432)
            ->
            FStar_Util.find_map (snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2448 -> None)
        | uu____2453 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2460  -> None)
        (fun uu____2463  -> None) k_global_def
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
          let uu____2490 = try_lookup_name any_val exclude_interf env lid in
          match uu____2490 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2499 -> None
let try_lookup_lid:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2519 = try_lookup_lid env l in
      match uu____2519 with
      | None  -> None
      | Some (e,uu____2527) ->
          let uu____2530 =
            let uu____2531 = FStar_Syntax_Subst.compress e in
            uu____2531.FStar_Syntax_Syntax.n in
          (match uu____2530 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2540 -> None)
let try_lookup_lid_no_resolve:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___181_2551 = env in
        {
          curmodule = (uu___181_2551.curmodule);
          curmonad = (uu___181_2551.curmonad);
          modules = (uu___181_2551.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___181_2551.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___181_2551.sigaccum);
          sigmap = (uu___181_2551.sigmap);
          iface = (uu___181_2551.iface);
          admitted_iface = (uu___181_2551.admitted_iface);
          expect_typ = (uu___181_2551.expect_typ);
          docs = (uu___181_2551.docs);
          remaining_iface_decls = (uu___181_2551.remaining_iface_decls);
          syntax_only = (uu___181_2551.syntax_only)
        } in
      try_lookup_lid env' l
let try_lookup_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___166_2575 =
        match uu___166_2575 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2579,uu____2580,uu____2581);
             FStar_Syntax_Syntax.sigrng = uu____2582;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2584;_},uu____2585)
            ->
            let uu____2587 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___165_2589  ->
                      match uu___165_2589 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2590 -> false)) in
            if uu____2587
            then
              let uu____2592 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2592
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2594;
             FStar_Syntax_Syntax.sigrng = uu____2595;
             FStar_Syntax_Syntax.sigquals = uu____2596;
             FStar_Syntax_Syntax.sigmeta = uu____2597;_},uu____2598)
            ->
            let uu____2607 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2607
        | uu____2608 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2611  -> None)
        (fun uu____2612  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___167_2631 =
        match uu___167_2631 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2636,uu____2637,uu____2638,uu____2639,datas,uu____2641);
             FStar_Syntax_Syntax.sigrng = uu____2642;
             FStar_Syntax_Syntax.sigquals = uu____2643;
             FStar_Syntax_Syntax.sigmeta = uu____2644;_},uu____2645)
            -> Some datas
        | uu____2652 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2657  -> None)
        (fun uu____2659  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____2693 =
    let uu____2694 =
      let uu____2697 =
        let uu____2699 = FStar_ST.read record_cache in
        FStar_List.hd uu____2699 in
      let uu____2707 = FStar_ST.read record_cache in uu____2697 :: uu____2707 in
    FStar_ST.write record_cache uu____2694 in
  let pop1 uu____2722 =
    let uu____2723 =
      let uu____2726 = FStar_ST.read record_cache in FStar_List.tl uu____2726 in
    FStar_ST.write record_cache uu____2723 in
  let peek uu____2742 =
    let uu____2743 = FStar_ST.read record_cache in FStar_List.hd uu____2743 in
  let insert r =
    let uu____2755 =
      let uu____2758 = let uu____2760 = peek () in r :: uu____2760 in
      let uu____2762 =
        let uu____2765 = FStar_ST.read record_cache in
        FStar_List.tl uu____2765 in
      uu____2758 :: uu____2762 in
    FStar_ST.write record_cache uu____2755 in
  let commit1 uu____2781 =
    let uu____2782 = FStar_ST.read record_cache in
    match uu____2782 with
    | hd1::uu____2790::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2803 -> failwith "Impossible" in
  let filter1 uu____2809 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____2816 =
           let uu____2819 = FStar_ST.read record_cache in filtered ::
             uu____2819 in
         FStar_ST.write record_cache uu____2816) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____2893 = record_cache_aux_with_filter in
  match uu____2893 with | (aux,uu____2931) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____2970 = record_cache_aux_with_filter in
  match uu____2970 with | (uu____2993,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____3033 = record_cache_aux in
  match uu____3033 with
  | (push1,uu____3053,uu____3054,uu____3055,uu____3056) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3081 = record_cache_aux in
  match uu____3081 with
  | (uu____3100,pop1,uu____3102,uu____3103,uu____3104) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____3130 = record_cache_aux in
  match uu____3130 with
  | (uu____3150,uu____3151,peek,uu____3153,uu____3154) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____3179 = record_cache_aux in
  match uu____3179 with
  | (uu____3198,uu____3199,uu____3200,insert,uu____3202) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____3227 = record_cache_aux in
  match uu____3227 with
  | (uu____3246,uu____3247,uu____3248,uu____3249,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3289) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___168_3298  ->
                   match uu___168_3298 with
                   | FStar_Syntax_Syntax.RecordType uu____3299 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____3304 -> true
                   | uu____3309 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___169_3317  ->
                      match uu___169_3317 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3319,uu____3320,uu____3321,uu____3322,uu____3323);
                          FStar_Syntax_Syntax.sigrng = uu____3324;
                          FStar_Syntax_Syntax.sigquals = uu____3325;
                          FStar_Syntax_Syntax.sigmeta = uu____3326;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3330 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___170_3332  ->
                    match uu___170_3332 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____3336,uu____3337,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____3339;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____3341;_} ->
                        let uu____3346 =
                          let uu____3347 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3347 in
                        (match uu____3346 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3351,t,uu____3353,uu____3354,uu____3355);
                             FStar_Syntax_Syntax.sigrng = uu____3356;
                             FStar_Syntax_Syntax.sigquals = uu____3357;
                             FStar_Syntax_Syntax.sigmeta = uu____3358;_} ->
                             let uu____3362 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3362 with
                              | (formals,uu____3371) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3397  ->
                                            match uu____3397 with
                                            | (x,q) ->
                                                let uu____3405 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3405
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3436  ->
                                            match uu____3436 with
                                            | (x,q) ->
                                                let uu____3445 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____3445,
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
                                  ((let uu____3457 =
                                      let uu____3459 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3459 in
                                    FStar_ST.write new_globs uu____3457);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3475 =
                                            match uu____3475 with
                                            | (id,uu____3481) ->
                                                let modul =
                                                  let uu____3487 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3487.FStar_Ident.str in
                                                let uu____3488 =
                                                  get_exported_id_set e modul in
                                                (match uu____3488 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____3504 =
                                                         let uu____3505 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3505 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3504);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3512 =
                                                               let uu____3513
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____3513.FStar_Ident.ident in
                                                             uu____3512.FStar_Ident.idText in
                                                           let uu____3515 =
                                                             let uu____3516 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3516 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3515))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3529 -> ())
                    | uu____3530 -> ()))
        | uu____3531 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3544 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3544 with
        | (ns,id) ->
            let uu____3554 = peek_record_cache () in
            FStar_Util.find_map uu____3554
              (fun record  ->
                 let uu____3557 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3560  -> None) uu____3557) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3561  -> Cont_ignore) (fun uu____3562  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3565 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3565)
        (fun k  -> fun uu____3568  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let uu____3577 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3577 with
      | Some r when r.is_record -> Some r
      | uu____3581 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3592 = try_lookup_record_by_field_name env lid in
        match uu____3592 with
        | Some record' when
            let uu____3595 =
              let uu____3596 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3596 in
            let uu____3598 =
              let uu____3599 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3599 in
            uu____3595 = uu____3598 ->
            let uu____3601 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3603  -> Cont_ok ()) in
            (match uu____3601 with
             | Cont_ok uu____3604 -> true
             | uu____3605 -> false)
        | uu____3607 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) option =
  fun env  ->
    fun fieldname  ->
      let uu____3618 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3618 with
      | Some r ->
          let uu____3624 =
            let uu____3627 =
              let uu____3628 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3628
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3627, (r.is_record)) in
          Some uu____3624
      | uu____3631 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3640  ->
    let uu____3641 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3641
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3652  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___171_3661  ->
      match uu___171_3661 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___172_3681 =
            match uu___172_3681 with
            | Rec_binding uu____3682 -> true
            | uu____3683 -> false in
          let this_env =
            let uu___182_3685 = env in
            let uu____3686 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___182_3685.curmodule);
              curmonad = (uu___182_3685.curmonad);
              modules = (uu___182_3685.modules);
              scope_mods = uu____3686;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___182_3685.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___182_3685.sigaccum);
              sigmap = (uu___182_3685.sigmap);
              iface = (uu___182_3685.iface);
              admitted_iface = (uu___182_3685.admitted_iface);
              expect_typ = (uu___182_3685.expect_typ);
              docs = (uu___182_3685.docs);
              remaining_iface_decls = (uu___182_3685.remaining_iface_decls);
              syntax_only = (uu___182_3685.syntax_only)
            } in
          let uu____3688 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3688 with | None  -> true | Some uu____3694 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___183_3705 = env in
      {
        curmodule = (uu___183_3705.curmodule);
        curmonad = (uu___183_3705.curmonad);
        modules = (uu___183_3705.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___183_3705.exported_ids);
        trans_exported_ids = (uu___183_3705.trans_exported_ids);
        includes = (uu___183_3705.includes);
        sigaccum = (uu___183_3705.sigaccum);
        sigmap = (uu___183_3705.sigmap);
        iface = (uu___183_3705.iface);
        admitted_iface = (uu___183_3705.admitted_iface);
        expect_typ = (uu___183_3705.expect_typ);
        docs = (uu___183_3705.docs);
        remaining_iface_decls = (uu___183_3705.remaining_iface_decls);
        syntax_only = (uu___183_3705.syntax_only)
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
        let uu____3744 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____3744
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
          | Some (se,uu____3764) ->
              let uu____3767 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____3767 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____3772 =
          let uu____3773 =
            let uu____3776 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____3776, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____3773 in
        raise uu____3772 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____3783 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3788 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3794 -> (true, true)
          | uu____3799 -> (false, false) in
        match uu____3783 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____3804 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3807 =
                     let uu____3808 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____3808 in
                   if uu____3807 then Some l else None) in
            (match uu____3804 with
             | Some l when
                 let uu____3812 = FStar_Options.interactive () in
                 Prims.op_Negation uu____3812 -> err1 l
             | uu____3813 ->
                 (extract_record env globals s;
                  (let uu___184_3818 = env in
                   {
                     curmodule = (uu___184_3818.curmodule);
                     curmonad = (uu___184_3818.curmonad);
                     modules = (uu___184_3818.modules);
                     scope_mods = (uu___184_3818.scope_mods);
                     exported_ids = (uu___184_3818.exported_ids);
                     trans_exported_ids = (uu___184_3818.trans_exported_ids);
                     includes = (uu___184_3818.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___184_3818.sigmap);
                     iface = (uu___184_3818.iface);
                     admitted_iface = (uu___184_3818.admitted_iface);
                     expect_typ = (uu___184_3818.expect_typ);
                     docs = (uu___184_3818.docs);
                     remaining_iface_decls =
                       (uu___184_3818.remaining_iface_decls);
                     syntax_only = (uu___184_3818.syntax_only)
                   }))) in
      let env2 =
        let uu___185_3820 = env1 in
        let uu____3821 = FStar_ST.read globals in
        {
          curmodule = (uu___185_3820.curmodule);
          curmonad = (uu___185_3820.curmonad);
          modules = (uu___185_3820.modules);
          scope_mods = uu____3821;
          exported_ids = (uu___185_3820.exported_ids);
          trans_exported_ids = (uu___185_3820.trans_exported_ids);
          includes = (uu___185_3820.includes);
          sigaccum = (uu___185_3820.sigaccum);
          sigmap = (uu___185_3820.sigmap);
          iface = (uu___185_3820.iface);
          admitted_iface = (uu___185_3820.admitted_iface);
          expect_typ = (uu___185_3820.expect_typ);
          docs = (uu___185_3820.docs);
          remaining_iface_decls = (uu___185_3820.remaining_iface_decls);
          syntax_only = (uu___185_3820.syntax_only)
        } in
      let uu____3826 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3840) ->
            let uu____3845 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____3845)
        | uu____3859 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____3826 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3889  ->
                   match uu____3889 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3900 =
                                  let uu____3902 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3902 in
                                FStar_ST.write globals uu____3900);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3911 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____3911.FStar_Ident.str in
                                    ((let uu____3913 =
                                        get_exported_id_set env3 modul in
                                      match uu____3913 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____3928 =
                                            let uu____3929 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3929 in
                                          FStar_ST.write my_exported_ids
                                            uu____3928
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
              let uu___186_3941 = env3 in
              let uu____3942 = FStar_ST.read globals in
              {
                curmodule = (uu___186_3941.curmodule);
                curmonad = (uu___186_3941.curmonad);
                modules = (uu___186_3941.modules);
                scope_mods = uu____3942;
                exported_ids = (uu___186_3941.exported_ids);
                trans_exported_ids = (uu___186_3941.trans_exported_ids);
                includes = (uu___186_3941.includes);
                sigaccum = (uu___186_3941.sigaccum);
                sigmap = (uu___186_3941.sigmap);
                iface = (uu___186_3941.iface);
                admitted_iface = (uu___186_3941.admitted_iface);
                expect_typ = (uu___186_3941.expect_typ);
                docs = (uu___186_3941.docs);
                remaining_iface_decls = (uu___186_3941.remaining_iface_decls);
                syntax_only = (uu___186_3941.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3953 =
        let uu____3956 = resolve_module_name env ns false in
        match uu____3956 with
        | None  ->
            let modules = env.modules in
            let uu____3964 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3970  ->
                      match uu____3970 with
                      | (m,uu____3974) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____3964
            then (ns, Open_namespace)
            else
              (let uu____3978 =
                 let uu____3979 =
                   let uu____3982 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____3982, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____3979 in
               raise uu____3978)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____3953 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____3996 = resolve_module_name env ns false in
      match uu____3996 with
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____4002 = current_module env1 in
              uu____4002.FStar_Ident.str in
            (let uu____4004 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____4004 with
             | None  -> ()
             | Some incl ->
                 let uu____4017 =
                   let uu____4019 = FStar_ST.read incl in ns1 :: uu____4019 in
                 FStar_ST.write incl uu____4017);
            (match () with
             | () ->
                 let uu____4027 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____4027 with
                  | Some ns_trans_exports ->
                      ((let uu____4040 =
                          let uu____4051 = get_exported_id_set env1 curmod in
                          let uu____4056 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____4051, uu____4056) in
                        match uu____4040 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____4096 = ns_trans_exports k in
                                FStar_ST.read uu____4096 in
                              let ex = cur_exports k in
                              (let uu____4105 =
                                 let uu____4106 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____4106 ns_ex in
                               FStar_ST.write ex uu____4105);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____4116 =
                                     let uu____4117 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____4117 ns_ex in
                                   FStar_ST.write trans_ex uu____4116) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____4123 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____4137 =
                        let uu____4138 =
                          let uu____4141 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____4141, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____4138 in
                      raise uu____4137))))
      | uu____4142 ->
          let uu____4144 =
            let uu____4145 =
              let uu____4148 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____4148, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____4145 in
          raise uu____4144
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____4158 = module_is_defined env l in
        if uu____4158
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____4161 =
             let uu____4162 =
               let uu____4165 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____4165, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____4162 in
           raise uu____4161)
let push_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____4179 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____4179 with
              | None  -> ()
              | Some old_doc ->
                  let uu____4182 =
                    let uu____4183 = FStar_Ident.string_of_lid l in
                    let uu____4184 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____4185 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____4183 uu____4184 uu____4185 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____4182);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____4194 = try_lookup_lid env l in
                (match uu____4194 with
                 | None  ->
                     ((let uu____4201 =
                         let uu____4202 = FStar_Options.interactive () in
                         Prims.op_Negation uu____4202 in
                       if uu____4201
                       then
                         let uu____4203 =
                           let uu____4204 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____4205 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____4204 uu____4205 in
                         FStar_Util.print_string uu____4203
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___187_4211 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___187_4211.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___187_4211.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___187_4211.FStar_Syntax_Syntax.sigmeta)
                           }), false)))
                 | Some uu____4212 -> ())
            | uu____4217 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4229) ->
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
                                (lid,uu____4237,uu____4238,uu____4239,uu____4240,uu____4241)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4246 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4249,uu____4250) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4254,lbs),uu____4256,uu____4257) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4270 =
                               let uu____4271 =
                                 let uu____4272 =
                                   let uu____4277 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4277.FStar_Syntax_Syntax.fv_name in
                                 uu____4272.FStar_Syntax_Syntax.v in
                               uu____4271.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4270))
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
                               let uu____4287 =
                                 let uu____4292 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4292.FStar_Syntax_Syntax.fv_name in
                               uu____4287.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___188_4299 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___188_4299.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___188_4299.FStar_Syntax_Syntax.sigmeta)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4306 -> ()));
      (let curmod =
         let uu____4308 = current_module env in uu____4308.FStar_Ident.str in
       (let uu____4310 =
          let uu____4321 = get_exported_id_set env curmod in
          let uu____4326 = get_trans_exported_id_set env curmod in
          (uu____4321, uu____4326) in
        match uu____4310 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4366 = cur_ex eikind in FStar_ST.read uu____4366 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4374 =
                let uu____4375 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4375 in
              FStar_ST.write cur_trans_ex_set_ref uu____4374 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4381 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___189_4393 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___189_4393.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___189_4393.exported_ids);
                    trans_exported_ids = (uu___189_4393.trans_exported_ids);
                    includes = (uu___189_4393.includes);
                    sigaccum = [];
                    sigmap = (uu___189_4393.sigmap);
                    iface = (uu___189_4393.iface);
                    admitted_iface = (uu___189_4393.admitted_iface);
                    expect_typ = (uu___189_4393.expect_typ);
                    docs = (uu___189_4393.docs);
                    remaining_iface_decls =
                      (uu___189_4393.remaining_iface_decls);
                    syntax_only = (uu___189_4393.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4406 =
       let uu____4408 = FStar_ST.read stack in env :: uu____4408 in
     FStar_ST.write stack uu____4406);
    (let uu___190_4416 = env in
     let uu____4417 = FStar_Util.smap_copy (sigmap env) in
     let uu____4423 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___190_4416.curmodule);
       curmonad = (uu___190_4416.curmonad);
       modules = (uu___190_4416.modules);
       scope_mods = (uu___190_4416.scope_mods);
       exported_ids = (uu___190_4416.exported_ids);
       trans_exported_ids = (uu___190_4416.trans_exported_ids);
       includes = (uu___190_4416.includes);
       sigaccum = (uu___190_4416.sigaccum);
       sigmap = uu____4417;
       iface = (uu___190_4416.iface);
       admitted_iface = (uu___190_4416.admitted_iface);
       expect_typ = (uu___190_4416.expect_typ);
       docs = uu____4423;
       remaining_iface_decls = (uu___190_4416.remaining_iface_decls);
       syntax_only = (uu___190_4416.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____4427  ->
    let uu____4428 = FStar_ST.read stack in
    match uu____4428 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4441 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4447 = FStar_ST.read stack in
     match uu____4447 with
     | uu____4452::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4459 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4466  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4478 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4480 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4498 = FStar_Util.smap_try_find sm' k in
              match uu____4498 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___191_4514 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___191_4514.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___191_4514.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___191_4514.FStar_Syntax_Syntax.sigmeta)
                          }
                      | uu____4515 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4518 -> ()));
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
                  FStar_Ident.lid_equals mname
                    FStar_Parser_Const.pervasives_lid
                then [FStar_Parser_Const.prims_lid]
                else
                  [FStar_Parser_Const.prims_lid;
                  FStar_Parser_Const.pervasives_lid;
                  FStar_Parser_Const.fstar_ns_lid] in
            let open_ns1 =
              if
                (FStar_List.length mname.FStar_Ident.ns) <>
                  (Prims.parse_int "0")
              then
                let ns = FStar_Ident.lid_of_ids mname.FStar_Ident.ns in ns ::
                  open_ns
              else open_ns in
            (let uu____4564 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4564);
            (match () with
             | () ->
                 ((let uu____4569 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4569);
                  (match () with
                   | () ->
                       ((let uu____4574 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4574);
                        (match () with
                         | () ->
                             let uu___192_4583 = env1 in
                             let uu____4584 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___192_4583.curmonad);
                               modules = (uu___192_4583.modules);
                               scope_mods = uu____4584;
                               exported_ids = (uu___192_4583.exported_ids);
                               trans_exported_ids =
                                 (uu___192_4583.trans_exported_ids);
                               includes = (uu___192_4583.includes);
                               sigaccum = (uu___192_4583.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___192_4583.expect_typ);
                               docs = (uu___192_4583.docs);
                               remaining_iface_decls =
                                 (uu___192_4583.remaining_iface_decls);
                               syntax_only = (uu___192_4583.syntax_only)
                             }))))) in
          let uu____4587 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4599  ->
                    match uu____4599 with
                    | (l,uu____4603) -> FStar_Ident.lid_equals l mname)) in
          match uu____4587 with
          | None  -> let uu____4608 = prep env in (uu____4608, false)
          | Some (uu____4609,m) ->
              ((let uu____4614 =
                  (let uu____4615 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4615) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4614
                then
                  let uu____4616 =
                    let uu____4617 =
                      let uu____4620 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4620, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4617 in
                  raise uu____4616
                else ());
               (let uu____4622 = let uu____4623 = push env in prep uu____4623 in
                (uu____4622, true)))
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
          let uu___193_4631 = env in
          {
            curmodule = (uu___193_4631.curmodule);
            curmonad = (Some mname);
            modules = (uu___193_4631.modules);
            scope_mods = (uu___193_4631.scope_mods);
            exported_ids = (uu___193_4631.exported_ids);
            trans_exported_ids = (uu___193_4631.trans_exported_ids);
            includes = (uu___193_4631.includes);
            sigaccum = (uu___193_4631.sigaccum);
            sigmap = (uu___193_4631.sigmap);
            iface = (uu___193_4631.iface);
            admitted_iface = (uu___193_4631.admitted_iface);
            expect_typ = (uu___193_4631.expect_typ);
            docs = (uu___193_4631.docs);
            remaining_iface_decls = (uu___193_4631.remaining_iface_decls);
            syntax_only = (uu___193_4631.syntax_only)
          }
let fail_or env lookup lid =
  let uu____4656 = lookup lid in
  match uu____4656 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4662  ->
             match uu____4662 with
             | (lid1,uu____4666) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4675 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4675
               (FStar_Ident.range_of_lid lid) in
           let uu____4676 = resolve_module_name env modul true in
           match uu____4676 with
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
  let uu____4703 = lookup id in
  match uu____4703 with
  | None  ->
      raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r