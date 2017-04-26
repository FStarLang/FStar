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
  curmodule: FStar_Ident.lident Prims.option;
  curmonad: FStar_Ident.ident Prims.option;
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
      let uu___174_390 = env in
      {
        curmodule = (uu___174_390.curmodule);
        curmonad = (uu___174_390.curmonad);
        modules = (uu___174_390.modules);
        scope_mods = (uu___174_390.scope_mods);
        exported_ids = (uu___174_390.exported_ids);
        trans_exported_ids = (uu___174_390.trans_exported_ids);
        includes = (uu___174_390.includes);
        sigaccum = (uu___174_390.sigaccum);
        sigmap = (uu___174_390.sigmap);
        iface = b;
        admitted_iface = (uu___174_390.admitted_iface);
        expect_typ = (uu___174_390.expect_typ);
        docs = (uu___174_390.docs);
        remaining_iface_decls = (uu___174_390.remaining_iface_decls);
        syntax_only = (uu___174_390.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___175_400 = e in
      {
        curmodule = (uu___175_400.curmodule);
        curmonad = (uu___175_400.curmonad);
        modules = (uu___175_400.modules);
        scope_mods = (uu___175_400.scope_mods);
        exported_ids = (uu___175_400.exported_ids);
        trans_exported_ids = (uu___175_400.trans_exported_ids);
        includes = (uu___175_400.includes);
        sigaccum = (uu___175_400.sigaccum);
        sigmap = (uu___175_400.sigmap);
        iface = (uu___175_400.iface);
        admitted_iface = b;
        expect_typ = (uu___175_400.expect_typ);
        docs = (uu___175_400.docs);
        remaining_iface_decls = (uu___175_400.remaining_iface_decls);
        syntax_only = (uu___175_400.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___176_410 = e in
      {
        curmodule = (uu___176_410.curmodule);
        curmonad = (uu___176_410.curmonad);
        modules = (uu___176_410.modules);
        scope_mods = (uu___176_410.scope_mods);
        exported_ids = (uu___176_410.exported_ids);
        trans_exported_ids = (uu___176_410.trans_exported_ids);
        includes = (uu___176_410.includes);
        sigaccum = (uu___176_410.sigaccum);
        sigmap = (uu___176_410.sigmap);
        iface = (uu___176_410.iface);
        admitted_iface = (uu___176_410.admitted_iface);
        expect_typ = b;
        docs = (uu___176_410.docs);
        remaining_iface_decls = (uu___176_410.remaining_iface_decls);
        syntax_only = (uu___176_410.syntax_only)
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
      let uu___177_446 = e in
      {
        curmodule = (Some l);
        curmonad = (uu___177_446.curmonad);
        modules = (uu___177_446.modules);
        scope_mods = (uu___177_446.scope_mods);
        exported_ids = (uu___177_446.exported_ids);
        trans_exported_ids = (uu___177_446.trans_exported_ids);
        includes = (uu___177_446.includes);
        sigaccum = (uu___177_446.sigaccum);
        sigmap = (uu___177_446.sigmap);
        iface = (uu___177_446.iface);
        admitted_iface = (uu___177_446.admitted_iface);
        expect_typ = (uu___177_446.expect_typ);
        docs = (uu___177_446.docs);
        remaining_iface_decls = (uu___177_446.remaining_iface_decls);
        syntax_only = (uu___177_446.syntax_only)
      }
let current_module: env -> FStar_Ident.lident =
  fun env  ->
    match env.curmodule with
    | None  -> failwith "Unset current module"
    | Some m -> m
let iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list Prims.option
  =
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
            let uu___178_548 = env in
            {
              curmodule = (uu___178_548.curmodule);
              curmonad = (uu___178_548.curmonad);
              modules = (uu___178_548.modules);
              scope_mods = (uu___178_548.scope_mods);
              exported_ids = (uu___178_548.exported_ids);
              trans_exported_ids = (uu___178_548.trans_exported_ids);
              includes = (uu___178_548.includes);
              sigaccum = (uu___178_548.sigaccum);
              sigmap = (uu___178_548.sigmap);
              iface = (uu___178_548.iface);
              admitted_iface = (uu___178_548.admitted_iface);
              expect_typ = (uu___178_548.expect_typ);
              docs = (uu___178_548.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___178_548.syntax_only)
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
      let uu___179_576 = env in
      {
        curmodule = (uu___179_576.curmodule);
        curmonad = (uu___179_576.curmonad);
        modules = (uu___179_576.modules);
        scope_mods = (uu___179_576.scope_mods);
        exported_ids = (uu___179_576.exported_ids);
        trans_exported_ids = (uu___179_576.trans_exported_ids);
        includes = (uu___179_576.includes);
        sigaccum = (uu___179_576.sigaccum);
        sigmap = (uu___179_576.sigmap);
        iface = (uu___179_576.iface);
        admitted_iface = (uu___179_576.admitted_iface);
        expect_typ = (uu___179_576.expect_typ);
        docs = (uu___179_576.docs);
        remaining_iface_decls = (uu___179_576.remaining_iface_decls);
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
             FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___180_634 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___180_634.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___181_635 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___181_635.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___181_635.FStar_Syntax_Syntax.sort)
      }
let bv_to_name:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r)
let unmangleMap:
  (Prims.string* Prims.string* FStar_Syntax_Syntax.delta_depth*
    FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None)]
let unmangleOpName:
  FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option =
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
let option_of_cont k_ignore uu___147_780 =
  match uu___147_780 with
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
let get_exported_id_set: env -> Prims.string -> exported_id_set Prims.option
  = fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname
let get_trans_exported_id_set:
  env -> Prims.string -> exported_id_set Prims.option =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname
let string_of_exported_id_kind: exported_id_kind -> Prims.string =
  fun uu___148_866  ->
    match uu___148_866 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___149_915 =
    match uu___149_915 with
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
  fun uu___150_973  ->
    match uu___150_973 with | Exported_id_field  -> true | uu____974 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___151_1063 =
    match uu___151_1063 with
    | (id',uu____1065,uu____1066) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___152_1070 =
    match uu___152_1070 with
    | (id',uu____1072,uu____1073) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1076 = current_module env in FStar_Ident.ids_of_lid uu____1076 in
  let proc uu___153_1081 =
    match uu___153_1081 with
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
  let rec aux uu___154_1098 =
    match uu___154_1098 with
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
  env ->
    FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  =
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
        (FStar_List.existsb
           (fun x  -> FStar_Ident.lid_equals lid (Prims.fst x)) env.modules)
let resolve_module_name:
  env -> FStar_Ident.lident -> Prims.bool -> FStar_Ident.lident Prims.option
  =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns in
        let rec aux uu___155_1352 =
          match uu___155_1352 with
          | [] ->
              let uu____1355 = module_is_defined env lid in
              if uu____1355 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1362 =
                  let uu____1364 = FStar_Ident.path_of_lid ns in
                  let uu____1366 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1364 uu____1366 in
                FStar_Ident.lid_of_path uu____1362
                  (FStar_Ident.range_of_lid lid) in
              let uu____1368 = module_is_defined env new_lid in
              if uu____1368 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1373 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1377::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____1389 =
          let uu____1390 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____1390 in
        if uu____1389
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Syntax_Const.prims_lid
           then ()
           else
             (let uu____1392 =
                let uu____1393 =
                  let uu____1396 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____1396, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____1393 in
              Prims.raise uu____1392))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____1404 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____1407 = resolve_module_name env modul_orig true in
          (match uu____1407 with
           | Some modul_res -> fail_if_curmodule env modul_orig modul_res
           | uu____1410 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___156_1418  ->
           match uu___156_1418 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1420 -> false) env.scope_mods
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
                 let uu____1475 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____1475
                   (FStar_Util.map_option
                      (fun uu____1499  ->
                         match uu____1499 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____1516 =
          is_full_path &&
            (let uu____1517 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____1517) in
        if uu____1516
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1534 = aux ns_rev_prefix ns_last_id in
               (match uu____1534 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let shorten_lid: env -> FStar_Ident.lid -> FStar_Ident.lid =
  fun env  ->
    fun lid  ->
      let uu____1568 = shorten_module_path env lid.FStar_Ident.ns true in
      match uu____1568 with
      | (uu____1573,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1664::uu____1665 ->
      let uu____1667 =
        let uu____1669 =
          let uu____1670 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____1670 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____1669 true in
      (match uu____1667 with
       | None  -> None
       | Some modul ->
           let uu____1673 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____1675  -> None) uu____1673)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___157_1690 =
  match uu___157_1690 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1769 = k_global_def lid1 def in cont_of_option k uu____1769 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1790 = k_local_binding l in
       cont_of_option Cont_fail uu____1790)
    (fun r  ->
       let uu____1793 = k_rec_binding r in
       cont_of_option Cont_fail uu____1793) (fun uu____1795  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual Prims.option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1801,uu____1802,uu____1803,l,uu____1805,uu____1806) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigqual
            (fun uu___158_1811  ->
               match uu___158_1811 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1813,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1820 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____1824,uu____1825,uu____1826)
        -> None
    | uu____1827 -> None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1836 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____1840 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____1840 then Some fv else None) in
      FStar_All.pipe_right uu____1836 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1854 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____1854 ns)
let try_lookup_name:
  Prims.bool ->
    Prims.bool -> env -> FStar_Ident.lident -> foundname Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___162_1879 =
            match uu___162_1879 with
            | (uu____1883,true ) when exclude_interf -> None
            | (se,uu____1885) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1887 ->
                     let uu____1896 =
                       let uu____1897 =
                         let uu____1900 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____1900, false) in
                       Term_name uu____1897 in
                     Some uu____1896
                 | FStar_Syntax_Syntax.Sig_datacon uu____1901 ->
                     let uu____1909 =
                       let uu____1910 =
                         let uu____1913 =
                           let uu____1914 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1914 in
                         (uu____1913, false) in
                       Term_name uu____1910 in
                     Some uu____1909
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1916,lbs),uu____1918,uu____1919) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____1930 =
                       let uu____1931 =
                         let uu____1934 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____1934, false) in
                       Term_name uu____1931 in
                     Some uu____1930
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1936,uu____1937) ->
                     let quals = se.FStar_Syntax_Syntax.sigqual in
                     let uu____1940 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___159_1942  ->
                                  match uu___159_1942 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1943 -> false))) in
                     if uu____1940
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____1947 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___160_1949  ->
                                         match uu___160_1949 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1952 -> false)))) in
                         if uu____1947
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____1954 =
                         FStar_Util.find_map quals
                           (fun uu___161_1956  ->
                              match uu___161_1956 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1959 -> None) in
                       (match uu____1954 with
                        | Some refl_monad ->
                            let refl_const =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reflect refl_monad)))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
                        | uu____1975 ->
                            let uu____1977 =
                              let uu____1978 =
                                let uu____1981 =
                                  let uu____1982 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____1982 in
                                (uu____1981, false) in
                              Term_name uu____1978 in
                            Some uu____1977)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1986 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1993 -> None) in
          let k_local_binding r =
            let uu____2005 =
              let uu____2006 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____2006 in
            Some uu____2005 in
          let k_rec_binding uu____2016 =
            match uu____2016 with
            | (id,l,dd) ->
                let uu____2024 =
                  let uu____2025 =
                    let uu____2028 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____2028, false) in
                  Term_name uu____2025 in
                Some uu____2024 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2032 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2032 with
                 | Some f -> Some (Term_name f)
                 | uu____2042 -> None)
            | uu____2046 -> None in
          match found_unmangled with
          | None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
let try_lookup_effect_name':
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident) Prims.option
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____2066 = try_lookup_name true exclude_interf env lid in
        match uu____2066 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____2075 -> None
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2086 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2086 with | Some (o,l1) -> Some l1 | uu____2095 -> None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list)
        Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____2109 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2109 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2118;
             FStar_Syntax_Syntax.sigqual = uu____2119;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2129;
             FStar_Syntax_Syntax.sigqual = uu____2130;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____2139,uu____2140,uu____2141,uu____2142,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2144;
             FStar_Syntax_Syntax.sigqual = uu____2145;_},l1)
          -> Some (l1, cattributes)
      | uu____2156 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      let uu____2170 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2170 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2176;
             FStar_Syntax_Syntax.sigqual = uu____2177;_},uu____2178)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2183;
             FStar_Syntax_Syntax.sigqual = uu____2184;_},uu____2185)
          -> Some ne
      | uu____2189 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2199 = try_lookup_effect_name env lid in
      match uu____2199 with | None  -> false | Some uu____2201 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2209 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2209 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____2215,uu____2216,uu____2217,uu____2218);
             FStar_Syntax_Syntax.sigrng = uu____2219;
             FStar_Syntax_Syntax.sigqual = uu____2220;_},uu____2221)
          ->
          let rec aux new_name =
            let uu____2232 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2232 with
            | None  -> None
            | Some (s,uu____2242) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____2247,uu____2248,uu____2249,cmp,uu____2251) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2255 -> None) in
          aux l'
      | Some (uu____2256,l') -> Some l'
      | uu____2260 -> None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___163_2281 =
        match uu___163_2281 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2286,uu____2287,uu____2288);
             FStar_Syntax_Syntax.sigrng = uu____2289;
             FStar_Syntax_Syntax.sigqual = quals;_},uu____2291)
            -> Some quals
        | uu____2294 -> None in
      let uu____2298 =
        resolve_in_open_namespaces' env lid (fun uu____2302  -> None)
          (fun uu____2304  -> None) k_global_def in
      match uu____2298 with | Some quals -> quals | uu____2310 -> []
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul Prims.option =
  fun env  ->
    fun path  ->
      let uu____2322 =
        FStar_List.tryFind
          (fun uu____2328  ->
             match uu____2328 with
             | (mlid,modul) ->
                 let uu____2333 = FStar_Ident.path_of_lid mlid in
                 uu____2333 = path) env.modules in
      match uu____2322 with
      | Some (uu____2337,modul) -> Some modul
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___164_2359 =
        match uu___164_2359 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2363,lbs),uu____2365,uu____2366);
             FStar_Syntax_Syntax.sigrng = uu____2367;
             FStar_Syntax_Syntax.sigqual = uu____2368;_},uu____2369)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2381 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2381
        | uu____2382 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2385  -> None)
        (fun uu____2386  -> None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___165_2405 =
        match uu___165_2405 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2412,uu____2413);
             FStar_Syntax_Syntax.sigrng = uu____2414;
             FStar_Syntax_Syntax.sigqual = uu____2415;_},uu____2416)
            ->
            FStar_Util.find_map (Prims.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2432 -> None)
        | uu____2437 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2444  -> None)
        (fun uu____2447  -> None) k_global_def
let empty_include_smap:
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = new_sigmap ()
let empty_exported_id_smap: exported_id_set FStar_Util.smap = new_sigmap ()
let try_lookup_lid':
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let uu____2474 = try_lookup_name any_val exclude_interf env lid in
          match uu____2474 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2483 -> None
let try_lookup_lid:
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2503 = try_lookup_lid env l in
      match uu____2503 with
      | None  -> None
      | Some (e,uu____2511) ->
          let uu____2514 =
            let uu____2515 = FStar_Syntax_Subst.compress e in
            uu____2515.FStar_Syntax_Syntax.n in
          (match uu____2514 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2524 -> None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___182_2535 = env in
        {
          curmodule = (uu___182_2535.curmodule);
          curmonad = (uu___182_2535.curmonad);
          modules = (uu___182_2535.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___182_2535.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___182_2535.sigaccum);
          sigmap = (uu___182_2535.sigmap);
          iface = (uu___182_2535.iface);
          admitted_iface = (uu___182_2535.admitted_iface);
          expect_typ = (uu___182_2535.expect_typ);
          docs = (uu___182_2535.docs);
          remaining_iface_decls = (uu___182_2535.remaining_iface_decls);
          syntax_only = (uu___182_2535.syntax_only)
        } in
      try_lookup_lid env' l
let try_lookup_doc:
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___167_2559 =
        match uu___167_2559 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2563,uu____2564,uu____2565);
             FStar_Syntax_Syntax.sigrng = uu____2566;
             FStar_Syntax_Syntax.sigqual = quals;_},uu____2568)
            ->
            let uu____2570 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___166_2572  ->
                      match uu___166_2572 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2573 -> false)) in
            if uu____2570
            then
              let uu____2575 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2575
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2577;
             FStar_Syntax_Syntax.sigrng = uu____2578;
             FStar_Syntax_Syntax.sigqual = uu____2579;_},uu____2580)
            ->
            let uu____2589 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2589
        | uu____2590 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2593  -> None)
        (fun uu____2594  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___168_2613 =
        match uu___168_2613 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2618,uu____2619,uu____2620,uu____2621,datas,uu____2623);
             FStar_Syntax_Syntax.sigrng = uu____2624;
             FStar_Syntax_Syntax.sigqual = uu____2625;_},uu____2626)
            -> Some datas
        | uu____2633 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2638  -> None)
        (fun uu____2640  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____2674 =
    let uu____2675 =
      let uu____2678 =
        let uu____2680 = FStar_ST.read record_cache in
        FStar_List.hd uu____2680 in
      let uu____2688 = FStar_ST.read record_cache in uu____2678 :: uu____2688 in
    FStar_ST.write record_cache uu____2675 in
  let pop1 uu____2703 =
    let uu____2704 =
      let uu____2707 = FStar_ST.read record_cache in FStar_List.tl uu____2707 in
    FStar_ST.write record_cache uu____2704 in
  let peek uu____2723 =
    let uu____2724 = FStar_ST.read record_cache in FStar_List.hd uu____2724 in
  let insert r =
    let uu____2736 =
      let uu____2739 = let uu____2741 = peek () in r :: uu____2741 in
      let uu____2743 =
        let uu____2746 = FStar_ST.read record_cache in
        FStar_List.tl uu____2746 in
      uu____2739 :: uu____2743 in
    FStar_ST.write record_cache uu____2736 in
  let commit1 uu____2762 =
    let uu____2763 = FStar_ST.read record_cache in
    match uu____2763 with
    | hd1::uu____2771::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2784 -> failwith "Impossible" in
  let filter1 uu____2790 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____2797 =
           let uu____2800 = FStar_ST.read record_cache in filtered ::
             uu____2800 in
         FStar_ST.write record_cache uu____2797) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____2874 = record_cache_aux_with_filter in
  match uu____2874 with | (aux,uu____2912) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____2951 = record_cache_aux_with_filter in
  match uu____2951 with | (uu____2974,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____3014 = record_cache_aux in
  match uu____3014 with
  | (push1,uu____3034,uu____3035,uu____3036,uu____3037) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3062 = record_cache_aux in
  match uu____3062 with
  | (uu____3081,pop1,uu____3083,uu____3084,uu____3085) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____3111 = record_cache_aux in
  match uu____3111 with
  | (uu____3131,uu____3132,peek,uu____3134,uu____3135) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____3160 = record_cache_aux in
  match uu____3160 with
  | (uu____3179,uu____3180,uu____3181,insert,uu____3183) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____3208 = record_cache_aux in
  match uu____3208 with
  | (uu____3227,uu____3228,uu____3229,uu____3230,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3270) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___169_3279  ->
                   match uu___169_3279 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____3282 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___170_3290  ->
                      match uu___170_3290 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3292,uu____3293,uu____3294,uu____3295,uu____3296);
                          FStar_Syntax_Syntax.sigrng = uu____3297;
                          FStar_Syntax_Syntax.sigqual = uu____3298;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3302 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___171_3304  ->
                    match uu___171_3304 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____3308,uu____3309,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____3311;
                        FStar_Syntax_Syntax.sigqual = typename_quals;_} ->
                        let uu____3317 =
                          let uu____3318 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3318 in
                        (match uu____3317 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3322,t,uu____3324,uu____3325,uu____3326);
                             FStar_Syntax_Syntax.sigrng = uu____3327;
                             FStar_Syntax_Syntax.sigqual = uu____3328;_} ->
                             let uu____3332 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3332 with
                              | (formals,uu____3341) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3367  ->
                                            match uu____3367 with
                                            | (x,q) ->
                                                let uu____3375 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3375
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3406  ->
                                            match uu____3406 with
                                            | (x,q) ->
                                                let uu____3415 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____3415,
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
                                  ((let uu____3427 =
                                      let uu____3429 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3429 in
                                    FStar_ST.write new_globs uu____3427);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3445 =
                                            match uu____3445 with
                                            | (id,uu____3451) ->
                                                let modul =
                                                  let uu____3457 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3457.FStar_Ident.str in
                                                let uu____3458 =
                                                  get_exported_id_set e modul in
                                                (match uu____3458 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____3474 =
                                                         let uu____3475 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3475 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3474);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3482 =
                                                               let uu____3483
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____3483.FStar_Ident.ident in
                                                             uu____3482.FStar_Ident.idText in
                                                           let uu____3485 =
                                                             let uu____3486 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3486 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3485))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3499 -> ())
                    | uu____3500 -> ()))
        | uu____3501 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3514 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3514 with
        | (ns,id) ->
            let uu____3524 = peek_record_cache () in
            FStar_Util.find_map uu____3524
              (fun record  ->
                 let uu____3527 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3530  -> None) uu____3527) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3531  -> Cont_ignore) (fun uu____3532  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3535 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3535)
        (fun k  -> fun uu____3538  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let uu____3547 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3547 with
      | Some r when r.is_record -> Some r
      | uu____3551 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3562 = try_lookup_record_by_field_name env lid in
        match uu____3562 with
        | Some record' when
            let uu____3565 =
              let uu____3566 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3566 in
            let uu____3568 =
              let uu____3569 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3569 in
            uu____3565 = uu____3568 ->
            let uu____3571 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3573  -> Cont_ok ()) in
            (match uu____3571 with
             | Cont_ok uu____3574 -> true
             | uu____3575 -> false)
        | uu____3577 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) Prims.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____3588 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3588 with
      | Some r ->
          let uu____3594 =
            let uu____3597 =
              let uu____3598 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3598
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3597, (r.is_record)) in
          Some uu____3594
      | uu____3601 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3610  ->
    let uu____3611 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3611
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3622  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___172_3631  ->
      match uu___172_3631 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___173_3651 =
            match uu___173_3651 with
            | Rec_binding uu____3652 -> true
            | uu____3653 -> false in
          let this_env =
            let uu___183_3655 = env in
            let uu____3656 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___183_3655.curmodule);
              curmonad = (uu___183_3655.curmonad);
              modules = (uu___183_3655.modules);
              scope_mods = uu____3656;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___183_3655.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___183_3655.sigaccum);
              sigmap = (uu___183_3655.sigmap);
              iface = (uu___183_3655.iface);
              admitted_iface = (uu___183_3655.admitted_iface);
              expect_typ = (uu___183_3655.expect_typ);
              docs = (uu___183_3655.docs);
              remaining_iface_decls = (uu___183_3655.remaining_iface_decls);
              syntax_only = (uu___183_3655.syntax_only)
            } in
          let uu____3658 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3658 with | None  -> true | Some uu____3664 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___184_3675 = env in
      {
        curmodule = (uu___184_3675.curmodule);
        curmonad = (uu___184_3675.curmonad);
        modules = (uu___184_3675.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___184_3675.exported_ids);
        trans_exported_ids = (uu___184_3675.trans_exported_ids);
        includes = (uu___184_3675.includes);
        sigaccum = (uu___184_3675.sigaccum);
        sigmap = (uu___184_3675.sigmap);
        iface = (uu___184_3675.iface);
        admitted_iface = (uu___184_3675.admitted_iface);
        expect_typ = (uu___184_3675.expect_typ);
        docs = (uu___184_3675.docs);
        remaining_iface_decls = (uu___184_3675.remaining_iface_decls);
        syntax_only = (uu___184_3675.syntax_only)
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
        let uu____3714 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____3714
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          Prims.raise
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
          | Some (se,uu____3734) ->
              let uu____3737 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____3737 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____3742 =
          let uu____3743 =
            let uu____3746 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____3746, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____3743 in
        Prims.raise uu____3742 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____3753 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3758 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3764 -> (true, true)
          | uu____3769 -> (false, false) in
        match uu____3753 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____3774 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3777 =
                     let uu____3778 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____3778 in
                   if uu____3777 then Some l else None) in
            (match uu____3774 with
             | Some l when
                 let uu____3782 = FStar_Options.interactive () in
                 Prims.op_Negation uu____3782 -> err1 l
             | uu____3783 ->
                 (extract_record env globals s;
                  (let uu___185_3788 = env in
                   {
                     curmodule = (uu___185_3788.curmodule);
                     curmonad = (uu___185_3788.curmonad);
                     modules = (uu___185_3788.modules);
                     scope_mods = (uu___185_3788.scope_mods);
                     exported_ids = (uu___185_3788.exported_ids);
                     trans_exported_ids = (uu___185_3788.trans_exported_ids);
                     includes = (uu___185_3788.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___185_3788.sigmap);
                     iface = (uu___185_3788.iface);
                     admitted_iface = (uu___185_3788.admitted_iface);
                     expect_typ = (uu___185_3788.expect_typ);
                     docs = (uu___185_3788.docs);
                     remaining_iface_decls =
                       (uu___185_3788.remaining_iface_decls);
                     syntax_only = (uu___185_3788.syntax_only)
                   }))) in
      let env2 =
        let uu___186_3790 = env1 in
        let uu____3791 = FStar_ST.read globals in
        {
          curmodule = (uu___186_3790.curmodule);
          curmonad = (uu___186_3790.curmonad);
          modules = (uu___186_3790.modules);
          scope_mods = uu____3791;
          exported_ids = (uu___186_3790.exported_ids);
          trans_exported_ids = (uu___186_3790.trans_exported_ids);
          includes = (uu___186_3790.includes);
          sigaccum = (uu___186_3790.sigaccum);
          sigmap = (uu___186_3790.sigmap);
          iface = (uu___186_3790.iface);
          admitted_iface = (uu___186_3790.admitted_iface);
          expect_typ = (uu___186_3790.expect_typ);
          docs = (uu___186_3790.docs);
          remaining_iface_decls = (uu___186_3790.remaining_iface_decls);
          syntax_only = (uu___186_3790.syntax_only)
        } in
      let uu____3796 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3810) ->
            let uu____3815 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____3815)
        | uu____3829 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____3796 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3859  ->
                   match uu____3859 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3870 =
                                  let uu____3872 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3872 in
                                FStar_ST.write globals uu____3870);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3881 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____3881.FStar_Ident.str in
                                    ((let uu____3883 =
                                        get_exported_id_set env3 modul in
                                      match uu____3883 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____3898 =
                                            let uu____3899 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3899 in
                                          FStar_ST.write my_exported_ids
                                            uu____3898
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
              let uu___187_3911 = env3 in
              let uu____3912 = FStar_ST.read globals in
              {
                curmodule = (uu___187_3911.curmodule);
                curmonad = (uu___187_3911.curmonad);
                modules = (uu___187_3911.modules);
                scope_mods = uu____3912;
                exported_ids = (uu___187_3911.exported_ids);
                trans_exported_ids = (uu___187_3911.trans_exported_ids);
                includes = (uu___187_3911.includes);
                sigaccum = (uu___187_3911.sigaccum);
                sigmap = (uu___187_3911.sigmap);
                iface = (uu___187_3911.iface);
                admitted_iface = (uu___187_3911.admitted_iface);
                expect_typ = (uu___187_3911.expect_typ);
                docs = (uu___187_3911.docs);
                remaining_iface_decls = (uu___187_3911.remaining_iface_decls);
                syntax_only = (uu___187_3911.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3923 =
        let uu____3926 = resolve_module_name env ns false in
        match uu____3926 with
        | None  ->
            let modules = env.modules in
            let uu____3934 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3940  ->
                      match uu____3940 with
                      | (m,uu____3944) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____3934
            then (ns, Open_namespace)
            else
              (let uu____3948 =
                 let uu____3949 =
                   let uu____3952 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____3952, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____3949 in
               Prims.raise uu____3948)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____3923 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____3966 = resolve_module_name env ns false in
      match uu____3966 with
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____3972 = current_module env1 in
              uu____3972.FStar_Ident.str in
            (let uu____3974 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____3974 with
             | None  -> ()
             | Some incl ->
                 let uu____3987 =
                   let uu____3989 = FStar_ST.read incl in ns1 :: uu____3989 in
                 FStar_ST.write incl uu____3987);
            (match () with
             | () ->
                 let uu____3997 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____3997 with
                  | Some ns_trans_exports ->
                      ((let uu____4010 =
                          let uu____4021 = get_exported_id_set env1 curmod in
                          let uu____4026 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____4021, uu____4026) in
                        match uu____4010 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____4066 = ns_trans_exports k in
                                FStar_ST.read uu____4066 in
                              let ex = cur_exports k in
                              (let uu____4075 =
                                 let uu____4076 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____4076 ns_ex in
                               FStar_ST.write ex uu____4075);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____4086 =
                                     let uu____4087 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____4087 ns_ex in
                                   FStar_ST.write trans_ex uu____4086) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____4093 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____4107 =
                        let uu____4108 =
                          let uu____4111 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____4111, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____4108 in
                      Prims.raise uu____4107))))
      | uu____4112 ->
          let uu____4114 =
            let uu____4115 =
              let uu____4118 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____4118, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____4115 in
          Prims.raise uu____4114
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____4128 = module_is_defined env l in
        if uu____4128
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____4131 =
             let uu____4132 =
               let uu____4135 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____4135, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____4132 in
           Prims.raise uu____4131)
let push_doc:
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option -> env =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____4149 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____4149 with
              | None  -> ()
              | Some old_doc ->
                  let uu____4152 =
                    let uu____4153 = FStar_Ident.string_of_lid l in
                    let uu____4154 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____4155 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____4153 uu____4154 uu____4155 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____4152);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____4164 = try_lookup_lid env l in
                (match uu____4164 with
                 | None  ->
                     ((let uu____4171 =
                         let uu____4172 = FStar_Options.interactive () in
                         Prims.op_Negation uu____4172 in
                       if uu____4171
                       then
                         let uu____4173 =
                           let uu____4174 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____4175 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____4174 uu____4175 in
                         FStar_Util.print_string uu____4173
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigqual) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___188_4181 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___188_4181.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___188_4181.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigqual = quals
                           }), false)))
                 | Some uu____4182 -> ())
            | uu____4187 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigqual in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4199) ->
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
                                (lid,uu____4207,uu____4208,uu____4209,uu____4210,uu____4211)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4216 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4219,uu____4220) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4224,lbs),uu____4226,uu____4227) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4240 =
                               let uu____4241 =
                                 let uu____4242 =
                                   let uu____4247 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4247.FStar_Syntax_Syntax.fv_name in
                                 uu____4242.FStar_Syntax_Syntax.v in
                               uu____4241.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4240))
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
                               let uu____4257 =
                                 let uu____4262 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4262.FStar_Syntax_Syntax.fv_name in
                               uu____4257.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___189_4269 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___189_4269.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigqual = quals1
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4276 -> ()));
      (let curmod =
         let uu____4278 = current_module env in uu____4278.FStar_Ident.str in
       (let uu____4280 =
          let uu____4291 = get_exported_id_set env curmod in
          let uu____4296 = get_trans_exported_id_set env curmod in
          (uu____4291, uu____4296) in
        match uu____4280 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4336 = cur_ex eikind in FStar_ST.read uu____4336 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4344 =
                let uu____4345 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4345 in
              FStar_ST.write cur_trans_ex_set_ref uu____4344 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4351 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___190_4363 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___190_4363.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___190_4363.exported_ids);
                    trans_exported_ids = (uu___190_4363.trans_exported_ids);
                    includes = (uu___190_4363.includes);
                    sigaccum = [];
                    sigmap = (uu___190_4363.sigmap);
                    iface = (uu___190_4363.iface);
                    admitted_iface = (uu___190_4363.admitted_iface);
                    expect_typ = (uu___190_4363.expect_typ);
                    docs = (uu___190_4363.docs);
                    remaining_iface_decls =
                      (uu___190_4363.remaining_iface_decls);
                    syntax_only = (uu___190_4363.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4376 =
       let uu____4378 = FStar_ST.read stack in env :: uu____4378 in
     FStar_ST.write stack uu____4376);
    (let uu___191_4386 = env in
     let uu____4387 = FStar_Util.smap_copy (sigmap env) in
     let uu____4393 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___191_4386.curmodule);
       curmonad = (uu___191_4386.curmonad);
       modules = (uu___191_4386.modules);
       scope_mods = (uu___191_4386.scope_mods);
       exported_ids = (uu___191_4386.exported_ids);
       trans_exported_ids = (uu___191_4386.trans_exported_ids);
       includes = (uu___191_4386.includes);
       sigaccum = (uu___191_4386.sigaccum);
       sigmap = uu____4387;
       iface = (uu___191_4386.iface);
       admitted_iface = (uu___191_4386.admitted_iface);
       expect_typ = (uu___191_4386.expect_typ);
       docs = uu____4393;
       remaining_iface_decls = (uu___191_4386.remaining_iface_decls);
       syntax_only = (uu___191_4386.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____4397  ->
    let uu____4398 = FStar_ST.read stack in
    match uu____4398 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4411 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4417 = FStar_ST.read stack in
     match uu____4417 with
     | uu____4422::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4429 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4436  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4448 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4450 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4468 = FStar_Util.smap_try_find sm' k in
              match uu____4468 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___192_4484 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___192_4484.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___192_4484.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigqual =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigqual))
                          }
                      | uu____4485 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4488 -> ()));
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
              if FStar_Ident.lid_equals mname FStar_Syntax_Const.prims_lid
              then []
              else
                if
                  FStar_Util.starts_with "FStar."
                    (FStar_Ident.text_of_lid mname)
                then
                  [FStar_Syntax_Const.prims_lid;
                  FStar_Syntax_Const.fstar_ns_lid]
                else
                  [FStar_Syntax_Const.prims_lid;
                  FStar_Syntax_Const.st_lid;
                  FStar_Syntax_Const.all_lid;
                  FStar_Syntax_Const.fstar_ns_lid] in
            let open_ns1 =
              if
                (FStar_List.length mname.FStar_Ident.ns) <>
                  (Prims.parse_int "0")
              then
                let ns = FStar_Ident.lid_of_ids mname.FStar_Ident.ns in ns ::
                  open_ns
              else open_ns in
            (let uu____4532 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4532);
            (match () with
             | () ->
                 ((let uu____4537 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4537);
                  (match () with
                   | () ->
                       ((let uu____4542 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4542);
                        (match () with
                         | () ->
                             let uu___193_4551 = env1 in
                             let uu____4552 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___193_4551.curmonad);
                               modules = (uu___193_4551.modules);
                               scope_mods = uu____4552;
                               exported_ids = (uu___193_4551.exported_ids);
                               trans_exported_ids =
                                 (uu___193_4551.trans_exported_ids);
                               includes = (uu___193_4551.includes);
                               sigaccum = (uu___193_4551.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___193_4551.expect_typ);
                               docs = (uu___193_4551.docs);
                               remaining_iface_decls =
                                 (uu___193_4551.remaining_iface_decls);
                               syntax_only = (uu___193_4551.syntax_only)
                             }))))) in
          let uu____4555 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4567  ->
                    match uu____4567 with
                    | (l,uu____4571) -> FStar_Ident.lid_equals l mname)) in
          match uu____4555 with
          | None  -> let uu____4576 = prep env in (uu____4576, false)
          | Some (uu____4577,m) ->
              ((let uu____4582 =
                  (let uu____4583 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4583) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4582
                then
                  let uu____4584 =
                    let uu____4585 =
                      let uu____4588 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4588, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4585 in
                  Prims.raise uu____4584
                else ());
               (let uu____4590 = let uu____4591 = push env in prep uu____4591 in
                (uu____4590, true)))
let enter_monad_scope: env -> FStar_Ident.ident -> env =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | Some mname' ->
          Prims.raise
            (FStar_Errors.Error
               ((Prims.strcat "Trying to define monad "
                   (Prims.strcat mname.FStar_Ident.idText
                      (Prims.strcat ", but already in monad scope "
                         mname'.FStar_Ident.idText))),
                 (mname.FStar_Ident.idRange)))
      | None  ->
          let uu___194_4599 = env in
          {
            curmodule = (uu___194_4599.curmodule);
            curmonad = (Some mname);
            modules = (uu___194_4599.modules);
            scope_mods = (uu___194_4599.scope_mods);
            exported_ids = (uu___194_4599.exported_ids);
            trans_exported_ids = (uu___194_4599.trans_exported_ids);
            includes = (uu___194_4599.includes);
            sigaccum = (uu___194_4599.sigaccum);
            sigmap = (uu___194_4599.sigmap);
            iface = (uu___194_4599.iface);
            admitted_iface = (uu___194_4599.admitted_iface);
            expect_typ = (uu___194_4599.expect_typ);
            docs = (uu___194_4599.docs);
            remaining_iface_decls = (uu___194_4599.remaining_iface_decls);
            syntax_only = (uu___194_4599.syntax_only)
          }
let fail_or env lookup lid =
  let uu____4624 = lookup lid in
  match uu____4624 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4630  ->
             match uu____4630 with
             | (lid1,uu____4634) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4641 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4641
               (FStar_Ident.range_of_lid lid) in
           let uu____4642 = resolve_module_name env modul true in
           match uu____4642 with
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
      Prims.raise (FStar_Errors.Error (msg1, (FStar_Ident.range_of_lid lid)))
  | Some r -> r
let fail_or2 lookup id =
  let uu____4669 = lookup id in
  match uu____4669 with
  | None  ->
      Prims.raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r