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
      let uu___175_390 = env in
      {
        curmodule = (uu___175_390.curmodule);
        curmonad = (uu___175_390.curmonad);
        modules = (uu___175_390.modules);
        scope_mods = (uu___175_390.scope_mods);
        exported_ids = (uu___175_390.exported_ids);
        trans_exported_ids = (uu___175_390.trans_exported_ids);
        includes = (uu___175_390.includes);
        sigaccum = (uu___175_390.sigaccum);
        sigmap = (uu___175_390.sigmap);
        iface = b;
        admitted_iface = (uu___175_390.admitted_iface);
        expect_typ = (uu___175_390.expect_typ);
        docs = (uu___175_390.docs);
        remaining_iface_decls = (uu___175_390.remaining_iface_decls);
        syntax_only = (uu___175_390.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___176_400 = e in
      {
        curmodule = (uu___176_400.curmodule);
        curmonad = (uu___176_400.curmonad);
        modules = (uu___176_400.modules);
        scope_mods = (uu___176_400.scope_mods);
        exported_ids = (uu___176_400.exported_ids);
        trans_exported_ids = (uu___176_400.trans_exported_ids);
        includes = (uu___176_400.includes);
        sigaccum = (uu___176_400.sigaccum);
        sigmap = (uu___176_400.sigmap);
        iface = (uu___176_400.iface);
        admitted_iface = b;
        expect_typ = (uu___176_400.expect_typ);
        docs = (uu___176_400.docs);
        remaining_iface_decls = (uu___176_400.remaining_iface_decls);
        syntax_only = (uu___176_400.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___177_410 = e in
      {
        curmodule = (uu___177_410.curmodule);
        curmonad = (uu___177_410.curmonad);
        modules = (uu___177_410.modules);
        scope_mods = (uu___177_410.scope_mods);
        exported_ids = (uu___177_410.exported_ids);
        trans_exported_ids = (uu___177_410.trans_exported_ids);
        includes = (uu___177_410.includes);
        sigaccum = (uu___177_410.sigaccum);
        sigmap = (uu___177_410.sigmap);
        iface = (uu___177_410.iface);
        admitted_iface = (uu___177_410.admitted_iface);
        expect_typ = b;
        docs = (uu___177_410.docs);
        remaining_iface_decls = (uu___177_410.remaining_iface_decls);
        syntax_only = (uu___177_410.syntax_only)
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
      let uu___178_446 = e in
      {
        curmodule = (Some l);
        curmonad = (uu___178_446.curmonad);
        modules = (uu___178_446.modules);
        scope_mods = (uu___178_446.scope_mods);
        exported_ids = (uu___178_446.exported_ids);
        trans_exported_ids = (uu___178_446.trans_exported_ids);
        includes = (uu___178_446.includes);
        sigaccum = (uu___178_446.sigaccum);
        sigmap = (uu___178_446.sigmap);
        iface = (uu___178_446.iface);
        admitted_iface = (uu___178_446.admitted_iface);
        expect_typ = (uu___178_446.expect_typ);
        docs = (uu___178_446.docs);
        remaining_iface_decls = (uu___178_446.remaining_iface_decls);
        syntax_only = (uu___178_446.syntax_only)
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
            let uu___179_548 = env in
            {
              curmodule = (uu___179_548.curmodule);
              curmonad = (uu___179_548.curmonad);
              modules = (uu___179_548.modules);
              scope_mods = (uu___179_548.scope_mods);
              exported_ids = (uu___179_548.exported_ids);
              trans_exported_ids = (uu___179_548.trans_exported_ids);
              includes = (uu___179_548.includes);
              sigaccum = (uu___179_548.sigaccum);
              sigmap = (uu___179_548.sigmap);
              iface = (uu___179_548.iface);
              admitted_iface = (uu___179_548.admitted_iface);
              expect_typ = (uu___179_548.expect_typ);
              docs = (uu___179_548.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___179_548.syntax_only)
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
      let uu___180_576 = env in
      {
        curmodule = (uu___180_576.curmodule);
        curmonad = (uu___180_576.curmonad);
        modules = (uu___180_576.modules);
        scope_mods = (uu___180_576.scope_mods);
        exported_ids = (uu___180_576.exported_ids);
        trans_exported_ids = (uu___180_576.trans_exported_ids);
        includes = (uu___180_576.includes);
        sigaccum = (uu___180_576.sigaccum);
        sigmap = (uu___180_576.sigmap);
        iface = (uu___180_576.iface);
        admitted_iface = (uu___180_576.admitted_iface);
        expect_typ = (uu___180_576.expect_typ);
        docs = (uu___180_576.docs);
        remaining_iface_decls = (uu___180_576.remaining_iface_decls);
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
        let uu___181_634 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___181_634.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___182_635 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___182_635.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___182_635.FStar_Syntax_Syntax.sort)
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
let option_of_cont k_ignore uu___148_780 =
  match uu___148_780 with
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
  fun uu___149_866  ->
    match uu___149_866 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___150_915 =
    match uu___150_915 with
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
  fun uu___151_973  ->
    match uu___151_973 with | Exported_id_field  -> true | uu____974 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___152_1063 =
    match uu___152_1063 with
    | (id',uu____1065,uu____1066) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___153_1070 =
    match uu___153_1070 with
    | (id',uu____1072,uu____1073) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1076 = current_module env in FStar_Ident.ids_of_lid uu____1076 in
  let proc uu___154_1081 =
    match uu___154_1081 with
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
  let rec aux uu___155_1098 =
    match uu___155_1098 with
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
        let rec aux uu___156_1352 =
          match uu___156_1352 with
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
        (fun uu___157_1418  ->
           match uu___157_1418 with
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
let cont_of_option k_none uu___158_1690 =
  match uu___158_1690 with | Some v1 -> Cont_ok v1 | None  -> k_none
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
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___159_1811  ->
               match uu___159_1811 with
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
          let k_global_def source_lid uu___163_1879 =
            match uu___163_1879 with
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
                     let quals = se.FStar_Syntax_Syntax.sigquals in
                     let uu____1940 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___160_1942  ->
                                  match uu___160_1942 with
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
                                      (fun uu___161_1949  ->
                                         match uu___161_1949 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1952 -> false)))) in
                         if uu____1947
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____1954 =
                         FStar_Util.find_map quals
                           (fun uu___162_1956  ->
                              match uu___162_1956 with
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
             FStar_Syntax_Syntax.sigquals = uu____2119;
             FStar_Syntax_Syntax.sigmeta = uu____2120;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2130;
             FStar_Syntax_Syntax.sigquals = uu____2131;
             FStar_Syntax_Syntax.sigmeta = uu____2132;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____2141,uu____2142,uu____2143,uu____2144,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2146;
             FStar_Syntax_Syntax.sigquals = uu____2147;
             FStar_Syntax_Syntax.sigmeta = uu____2148;_},l1)
          -> Some (l1, cattributes)
      | uu____2159 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      let uu____2173 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2173 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2179;
             FStar_Syntax_Syntax.sigquals = uu____2180;
             FStar_Syntax_Syntax.sigmeta = uu____2181;_},uu____2182)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2187;
             FStar_Syntax_Syntax.sigquals = uu____2188;
             FStar_Syntax_Syntax.sigmeta = uu____2189;_},uu____2190)
          -> Some ne
      | uu____2194 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2204 = try_lookup_effect_name env lid in
      match uu____2204 with | None  -> false | Some uu____2206 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2214 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2214 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____2220,uu____2221,uu____2222,uu____2223);
             FStar_Syntax_Syntax.sigrng = uu____2224;
             FStar_Syntax_Syntax.sigquals = uu____2225;
             FStar_Syntax_Syntax.sigmeta = uu____2226;_},uu____2227)
          ->
          let rec aux new_name =
            let uu____2238 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2238 with
            | None  -> None
            | Some (s,uu____2248) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____2253,uu____2254,uu____2255,cmp,uu____2257) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2261 -> None) in
          aux l'
      | Some (uu____2262,l') -> Some l'
      | uu____2266 -> None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___164_2287 =
        match uu___164_2287 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2292,uu____2293,uu____2294);
             FStar_Syntax_Syntax.sigrng = uu____2295;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2297;_},uu____2298)
            -> Some quals
        | uu____2301 -> None in
      let uu____2305 =
        resolve_in_open_namespaces' env lid (fun uu____2309  -> None)
          (fun uu____2311  -> None) k_global_def in
      match uu____2305 with | Some quals -> quals | uu____2317 -> []
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul Prims.option =
  fun env  ->
    fun path  ->
      let uu____2329 =
        FStar_List.tryFind
          (fun uu____2335  ->
             match uu____2335 with
             | (mlid,modul) ->
                 let uu____2340 = FStar_Ident.path_of_lid mlid in
                 uu____2340 = path) env.modules in
      match uu____2329 with
      | Some (uu____2344,modul) -> Some modul
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___165_2366 =
        match uu___165_2366 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2370,lbs),uu____2372,uu____2373);
             FStar_Syntax_Syntax.sigrng = uu____2374;
             FStar_Syntax_Syntax.sigquals = uu____2375;
             FStar_Syntax_Syntax.sigmeta = uu____2376;_},uu____2377)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2389 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2389
        | uu____2390 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2393  -> None)
        (fun uu____2394  -> None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___166_2413 =
        match uu___166_2413 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2420,uu____2421);
             FStar_Syntax_Syntax.sigrng = uu____2422;
             FStar_Syntax_Syntax.sigquals = uu____2423;
             FStar_Syntax_Syntax.sigmeta = uu____2424;_},uu____2425)
            ->
            FStar_Util.find_map (Prims.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2441 -> None)
        | uu____2446 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2453  -> None)
        (fun uu____2456  -> None) k_global_def
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
          let uu____2483 = try_lookup_name any_val exclude_interf env lid in
          match uu____2483 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2492 -> None
let try_lookup_lid:
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2512 = try_lookup_lid env l in
      match uu____2512 with
      | None  -> None
      | Some (e,uu____2520) ->
          let uu____2523 =
            let uu____2524 = FStar_Syntax_Subst.compress e in
            uu____2524.FStar_Syntax_Syntax.n in
          (match uu____2523 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2533 -> None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___183_2544 = env in
        {
          curmodule = (uu___183_2544.curmodule);
          curmonad = (uu___183_2544.curmonad);
          modules = (uu___183_2544.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___183_2544.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___183_2544.sigaccum);
          sigmap = (uu___183_2544.sigmap);
          iface = (uu___183_2544.iface);
          admitted_iface = (uu___183_2544.admitted_iface);
          expect_typ = (uu___183_2544.expect_typ);
          docs = (uu___183_2544.docs);
          remaining_iface_decls = (uu___183_2544.remaining_iface_decls);
          syntax_only = (uu___183_2544.syntax_only)
        } in
      try_lookup_lid env' l
let try_lookup_doc:
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___168_2568 =
        match uu___168_2568 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2572,uu____2573,uu____2574);
             FStar_Syntax_Syntax.sigrng = uu____2575;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2577;_},uu____2578)
            ->
            let uu____2580 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___167_2582  ->
                      match uu___167_2582 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2583 -> false)) in
            if uu____2580
            then
              let uu____2585 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2585
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2587;
             FStar_Syntax_Syntax.sigrng = uu____2588;
             FStar_Syntax_Syntax.sigquals = uu____2589;
             FStar_Syntax_Syntax.sigmeta = uu____2590;_},uu____2591)
            ->
            let uu____2600 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2600
        | uu____2601 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2604  -> None)
        (fun uu____2605  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___169_2624 =
        match uu___169_2624 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2629,uu____2630,uu____2631,uu____2632,datas,uu____2634);
             FStar_Syntax_Syntax.sigrng = uu____2635;
             FStar_Syntax_Syntax.sigquals = uu____2636;
             FStar_Syntax_Syntax.sigmeta = uu____2637;_},uu____2638)
            -> Some datas
        | uu____2645 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2650  -> None)
        (fun uu____2652  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____2686 =
    let uu____2687 =
      let uu____2690 =
        let uu____2692 = FStar_ST.read record_cache in
        FStar_List.hd uu____2692 in
      let uu____2700 = FStar_ST.read record_cache in uu____2690 :: uu____2700 in
    FStar_ST.write record_cache uu____2687 in
  let pop1 uu____2715 =
    let uu____2716 =
      let uu____2719 = FStar_ST.read record_cache in FStar_List.tl uu____2719 in
    FStar_ST.write record_cache uu____2716 in
  let peek uu____2735 =
    let uu____2736 = FStar_ST.read record_cache in FStar_List.hd uu____2736 in
  let insert r =
    let uu____2748 =
      let uu____2751 = let uu____2753 = peek () in r :: uu____2753 in
      let uu____2755 =
        let uu____2758 = FStar_ST.read record_cache in
        FStar_List.tl uu____2758 in
      uu____2751 :: uu____2755 in
    FStar_ST.write record_cache uu____2748 in
  let commit1 uu____2774 =
    let uu____2775 = FStar_ST.read record_cache in
    match uu____2775 with
    | hd1::uu____2783::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2796 -> failwith "Impossible" in
  let filter1 uu____2802 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____2809 =
           let uu____2812 = FStar_ST.read record_cache in filtered ::
             uu____2812 in
         FStar_ST.write record_cache uu____2809) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____2886 = record_cache_aux_with_filter in
  match uu____2886 with | (aux,uu____2924) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____2963 = record_cache_aux_with_filter in
  match uu____2963 with | (uu____2986,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____3026 = record_cache_aux in
  match uu____3026 with
  | (push1,uu____3046,uu____3047,uu____3048,uu____3049) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3074 = record_cache_aux in
  match uu____3074 with
  | (uu____3093,pop1,uu____3095,uu____3096,uu____3097) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____3123 = record_cache_aux in
  match uu____3123 with
  | (uu____3143,uu____3144,peek,uu____3146,uu____3147) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____3172 = record_cache_aux in
  match uu____3172 with
  | (uu____3191,uu____3192,uu____3193,insert,uu____3195) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____3220 = record_cache_aux in
  match uu____3220 with
  | (uu____3239,uu____3240,uu____3241,uu____3242,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3282) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___170_3291  ->
                   match uu___170_3291 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____3294 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___171_3302  ->
                      match uu___171_3302 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3304,uu____3305,uu____3306,uu____3307,uu____3308);
                          FStar_Syntax_Syntax.sigrng = uu____3309;
                          FStar_Syntax_Syntax.sigquals = uu____3310;
                          FStar_Syntax_Syntax.sigmeta = uu____3311;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3315 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___172_3317  ->
                    match uu___172_3317 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____3321,uu____3322,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____3324;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____3326;_} ->
                        let uu____3331 =
                          let uu____3332 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3332 in
                        (match uu____3331 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3336,t,uu____3338,uu____3339,uu____3340);
                             FStar_Syntax_Syntax.sigrng = uu____3341;
                             FStar_Syntax_Syntax.sigquals = uu____3342;
                             FStar_Syntax_Syntax.sigmeta = uu____3343;_} ->
                             let uu____3347 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3347 with
                              | (formals,uu____3356) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3382  ->
                                            match uu____3382 with
                                            | (x,q) ->
                                                let uu____3390 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3390
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3421  ->
                                            match uu____3421 with
                                            | (x,q) ->
                                                let uu____3430 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____3430,
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
                                  ((let uu____3442 =
                                      let uu____3444 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3444 in
                                    FStar_ST.write new_globs uu____3442);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3460 =
                                            match uu____3460 with
                                            | (id,uu____3466) ->
                                                let modul =
                                                  let uu____3472 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3472.FStar_Ident.str in
                                                let uu____3473 =
                                                  get_exported_id_set e modul in
                                                (match uu____3473 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____3489 =
                                                         let uu____3490 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3490 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3489);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3497 =
                                                               let uu____3498
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____3498.FStar_Ident.ident in
                                                             uu____3497.FStar_Ident.idText in
                                                           let uu____3500 =
                                                             let uu____3501 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3501 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3500))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3514 -> ())
                    | uu____3515 -> ()))
        | uu____3516 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3529 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3529 with
        | (ns,id) ->
            let uu____3539 = peek_record_cache () in
            FStar_Util.find_map uu____3539
              (fun record  ->
                 let uu____3542 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3545  -> None) uu____3542) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3546  -> Cont_ignore) (fun uu____3547  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3550 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3550)
        (fun k  -> fun uu____3553  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let uu____3562 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3562 with
      | Some r when r.is_record -> Some r
      | uu____3566 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3577 = try_lookup_record_by_field_name env lid in
        match uu____3577 with
        | Some record' when
            let uu____3580 =
              let uu____3581 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3581 in
            let uu____3583 =
              let uu____3584 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3584 in
            uu____3580 = uu____3583 ->
            let uu____3586 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3588  -> Cont_ok ()) in
            (match uu____3586 with
             | Cont_ok uu____3589 -> true
             | uu____3590 -> false)
        | uu____3592 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) Prims.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____3603 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3603 with
      | Some r ->
          let uu____3609 =
            let uu____3612 =
              let uu____3613 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3613
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3612, (r.is_record)) in
          Some uu____3609
      | uu____3616 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3625  ->
    let uu____3626 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3626
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3637  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___173_3646  ->
      match uu___173_3646 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___174_3666 =
            match uu___174_3666 with
            | Rec_binding uu____3667 -> true
            | uu____3668 -> false in
          let this_env =
            let uu___184_3670 = env in
            let uu____3671 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___184_3670.curmodule);
              curmonad = (uu___184_3670.curmonad);
              modules = (uu___184_3670.modules);
              scope_mods = uu____3671;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___184_3670.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___184_3670.sigaccum);
              sigmap = (uu___184_3670.sigmap);
              iface = (uu___184_3670.iface);
              admitted_iface = (uu___184_3670.admitted_iface);
              expect_typ = (uu___184_3670.expect_typ);
              docs = (uu___184_3670.docs);
              remaining_iface_decls = (uu___184_3670.remaining_iface_decls);
              syntax_only = (uu___184_3670.syntax_only)
            } in
          let uu____3673 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3673 with | None  -> true | Some uu____3679 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___185_3690 = env in
      {
        curmodule = (uu___185_3690.curmodule);
        curmonad = (uu___185_3690.curmonad);
        modules = (uu___185_3690.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___185_3690.exported_ids);
        trans_exported_ids = (uu___185_3690.trans_exported_ids);
        includes = (uu___185_3690.includes);
        sigaccum = (uu___185_3690.sigaccum);
        sigmap = (uu___185_3690.sigmap);
        iface = (uu___185_3690.iface);
        admitted_iface = (uu___185_3690.admitted_iface);
        expect_typ = (uu___185_3690.expect_typ);
        docs = (uu___185_3690.docs);
        remaining_iface_decls = (uu___185_3690.remaining_iface_decls);
        syntax_only = (uu___185_3690.syntax_only)
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
        let uu____3729 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____3729
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
          | Some (se,uu____3749) ->
              let uu____3752 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____3752 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____3757 =
          let uu____3758 =
            let uu____3761 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____3761, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____3758 in
        Prims.raise uu____3757 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____3768 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3773 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3779 -> (true, true)
          | uu____3784 -> (false, false) in
        match uu____3768 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____3789 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3792 =
                     let uu____3793 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____3793 in
                   if uu____3792 then Some l else None) in
            (match uu____3789 with
             | Some l when
                 let uu____3797 = FStar_Options.interactive () in
                 Prims.op_Negation uu____3797 -> err1 l
             | uu____3798 ->
                 (extract_record env globals s;
                  (let uu___186_3803 = env in
                   {
                     curmodule = (uu___186_3803.curmodule);
                     curmonad = (uu___186_3803.curmonad);
                     modules = (uu___186_3803.modules);
                     scope_mods = (uu___186_3803.scope_mods);
                     exported_ids = (uu___186_3803.exported_ids);
                     trans_exported_ids = (uu___186_3803.trans_exported_ids);
                     includes = (uu___186_3803.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___186_3803.sigmap);
                     iface = (uu___186_3803.iface);
                     admitted_iface = (uu___186_3803.admitted_iface);
                     expect_typ = (uu___186_3803.expect_typ);
                     docs = (uu___186_3803.docs);
                     remaining_iface_decls =
                       (uu___186_3803.remaining_iface_decls);
                     syntax_only = (uu___186_3803.syntax_only)
                   }))) in
      let env2 =
        let uu___187_3805 = env1 in
        let uu____3806 = FStar_ST.read globals in
        {
          curmodule = (uu___187_3805.curmodule);
          curmonad = (uu___187_3805.curmonad);
          modules = (uu___187_3805.modules);
          scope_mods = uu____3806;
          exported_ids = (uu___187_3805.exported_ids);
          trans_exported_ids = (uu___187_3805.trans_exported_ids);
          includes = (uu___187_3805.includes);
          sigaccum = (uu___187_3805.sigaccum);
          sigmap = (uu___187_3805.sigmap);
          iface = (uu___187_3805.iface);
          admitted_iface = (uu___187_3805.admitted_iface);
          expect_typ = (uu___187_3805.expect_typ);
          docs = (uu___187_3805.docs);
          remaining_iface_decls = (uu___187_3805.remaining_iface_decls);
          syntax_only = (uu___187_3805.syntax_only)
        } in
      let uu____3811 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3825) ->
            let uu____3830 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____3830)
        | uu____3844 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____3811 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3874  ->
                   match uu____3874 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3885 =
                                  let uu____3887 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3887 in
                                FStar_ST.write globals uu____3885);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3896 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____3896.FStar_Ident.str in
                                    ((let uu____3898 =
                                        get_exported_id_set env3 modul in
                                      match uu____3898 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____3913 =
                                            let uu____3914 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3914 in
                                          FStar_ST.write my_exported_ids
                                            uu____3913
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
              let uu___188_3926 = env3 in
              let uu____3927 = FStar_ST.read globals in
              {
                curmodule = (uu___188_3926.curmodule);
                curmonad = (uu___188_3926.curmonad);
                modules = (uu___188_3926.modules);
                scope_mods = uu____3927;
                exported_ids = (uu___188_3926.exported_ids);
                trans_exported_ids = (uu___188_3926.trans_exported_ids);
                includes = (uu___188_3926.includes);
                sigaccum = (uu___188_3926.sigaccum);
                sigmap = (uu___188_3926.sigmap);
                iface = (uu___188_3926.iface);
                admitted_iface = (uu___188_3926.admitted_iface);
                expect_typ = (uu___188_3926.expect_typ);
                docs = (uu___188_3926.docs);
                remaining_iface_decls = (uu___188_3926.remaining_iface_decls);
                syntax_only = (uu___188_3926.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3938 =
        let uu____3941 = resolve_module_name env ns false in
        match uu____3941 with
        | None  ->
            let modules = env.modules in
            let uu____3949 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3955  ->
                      match uu____3955 with
                      | (m,uu____3959) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____3949
            then (ns, Open_namespace)
            else
              (let uu____3963 =
                 let uu____3964 =
                   let uu____3967 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____3967, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____3964 in
               Prims.raise uu____3963)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____3938 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____3981 = resolve_module_name env ns false in
      match uu____3981 with
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____3987 = current_module env1 in
              uu____3987.FStar_Ident.str in
            (let uu____3989 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____3989 with
             | None  -> ()
             | Some incl ->
                 let uu____4002 =
                   let uu____4004 = FStar_ST.read incl in ns1 :: uu____4004 in
                 FStar_ST.write incl uu____4002);
            (match () with
             | () ->
                 let uu____4012 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____4012 with
                  | Some ns_trans_exports ->
                      ((let uu____4025 =
                          let uu____4036 = get_exported_id_set env1 curmod in
                          let uu____4041 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____4036, uu____4041) in
                        match uu____4025 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____4081 = ns_trans_exports k in
                                FStar_ST.read uu____4081 in
                              let ex = cur_exports k in
                              (let uu____4090 =
                                 let uu____4091 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____4091 ns_ex in
                               FStar_ST.write ex uu____4090);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____4101 =
                                     let uu____4102 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____4102 ns_ex in
                                   FStar_ST.write trans_ex uu____4101) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____4108 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____4122 =
                        let uu____4123 =
                          let uu____4126 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____4126, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____4123 in
                      Prims.raise uu____4122))))
      | uu____4127 ->
          let uu____4129 =
            let uu____4130 =
              let uu____4133 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____4133, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____4130 in
          Prims.raise uu____4129
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____4143 = module_is_defined env l in
        if uu____4143
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____4146 =
             let uu____4147 =
               let uu____4150 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____4150, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____4147 in
           Prims.raise uu____4146)
let push_doc:
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option -> env =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____4164 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____4164 with
              | None  -> ()
              | Some old_doc ->
                  let uu____4167 =
                    let uu____4168 = FStar_Ident.string_of_lid l in
                    let uu____4169 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____4170 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____4168 uu____4169 uu____4170 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____4167);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____4179 = try_lookup_lid env l in
                (match uu____4179 with
                 | None  ->
                     ((let uu____4186 =
                         let uu____4187 = FStar_Options.interactive () in
                         Prims.op_Negation uu____4187 in
                       if uu____4186
                       then
                         let uu____4188 =
                           let uu____4189 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____4190 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____4189 uu____4190 in
                         FStar_Util.print_string uu____4188
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___189_4196 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___189_4196.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___189_4196.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___189_4196.FStar_Syntax_Syntax.sigmeta)
                           }), false)))
                 | Some uu____4197 -> ())
            | uu____4202 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4214) ->
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
                                (lid,uu____4222,uu____4223,uu____4224,uu____4225,uu____4226)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4231 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4234,uu____4235) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4239,lbs),uu____4241,uu____4242) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4255 =
                               let uu____4256 =
                                 let uu____4257 =
                                   let uu____4262 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4262.FStar_Syntax_Syntax.fv_name in
                                 uu____4257.FStar_Syntax_Syntax.v in
                               uu____4256.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4255))
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
                               let uu____4272 =
                                 let uu____4277 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4277.FStar_Syntax_Syntax.fv_name in
                               uu____4272.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___190_4284 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___190_4284.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___190_4284.FStar_Syntax_Syntax.sigmeta)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4291 -> ()));
      (let curmod =
         let uu____4293 = current_module env in uu____4293.FStar_Ident.str in
       (let uu____4295 =
          let uu____4306 = get_exported_id_set env curmod in
          let uu____4311 = get_trans_exported_id_set env curmod in
          (uu____4306, uu____4311) in
        match uu____4295 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4351 = cur_ex eikind in FStar_ST.read uu____4351 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4359 =
                let uu____4360 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4360 in
              FStar_ST.write cur_trans_ex_set_ref uu____4359 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4366 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___191_4378 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___191_4378.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___191_4378.exported_ids);
                    trans_exported_ids = (uu___191_4378.trans_exported_ids);
                    includes = (uu___191_4378.includes);
                    sigaccum = [];
                    sigmap = (uu___191_4378.sigmap);
                    iface = (uu___191_4378.iface);
                    admitted_iface = (uu___191_4378.admitted_iface);
                    expect_typ = (uu___191_4378.expect_typ);
                    docs = (uu___191_4378.docs);
                    remaining_iface_decls =
                      (uu___191_4378.remaining_iface_decls);
                    syntax_only = (uu___191_4378.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4391 =
       let uu____4393 = FStar_ST.read stack in env :: uu____4393 in
     FStar_ST.write stack uu____4391);
    (let uu___192_4401 = env in
     let uu____4402 = FStar_Util.smap_copy (sigmap env) in
     let uu____4408 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___192_4401.curmodule);
       curmonad = (uu___192_4401.curmonad);
       modules = (uu___192_4401.modules);
       scope_mods = (uu___192_4401.scope_mods);
       exported_ids = (uu___192_4401.exported_ids);
       trans_exported_ids = (uu___192_4401.trans_exported_ids);
       includes = (uu___192_4401.includes);
       sigaccum = (uu___192_4401.sigaccum);
       sigmap = uu____4402;
       iface = (uu___192_4401.iface);
       admitted_iface = (uu___192_4401.admitted_iface);
       expect_typ = (uu___192_4401.expect_typ);
       docs = uu____4408;
       remaining_iface_decls = (uu___192_4401.remaining_iface_decls);
       syntax_only = (uu___192_4401.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____4412  ->
    let uu____4413 = FStar_ST.read stack in
    match uu____4413 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4426 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4432 = FStar_ST.read stack in
     match uu____4432 with
     | uu____4437::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4444 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4451  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4463 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4465 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4483 = FStar_Util.smap_try_find sm' k in
              match uu____4483 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___193_4499 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___193_4499.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___193_4499.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___193_4499.FStar_Syntax_Syntax.sigmeta)
                          }
                      | uu____4500 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4503 -> ()));
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
                  FStar_Parser_Const.fstar_ns_lid]
                else
                  [FStar_Parser_Const.prims_lid;
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
            (let uu____4547 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4547);
            (match () with
             | () ->
                 ((let uu____4552 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4552);
                  (match () with
                   | () ->
                       ((let uu____4557 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4557);
                        (match () with
                         | () ->
                             let uu___194_4566 = env1 in
                             let uu____4567 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___194_4566.curmonad);
                               modules = (uu___194_4566.modules);
                               scope_mods = uu____4567;
                               exported_ids = (uu___194_4566.exported_ids);
                               trans_exported_ids =
                                 (uu___194_4566.trans_exported_ids);
                               includes = (uu___194_4566.includes);
                               sigaccum = (uu___194_4566.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___194_4566.expect_typ);
                               docs = (uu___194_4566.docs);
                               remaining_iface_decls =
                                 (uu___194_4566.remaining_iface_decls);
                               syntax_only = (uu___194_4566.syntax_only)
                             }))))) in
          let uu____4570 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4582  ->
                    match uu____4582 with
                    | (l,uu____4586) -> FStar_Ident.lid_equals l mname)) in
          match uu____4570 with
          | None  -> let uu____4591 = prep env in (uu____4591, false)
          | Some (uu____4592,m) ->
              ((let uu____4597 =
                  (let uu____4598 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4598) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4597
                then
                  let uu____4599 =
                    let uu____4600 =
                      let uu____4603 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4603, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4600 in
                  Prims.raise uu____4599
                else ());
               (let uu____4605 = let uu____4606 = push env in prep uu____4606 in
                (uu____4605, true)))
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
          let uu___195_4614 = env in
          {
            curmodule = (uu___195_4614.curmodule);
            curmonad = (Some mname);
            modules = (uu___195_4614.modules);
            scope_mods = (uu___195_4614.scope_mods);
            exported_ids = (uu___195_4614.exported_ids);
            trans_exported_ids = (uu___195_4614.trans_exported_ids);
            includes = (uu___195_4614.includes);
            sigaccum = (uu___195_4614.sigaccum);
            sigmap = (uu___195_4614.sigmap);
            iface = (uu___195_4614.iface);
            admitted_iface = (uu___195_4614.admitted_iface);
            expect_typ = (uu___195_4614.expect_typ);
            docs = (uu___195_4614.docs);
            remaining_iface_decls = (uu___195_4614.remaining_iface_decls);
            syntax_only = (uu___195_4614.syntax_only)
          }
let fail_or env lookup lid =
  let uu____4639 = lookup lid in
  match uu____4639 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4645  ->
             match uu____4645 with
             | (lid1,uu____4649) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4656 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4656
               (FStar_Ident.range_of_lid lid) in
           let uu____4657 = resolve_module_name env modul true in
           match uu____4657 with
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
  let uu____4684 = lookup id in
  match uu____4684 with
  | None  ->
      Prims.raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r