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
      let uu___172_390 = env in
      {
        curmodule = (uu___172_390.curmodule);
        curmonad = (uu___172_390.curmonad);
        modules = (uu___172_390.modules);
        scope_mods = (uu___172_390.scope_mods);
        exported_ids = (uu___172_390.exported_ids);
        trans_exported_ids = (uu___172_390.trans_exported_ids);
        includes = (uu___172_390.includes);
        sigaccum = (uu___172_390.sigaccum);
        sigmap = (uu___172_390.sigmap);
        iface = b;
        admitted_iface = (uu___172_390.admitted_iface);
        expect_typ = (uu___172_390.expect_typ);
        docs = (uu___172_390.docs);
        remaining_iface_decls = (uu___172_390.remaining_iface_decls);
        syntax_only = (uu___172_390.syntax_only)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___173_400 = e in
      {
        curmodule = (uu___173_400.curmodule);
        curmonad = (uu___173_400.curmonad);
        modules = (uu___173_400.modules);
        scope_mods = (uu___173_400.scope_mods);
        exported_ids = (uu___173_400.exported_ids);
        trans_exported_ids = (uu___173_400.trans_exported_ids);
        includes = (uu___173_400.includes);
        sigaccum = (uu___173_400.sigaccum);
        sigmap = (uu___173_400.sigmap);
        iface = (uu___173_400.iface);
        admitted_iface = b;
        expect_typ = (uu___173_400.expect_typ);
        docs = (uu___173_400.docs);
        remaining_iface_decls = (uu___173_400.remaining_iface_decls);
        syntax_only = (uu___173_400.syntax_only)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___174_410 = e in
      {
        curmodule = (uu___174_410.curmodule);
        curmonad = (uu___174_410.curmonad);
        modules = (uu___174_410.modules);
        scope_mods = (uu___174_410.scope_mods);
        exported_ids = (uu___174_410.exported_ids);
        trans_exported_ids = (uu___174_410.trans_exported_ids);
        includes = (uu___174_410.includes);
        sigaccum = (uu___174_410.sigaccum);
        sigmap = (uu___174_410.sigmap);
        iface = (uu___174_410.iface);
        admitted_iface = (uu___174_410.admitted_iface);
        expect_typ = b;
        docs = (uu___174_410.docs);
        remaining_iface_decls = (uu___174_410.remaining_iface_decls);
        syntax_only = (uu___174_410.syntax_only)
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
      let uu___175_446 = e in
      {
        curmodule = (Some l);
        curmonad = (uu___175_446.curmonad);
        modules = (uu___175_446.modules);
        scope_mods = (uu___175_446.scope_mods);
        exported_ids = (uu___175_446.exported_ids);
        trans_exported_ids = (uu___175_446.trans_exported_ids);
        includes = (uu___175_446.includes);
        sigaccum = (uu___175_446.sigaccum);
        sigmap = (uu___175_446.sigmap);
        iface = (uu___175_446.iface);
        admitted_iface = (uu___175_446.admitted_iface);
        expect_typ = (uu___175_446.expect_typ);
        docs = (uu___175_446.docs);
        remaining_iface_decls = (uu___175_446.remaining_iface_decls);
        syntax_only = (uu___175_446.syntax_only)
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
            let uu___176_548 = env in
            {
              curmodule = (uu___176_548.curmodule);
              curmonad = (uu___176_548.curmonad);
              modules = (uu___176_548.modules);
              scope_mods = (uu___176_548.scope_mods);
              exported_ids = (uu___176_548.exported_ids);
              trans_exported_ids = (uu___176_548.trans_exported_ids);
              includes = (uu___176_548.includes);
              sigaccum = (uu___176_548.sigaccum);
              sigmap = (uu___176_548.sigmap);
              iface = (uu___176_548.iface);
              admitted_iface = (uu___176_548.admitted_iface);
              expect_typ = (uu___176_548.expect_typ);
              docs = (uu___176_548.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___176_548.syntax_only)
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
      let uu___177_576 = env in
      {
        curmodule = (uu___177_576.curmodule);
        curmonad = (uu___177_576.curmonad);
        modules = (uu___177_576.modules);
        scope_mods = (uu___177_576.scope_mods);
        exported_ids = (uu___177_576.exported_ids);
        trans_exported_ids = (uu___177_576.trans_exported_ids);
        includes = (uu___177_576.includes);
        sigaccum = (uu___177_576.sigaccum);
        sigmap = (uu___177_576.sigmap);
        iface = (uu___177_576.iface);
        admitted_iface = (uu___177_576.admitted_iface);
        expect_typ = (uu___177_576.expect_typ);
        docs = (uu___177_576.docs);
        remaining_iface_decls = (uu___177_576.remaining_iface_decls);
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
        let uu___178_634 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___178_634.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___179_635 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___179_635.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___179_635.FStar_Syntax_Syntax.sort)
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
let option_of_cont k_ignore uu___145_780 =
  match uu___145_780 with
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
  fun uu___146_866  ->
    match uu___146_866 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___147_915 =
    match uu___147_915 with
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
  fun uu___148_973  ->
    match uu___148_973 with | Exported_id_field  -> true | uu____974 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___149_1063 =
    match uu___149_1063 with
    | (id',uu____1065,uu____1066) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___150_1070 =
    match uu___150_1070 with
    | (id',uu____1072,uu____1073) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1076 = current_module env in FStar_Ident.ids_of_lid uu____1076 in
  let proc uu___151_1081 =
    match uu___151_1081 with
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
  let rec aux uu___152_1098 =
    match uu___152_1098 with
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
        let rec aux uu___153_1352 =
          match uu___153_1352 with
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
              raise uu____1392))
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
        (fun uu___154_1418  ->
           match uu___154_1418 with
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
let cont_of_option k_none uu___155_1690 =
  match uu___155_1690 with | Some v1 -> Cont_ok v1 | None  -> k_none
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
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1801,uu____1802,uu____1803,l,uu____1805,uu____1806) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___156_1811  ->
               match uu___156_1811 with
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
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> foundname option =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___160_1879 =
            match uu___160_1879 with
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
                               (fun uu___157_1942  ->
                                  match uu___157_1942 with
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
                                      (fun uu___158_1949  ->
                                         match uu___158_1949 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1952 -> false)))) in
                         if uu____1947
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____1954 =
                         FStar_Util.find_map quals
                           (fun uu___159_1956  ->
                              match uu___159_1956 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1959 -> None) in
                       (match uu____1954 with
                        | Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
                        | uu____1971 ->
                            let uu____1973 =
                              let uu____1974 =
                                let uu____1977 =
                                  let uu____1978 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____1978 in
                                (uu____1977, false) in
                              Term_name uu____1974 in
                            Some uu____1973)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1982 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1989 -> None) in
          let k_local_binding r =
            let uu____2001 =
              let uu____2002 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____2002 in
            Some uu____2001 in
          let k_rec_binding uu____2012 =
            match uu____2012 with
            | (id,l,dd) ->
                let uu____2020 =
                  let uu____2021 =
                    let uu____2024 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____2024, false) in
                  Term_name uu____2021 in
                Some uu____2020 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2028 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2028 with
                 | Some f -> Some (Term_name f)
                 | uu____2038 -> None)
            | uu____2042 -> None in
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
        let uu____2062 = try_lookup_name true exclude_interf env lid in
        match uu____2062 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____2071 -> None
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2082 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2082 with | Some (o,l1) -> Some l1 | uu____2091 -> None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list) option
  =
  fun env  ->
    fun l  ->
      let uu____2105 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2105 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2114;
             FStar_Syntax_Syntax.sigquals = uu____2115;
             FStar_Syntax_Syntax.sigmeta = uu____2116;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2126;
             FStar_Syntax_Syntax.sigquals = uu____2127;
             FStar_Syntax_Syntax.sigmeta = uu____2128;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____2137,uu____2138,uu____2139,uu____2140,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2142;
             FStar_Syntax_Syntax.sigquals = uu____2143;
             FStar_Syntax_Syntax.sigmeta = uu____2144;_},l1)
          -> Some (l1, cattributes)
      | uu____2155 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl option =
  fun env  ->
    fun l  ->
      let uu____2169 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2169 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2175;
             FStar_Syntax_Syntax.sigquals = uu____2176;
             FStar_Syntax_Syntax.sigmeta = uu____2177;_},uu____2178)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2183;
             FStar_Syntax_Syntax.sigquals = uu____2184;
             FStar_Syntax_Syntax.sigmeta = uu____2185;_},uu____2186)
          -> Some ne
      | uu____2190 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2200 = try_lookup_effect_name env lid in
      match uu____2200 with | None  -> false | Some uu____2202 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2210 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2210 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____2216,uu____2217,uu____2218,uu____2219);
             FStar_Syntax_Syntax.sigrng = uu____2220;
             FStar_Syntax_Syntax.sigquals = uu____2221;
             FStar_Syntax_Syntax.sigmeta = uu____2222;_},uu____2223)
          ->
          let rec aux new_name =
            let uu____2234 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2234 with
            | None  -> None
            | Some (s,uu____2244) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____2249,uu____2250,uu____2251,cmp,uu____2253) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2257 -> None) in
          aux l'
      | Some (uu____2258,l') -> Some l'
      | uu____2262 -> None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___161_2283 =
        match uu___161_2283 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2288,uu____2289,uu____2290);
             FStar_Syntax_Syntax.sigrng = uu____2291;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2293;_},uu____2294)
            -> Some quals
        | uu____2297 -> None in
      let uu____2301 =
        resolve_in_open_namespaces' env lid (fun uu____2305  -> None)
          (fun uu____2307  -> None) k_global_def in
      match uu____2301 with | Some quals -> quals | uu____2313 -> []
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul option =
  fun env  ->
    fun path  ->
      let uu____2325 =
        FStar_List.tryFind
          (fun uu____2331  ->
             match uu____2331 with
             | (mlid,modul) ->
                 let uu____2336 = FStar_Ident.path_of_lid mlid in
                 uu____2336 = path) env.modules in
      match uu____2325 with
      | Some (uu____2340,modul) -> Some modul
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___162_2362 =
        match uu___162_2362 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2366,lbs),uu____2368,uu____2369);
             FStar_Syntax_Syntax.sigrng = uu____2370;
             FStar_Syntax_Syntax.sigquals = uu____2371;
             FStar_Syntax_Syntax.sigmeta = uu____2372;_},uu____2373)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2385 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2385
        | uu____2386 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2389  -> None)
        (fun uu____2390  -> None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___163_2409 =
        match uu___163_2409 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2416,uu____2417);
             FStar_Syntax_Syntax.sigrng = uu____2418;
             FStar_Syntax_Syntax.sigquals = uu____2419;
             FStar_Syntax_Syntax.sigmeta = uu____2420;_},uu____2421)
            ->
            FStar_Util.find_map (snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2437 -> None)
        | uu____2442 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2449  -> None)
        (fun uu____2452  -> None) k_global_def
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
          let uu____2479 = try_lookup_name any_val exclude_interf env lid in
          match uu____2479 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2488 -> None
let try_lookup_lid:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident option =
  fun env  ->
    fun l  ->
      let uu____2508 = try_lookup_lid env l in
      match uu____2508 with
      | None  -> None
      | Some (e,uu____2516) ->
          let uu____2519 =
            let uu____2520 = FStar_Syntax_Subst.compress e in
            uu____2520.FStar_Syntax_Syntax.n in
          (match uu____2519 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2529 -> None)
let try_lookup_lid_no_resolve:
  env -> FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___180_2540 = env in
        {
          curmodule = (uu___180_2540.curmodule);
          curmonad = (uu___180_2540.curmonad);
          modules = (uu___180_2540.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___180_2540.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___180_2540.sigaccum);
          sigmap = (uu___180_2540.sigmap);
          iface = (uu___180_2540.iface);
          admitted_iface = (uu___180_2540.admitted_iface);
          expect_typ = (uu___180_2540.expect_typ);
          docs = (uu___180_2540.docs);
          remaining_iface_decls = (uu___180_2540.remaining_iface_decls);
          syntax_only = (uu___180_2540.syntax_only)
        } in
      try_lookup_lid env' l
let try_lookup_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___165_2564 =
        match uu___165_2564 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2568,uu____2569,uu____2570);
             FStar_Syntax_Syntax.sigrng = uu____2571;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____2573;_},uu____2574)
            ->
            let uu____2576 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___164_2578  ->
                      match uu___164_2578 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2579 -> false)) in
            if uu____2576
            then
              let uu____2581 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2581
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2583;
             FStar_Syntax_Syntax.sigrng = uu____2584;
             FStar_Syntax_Syntax.sigquals = uu____2585;
             FStar_Syntax_Syntax.sigmeta = uu____2586;_},uu____2587)
            ->
            let uu____2596 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2596
        | uu____2597 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2600  -> None)
        (fun uu____2601  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___166_2620 =
        match uu___166_2620 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2625,uu____2626,uu____2627,uu____2628,datas,uu____2630);
             FStar_Syntax_Syntax.sigrng = uu____2631;
             FStar_Syntax_Syntax.sigquals = uu____2632;
             FStar_Syntax_Syntax.sigmeta = uu____2633;_},uu____2634)
            -> Some datas
        | uu____2641 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2646  -> None)
        (fun uu____2648  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____2682 =
    let uu____2683 =
      let uu____2686 =
        let uu____2688 = FStar_ST.read record_cache in
        FStar_List.hd uu____2688 in
      let uu____2696 = FStar_ST.read record_cache in uu____2686 :: uu____2696 in
    FStar_ST.write record_cache uu____2683 in
  let pop1 uu____2711 =
    let uu____2712 =
      let uu____2715 = FStar_ST.read record_cache in FStar_List.tl uu____2715 in
    FStar_ST.write record_cache uu____2712 in
  let peek uu____2731 =
    let uu____2732 = FStar_ST.read record_cache in FStar_List.hd uu____2732 in
  let insert r =
    let uu____2744 =
      let uu____2747 = let uu____2749 = peek () in r :: uu____2749 in
      let uu____2751 =
        let uu____2754 = FStar_ST.read record_cache in
        FStar_List.tl uu____2754 in
      uu____2747 :: uu____2751 in
    FStar_ST.write record_cache uu____2744 in
  let commit1 uu____2770 =
    let uu____2771 = FStar_ST.read record_cache in
    match uu____2771 with
    | hd1::uu____2779::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2792 -> failwith "Impossible" in
  let filter1 uu____2798 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____2805 =
           let uu____2808 = FStar_ST.read record_cache in filtered ::
             uu____2808 in
         FStar_ST.write record_cache uu____2805) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____2882 = record_cache_aux_with_filter in
  match uu____2882 with | (aux,uu____2920) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____2959 = record_cache_aux_with_filter in
  match uu____2959 with | (uu____2982,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____3022 = record_cache_aux in
  match uu____3022 with
  | (push1,uu____3042,uu____3043,uu____3044,uu____3045) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3070 = record_cache_aux in
  match uu____3070 with
  | (uu____3089,pop1,uu____3091,uu____3092,uu____3093) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____3119 = record_cache_aux in
  match uu____3119 with
  | (uu____3139,uu____3140,peek,uu____3142,uu____3143) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____3168 = record_cache_aux in
  match uu____3168 with
  | (uu____3187,uu____3188,uu____3189,insert,uu____3191) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____3216 = record_cache_aux in
  match uu____3216 with
  | (uu____3235,uu____3236,uu____3237,uu____3238,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3278) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___167_3287  ->
                   match uu___167_3287 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____3290 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___168_3298  ->
                      match uu___168_3298 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3300,uu____3301,uu____3302,uu____3303,uu____3304);
                          FStar_Syntax_Syntax.sigrng = uu____3305;
                          FStar_Syntax_Syntax.sigquals = uu____3306;
                          FStar_Syntax_Syntax.sigmeta = uu____3307;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3311 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___169_3313  ->
                    match uu___169_3313 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____3317,uu____3318,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____3320;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____3322;_} ->
                        let uu____3327 =
                          let uu____3328 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3328 in
                        (match uu____3327 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3332,t,uu____3334,uu____3335,uu____3336);
                             FStar_Syntax_Syntax.sigrng = uu____3337;
                             FStar_Syntax_Syntax.sigquals = uu____3338;
                             FStar_Syntax_Syntax.sigmeta = uu____3339;_} ->
                             let uu____3343 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3343 with
                              | (formals,uu____3352) ->
                                  let is_rec = is_record typename_quals in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3378  ->
                                            match uu____3378 with
                                            | (x,q) ->
                                                let uu____3386 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3386
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3417  ->
                                            match uu____3417 with
                                            | (x,q) ->
                                                let uu____3426 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____3426,
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
                                  ((let uu____3438 =
                                      let uu____3440 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3440 in
                                    FStar_ST.write new_globs uu____3438);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3456 =
                                            match uu____3456 with
                                            | (id,uu____3462) ->
                                                let modul =
                                                  let uu____3468 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3468.FStar_Ident.str in
                                                let uu____3469 =
                                                  get_exported_id_set e modul in
                                                (match uu____3469 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____3485 =
                                                         let uu____3486 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3486 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3485);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3493 =
                                                               let uu____3494
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____3494.FStar_Ident.ident in
                                                             uu____3493.FStar_Ident.idText in
                                                           let uu____3496 =
                                                             let uu____3497 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3497 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3496))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3510 -> ())
                    | uu____3511 -> ()))
        | uu____3512 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3525 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3525 with
        | (ns,id) ->
            let uu____3535 = peek_record_cache () in
            FStar_Util.find_map uu____3535
              (fun record  ->
                 let uu____3538 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3541  -> None) uu____3538) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3542  -> Cont_ignore) (fun uu____3543  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3546 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3546)
        (fun k  -> fun uu____3549  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc option =
  fun env  ->
    fun fieldname  ->
      let uu____3558 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3558 with
      | Some r when r.is_record -> Some r
      | uu____3562 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3573 = try_lookup_record_by_field_name env lid in
        match uu____3573 with
        | Some record' when
            let uu____3576 =
              let uu____3577 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3577 in
            let uu____3579 =
              let uu____3580 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3580 in
            uu____3576 = uu____3579 ->
            let uu____3582 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3584  -> Cont_ok ()) in
            (match uu____3582 with
             | Cont_ok uu____3585 -> true
             | uu____3586 -> false)
        | uu____3588 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) option =
  fun env  ->
    fun fieldname  ->
      let uu____3599 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3599 with
      | Some r ->
          let uu____3605 =
            let uu____3608 =
              let uu____3609 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3609
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3608, (r.is_record)) in
          Some uu____3605
      | uu____3612 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3621  ->
    let uu____3622 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3622
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3633  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___170_3642  ->
      match uu___170_3642 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___171_3662 =
            match uu___171_3662 with
            | Rec_binding uu____3663 -> true
            | uu____3664 -> false in
          let this_env =
            let uu___181_3666 = env in
            let uu____3667 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___181_3666.curmodule);
              curmonad = (uu___181_3666.curmonad);
              modules = (uu___181_3666.modules);
              scope_mods = uu____3667;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___181_3666.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___181_3666.sigaccum);
              sigmap = (uu___181_3666.sigmap);
              iface = (uu___181_3666.iface);
              admitted_iface = (uu___181_3666.admitted_iface);
              expect_typ = (uu___181_3666.expect_typ);
              docs = (uu___181_3666.docs);
              remaining_iface_decls = (uu___181_3666.remaining_iface_decls);
              syntax_only = (uu___181_3666.syntax_only)
            } in
          let uu____3669 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3669 with | None  -> true | Some uu____3675 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___182_3686 = env in
      {
        curmodule = (uu___182_3686.curmodule);
        curmonad = (uu___182_3686.curmonad);
        modules = (uu___182_3686.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___182_3686.exported_ids);
        trans_exported_ids = (uu___182_3686.trans_exported_ids);
        includes = (uu___182_3686.includes);
        sigaccum = (uu___182_3686.sigaccum);
        sigmap = (uu___182_3686.sigmap);
        iface = (uu___182_3686.iface);
        admitted_iface = (uu___182_3686.admitted_iface);
        expect_typ = (uu___182_3686.expect_typ);
        docs = (uu___182_3686.docs);
        remaining_iface_decls = (uu___182_3686.remaining_iface_decls);
        syntax_only = (uu___182_3686.syntax_only)
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
        let uu____3725 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____3725
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
          | Some (se,uu____3745) ->
              let uu____3748 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____3748 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____3753 =
          let uu____3754 =
            let uu____3757 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____3757, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____3754 in
        raise uu____3753 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____3764 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3769 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3775 -> (true, true)
          | uu____3780 -> (false, false) in
        match uu____3764 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____3785 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3788 =
                     let uu____3789 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____3789 in
                   if uu____3788 then Some l else None) in
            (match uu____3785 with
             | Some l when
                 let uu____3793 = FStar_Options.interactive () in
                 Prims.op_Negation uu____3793 -> err1 l
             | uu____3794 ->
                 (extract_record env globals s;
                  (let uu___183_3799 = env in
                   {
                     curmodule = (uu___183_3799.curmodule);
                     curmonad = (uu___183_3799.curmonad);
                     modules = (uu___183_3799.modules);
                     scope_mods = (uu___183_3799.scope_mods);
                     exported_ids = (uu___183_3799.exported_ids);
                     trans_exported_ids = (uu___183_3799.trans_exported_ids);
                     includes = (uu___183_3799.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___183_3799.sigmap);
                     iface = (uu___183_3799.iface);
                     admitted_iface = (uu___183_3799.admitted_iface);
                     expect_typ = (uu___183_3799.expect_typ);
                     docs = (uu___183_3799.docs);
                     remaining_iface_decls =
                       (uu___183_3799.remaining_iface_decls);
                     syntax_only = (uu___183_3799.syntax_only)
                   }))) in
      let env2 =
        let uu___184_3801 = env1 in
        let uu____3802 = FStar_ST.read globals in
        {
          curmodule = (uu___184_3801.curmodule);
          curmonad = (uu___184_3801.curmonad);
          modules = (uu___184_3801.modules);
          scope_mods = uu____3802;
          exported_ids = (uu___184_3801.exported_ids);
          trans_exported_ids = (uu___184_3801.trans_exported_ids);
          includes = (uu___184_3801.includes);
          sigaccum = (uu___184_3801.sigaccum);
          sigmap = (uu___184_3801.sigmap);
          iface = (uu___184_3801.iface);
          admitted_iface = (uu___184_3801.admitted_iface);
          expect_typ = (uu___184_3801.expect_typ);
          docs = (uu___184_3801.docs);
          remaining_iface_decls = (uu___184_3801.remaining_iface_decls);
          syntax_only = (uu___184_3801.syntax_only)
        } in
      let uu____3807 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3821) ->
            let uu____3826 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____3826)
        | uu____3840 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____3807 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3870  ->
                   match uu____3870 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3881 =
                                  let uu____3883 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3883 in
                                FStar_ST.write globals uu____3881);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3892 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____3892.FStar_Ident.str in
                                    ((let uu____3894 =
                                        get_exported_id_set env3 modul in
                                      match uu____3894 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____3909 =
                                            let uu____3910 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3910 in
                                          FStar_ST.write my_exported_ids
                                            uu____3909
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
              let uu___185_3922 = env3 in
              let uu____3923 = FStar_ST.read globals in
              {
                curmodule = (uu___185_3922.curmodule);
                curmonad = (uu___185_3922.curmonad);
                modules = (uu___185_3922.modules);
                scope_mods = uu____3923;
                exported_ids = (uu___185_3922.exported_ids);
                trans_exported_ids = (uu___185_3922.trans_exported_ids);
                includes = (uu___185_3922.includes);
                sigaccum = (uu___185_3922.sigaccum);
                sigmap = (uu___185_3922.sigmap);
                iface = (uu___185_3922.iface);
                admitted_iface = (uu___185_3922.admitted_iface);
                expect_typ = (uu___185_3922.expect_typ);
                docs = (uu___185_3922.docs);
                remaining_iface_decls = (uu___185_3922.remaining_iface_decls);
                syntax_only = (uu___185_3922.syntax_only)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3934 =
        let uu____3937 = resolve_module_name env ns false in
        match uu____3937 with
        | None  ->
            let modules = env.modules in
            let uu____3945 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3951  ->
                      match uu____3951 with
                      | (m,uu____3955) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____3945
            then (ns, Open_namespace)
            else
              (let uu____3959 =
                 let uu____3960 =
                   let uu____3963 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____3963, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____3960 in
               raise uu____3959)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____3934 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____3977 = resolve_module_name env ns false in
      match uu____3977 with
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____3983 = current_module env1 in
              uu____3983.FStar_Ident.str in
            (let uu____3985 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____3985 with
             | None  -> ()
             | Some incl ->
                 let uu____3998 =
                   let uu____4000 = FStar_ST.read incl in ns1 :: uu____4000 in
                 FStar_ST.write incl uu____3998);
            (match () with
             | () ->
                 let uu____4008 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____4008 with
                  | Some ns_trans_exports ->
                      ((let uu____4021 =
                          let uu____4032 = get_exported_id_set env1 curmod in
                          let uu____4037 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____4032, uu____4037) in
                        match uu____4021 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____4077 = ns_trans_exports k in
                                FStar_ST.read uu____4077 in
                              let ex = cur_exports k in
                              (let uu____4086 =
                                 let uu____4087 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____4087 ns_ex in
                               FStar_ST.write ex uu____4086);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____4097 =
                                     let uu____4098 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____4098 ns_ex in
                                   FStar_ST.write trans_ex uu____4097) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____4104 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____4118 =
                        let uu____4119 =
                          let uu____4122 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____4122, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____4119 in
                      raise uu____4118))))
      | uu____4123 ->
          let uu____4125 =
            let uu____4126 =
              let uu____4129 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____4129, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____4126 in
          raise uu____4125
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____4139 = module_is_defined env l in
        if uu____4139
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____4142 =
             let uu____4143 =
               let uu____4146 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____4146, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____4143 in
           raise uu____4142)
let push_doc: env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc option -> env
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____4160 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____4160 with
              | None  -> ()
              | Some old_doc ->
                  let uu____4163 =
                    let uu____4164 = FStar_Ident.string_of_lid l in
                    let uu____4165 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____4166 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____4164 uu____4165 uu____4166 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____4163);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                let uu____4175 = try_lookup_lid env l in
                (match uu____4175 with
                 | None  ->
                     ((let uu____4182 =
                         let uu____4183 = FStar_Options.interactive () in
                         Prims.op_Negation uu____4183 in
                       if uu____4182
                       then
                         let uu____4184 =
                           let uu____4185 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____4186 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____4185 uu____4186 in
                         FStar_Util.print_string uu____4184
                       else ());
                      (let quals = FStar_Syntax_Syntax.Assumption ::
                         (se.FStar_Syntax_Syntax.sigquals) in
                       FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                         ((let uu___186_4192 = se in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___186_4192.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___186_4192.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals = quals;
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___186_4192.FStar_Syntax_Syntax.sigmeta)
                           }), false)))
                 | Some uu____4193 -> ())
            | uu____4198 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4210) ->
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
                                (lid,uu____4218,uu____4219,uu____4220,uu____4221,uu____4222)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4227 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4230,uu____4231) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4235,lbs),uu____4237,uu____4238) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4251 =
                               let uu____4252 =
                                 let uu____4253 =
                                   let uu____4258 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4258.FStar_Syntax_Syntax.fv_name in
                                 uu____4253.FStar_Syntax_Syntax.v in
                               uu____4252.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4251))
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
                               let uu____4268 =
                                 let uu____4273 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4273.FStar_Syntax_Syntax.fv_name in
                               uu____4268.FStar_Syntax_Syntax.v in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals in
                             let decl =
                               let uu___187_4280 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___187_4280.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___187_4280.FStar_Syntax_Syntax.sigmeta)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4287 -> ()));
      (let curmod =
         let uu____4289 = current_module env in uu____4289.FStar_Ident.str in
       (let uu____4291 =
          let uu____4302 = get_exported_id_set env curmod in
          let uu____4307 = get_trans_exported_id_set env curmod in
          (uu____4302, uu____4307) in
        match uu____4291 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4347 = cur_ex eikind in FStar_ST.read uu____4347 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4355 =
                let uu____4356 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4356 in
              FStar_ST.write cur_trans_ex_set_ref uu____4355 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4362 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___188_4374 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___188_4374.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___188_4374.exported_ids);
                    trans_exported_ids = (uu___188_4374.trans_exported_ids);
                    includes = (uu___188_4374.includes);
                    sigaccum = [];
                    sigmap = (uu___188_4374.sigmap);
                    iface = (uu___188_4374.iface);
                    admitted_iface = (uu___188_4374.admitted_iface);
                    expect_typ = (uu___188_4374.expect_typ);
                    docs = (uu___188_4374.docs);
                    remaining_iface_decls =
                      (uu___188_4374.remaining_iface_decls);
                    syntax_only = (uu___188_4374.syntax_only)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4387 =
       let uu____4389 = FStar_ST.read stack in env :: uu____4389 in
     FStar_ST.write stack uu____4387);
    (let uu___189_4397 = env in
     let uu____4398 = FStar_Util.smap_copy (sigmap env) in
     let uu____4404 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___189_4397.curmodule);
       curmonad = (uu___189_4397.curmonad);
       modules = (uu___189_4397.modules);
       scope_mods = (uu___189_4397.scope_mods);
       exported_ids = (uu___189_4397.exported_ids);
       trans_exported_ids = (uu___189_4397.trans_exported_ids);
       includes = (uu___189_4397.includes);
       sigaccum = (uu___189_4397.sigaccum);
       sigmap = uu____4398;
       iface = (uu___189_4397.iface);
       admitted_iface = (uu___189_4397.admitted_iface);
       expect_typ = (uu___189_4397.expect_typ);
       docs = uu____4404;
       remaining_iface_decls = (uu___189_4397.remaining_iface_decls);
       syntax_only = (uu___189_4397.syntax_only)
     })
let pop: Prims.unit -> env =
  fun uu____4408  ->
    let uu____4409 = FStar_ST.read stack in
    match uu____4409 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4422 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4428 = FStar_ST.read stack in
     match uu____4428 with
     | uu____4433::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4440 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4447  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4459 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4461 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4479 = FStar_Util.smap_try_find sm' k in
              match uu____4479 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___190_4495 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___190_4495.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___190_4495.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___190_4495.FStar_Syntax_Syntax.sigmeta)
                          }
                      | uu____4496 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4499 -> ()));
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
            (let uu____4543 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4543);
            (match () with
             | () ->
                 ((let uu____4548 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4548);
                  (match () with
                   | () ->
                       ((let uu____4553 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4553);
                        (match () with
                         | () ->
                             let uu___191_4562 = env1 in
                             let uu____4563 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___191_4562.curmonad);
                               modules = (uu___191_4562.modules);
                               scope_mods = uu____4563;
                               exported_ids = (uu___191_4562.exported_ids);
                               trans_exported_ids =
                                 (uu___191_4562.trans_exported_ids);
                               includes = (uu___191_4562.includes);
                               sigaccum = (uu___191_4562.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___191_4562.expect_typ);
                               docs = (uu___191_4562.docs);
                               remaining_iface_decls =
                                 (uu___191_4562.remaining_iface_decls);
                               syntax_only = (uu___191_4562.syntax_only)
                             }))))) in
          let uu____4566 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4578  ->
                    match uu____4578 with
                    | (l,uu____4582) -> FStar_Ident.lid_equals l mname)) in
          match uu____4566 with
          | None  -> let uu____4587 = prep env in (uu____4587, false)
          | Some (uu____4588,m) ->
              ((let uu____4593 =
                  (let uu____4594 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4594) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4593
                then
                  let uu____4595 =
                    let uu____4596 =
                      let uu____4599 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4599, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4596 in
                  raise uu____4595
                else ());
               (let uu____4601 = let uu____4602 = push env in prep uu____4602 in
                (uu____4601, true)))
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
          let uu___192_4610 = env in
          {
            curmodule = (uu___192_4610.curmodule);
            curmonad = (Some mname);
            modules = (uu___192_4610.modules);
            scope_mods = (uu___192_4610.scope_mods);
            exported_ids = (uu___192_4610.exported_ids);
            trans_exported_ids = (uu___192_4610.trans_exported_ids);
            includes = (uu___192_4610.includes);
            sigaccum = (uu___192_4610.sigaccum);
            sigmap = (uu___192_4610.sigmap);
            iface = (uu___192_4610.iface);
            admitted_iface = (uu___192_4610.admitted_iface);
            expect_typ = (uu___192_4610.expect_typ);
            docs = (uu___192_4610.docs);
            remaining_iface_decls = (uu___192_4610.remaining_iface_decls);
            syntax_only = (uu___192_4610.syntax_only)
          }
let fail_or env lookup lid =
  let uu____4635 = lookup lid in
  match uu____4635 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4641  ->
             match uu____4641 with
             | (lid1,uu____4645) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4652 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4652
               (FStar_Ident.range_of_lid lid) in
           let uu____4653 = resolve_module_name env modul true in
           match uu____4653 with
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
  let uu____4680 = lookup id in
  match uu____4680 with
  | None  ->
      raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r