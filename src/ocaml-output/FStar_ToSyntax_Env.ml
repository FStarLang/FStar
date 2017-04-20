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
    (FStar_Ident.lident* FStar_Parser_AST.decl Prims.list) Prims.list;}
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ* Prims.bool)
  | Eff_name of (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident)
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____343 -> false
let __proj__Term_name__item___0:
  foundname -> (FStar_Syntax_Syntax.typ* Prims.bool) =
  fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____363 -> false
let __proj__Eff_name__item___0:
  foundname -> (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0
let set_iface: env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___171_383 = env in
      {
        curmodule = (uu___171_383.curmodule);
        curmonad = (uu___171_383.curmonad);
        modules = (uu___171_383.modules);
        scope_mods = (uu___171_383.scope_mods);
        exported_ids = (uu___171_383.exported_ids);
        trans_exported_ids = (uu___171_383.trans_exported_ids);
        includes = (uu___171_383.includes);
        sigaccum = (uu___171_383.sigaccum);
        sigmap = (uu___171_383.sigmap);
        iface = b;
        admitted_iface = (uu___171_383.admitted_iface);
        expect_typ = (uu___171_383.expect_typ);
        docs = (uu___171_383.docs);
        remaining_iface_decls = (uu___171_383.remaining_iface_decls)
      }
let iface: env -> Prims.bool = fun e  -> e.iface
let set_admitted_iface: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___172_393 = e in
      {
        curmodule = (uu___172_393.curmodule);
        curmonad = (uu___172_393.curmonad);
        modules = (uu___172_393.modules);
        scope_mods = (uu___172_393.scope_mods);
        exported_ids = (uu___172_393.exported_ids);
        trans_exported_ids = (uu___172_393.trans_exported_ids);
        includes = (uu___172_393.includes);
        sigaccum = (uu___172_393.sigaccum);
        sigmap = (uu___172_393.sigmap);
        iface = (uu___172_393.iface);
        admitted_iface = b;
        expect_typ = (uu___172_393.expect_typ);
        docs = (uu___172_393.docs);
        remaining_iface_decls = (uu___172_393.remaining_iface_decls)
      }
let admitted_iface: env -> Prims.bool = fun e  -> e.admitted_iface
let set_expect_typ: env -> Prims.bool -> env =
  fun e  ->
    fun b  ->
      let uu___173_403 = e in
      {
        curmodule = (uu___173_403.curmodule);
        curmonad = (uu___173_403.curmonad);
        modules = (uu___173_403.modules);
        scope_mods = (uu___173_403.scope_mods);
        exported_ids = (uu___173_403.exported_ids);
        trans_exported_ids = (uu___173_403.trans_exported_ids);
        includes = (uu___173_403.includes);
        sigaccum = (uu___173_403.sigaccum);
        sigmap = (uu___173_403.sigmap);
        iface = (uu___173_403.iface);
        admitted_iface = (uu___173_403.admitted_iface);
        expect_typ = b;
        docs = (uu___173_403.docs);
        remaining_iface_decls = (uu___173_403.remaining_iface_decls)
      }
let expect_typ: env -> Prims.bool = fun e  -> e.expect_typ
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____416 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____416 with
      | None  -> []
      | Some exported_id_set ->
          let uu____420 =
            let uu____421 = exported_id_set Exported_id_term_type in
            FStar_ST.read uu____421 in
          FStar_All.pipe_right uu____420 FStar_Util.set_elements
let open_modules:
  env -> (FStar_Ident.lident* FStar_Syntax_Syntax.modul) Prims.list =
  fun e  -> e.modules
let set_current_module: env -> FStar_Ident.lident -> env =
  fun e  ->
    fun l  ->
      let uu___174_439 = e in
      {
        curmodule = (Some l);
        curmonad = (uu___174_439.curmonad);
        modules = (uu___174_439.modules);
        scope_mods = (uu___174_439.scope_mods);
        exported_ids = (uu___174_439.exported_ids);
        trans_exported_ids = (uu___174_439.trans_exported_ids);
        includes = (uu___174_439.includes);
        sigaccum = (uu___174_439.sigaccum);
        sigmap = (uu___174_439.sigmap);
        iface = (uu___174_439.iface);
        admitted_iface = (uu___174_439.admitted_iface);
        expect_typ = (uu___174_439.expect_typ);
        docs = (uu___174_439.docs);
        remaining_iface_decls = (uu___174_439.remaining_iface_decls)
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
      let uu____452 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____468  ->
                match uu____468 with
                | (m,uu____473) -> FStar_Ident.lid_equals l m)) in
      match uu____452 with
      | None  -> None
      | Some (uu____482,decls) -> Some decls
let set_iface_decls:
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____501 =
          FStar_List.partition
            (fun uu____515  ->
               match uu____515 with
               | (m,uu____520) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls in
        match uu____501 with
        | (uu____523,rest) ->
            let uu___175_541 = env in
            {
              curmodule = (uu___175_541.curmodule);
              curmonad = (uu___175_541.curmonad);
              modules = (uu___175_541.modules);
              scope_mods = (uu___175_541.scope_mods);
              exported_ids = (uu___175_541.exported_ids);
              trans_exported_ids = (uu___175_541.trans_exported_ids);
              includes = (uu___175_541.includes);
              sigaccum = (uu___175_541.sigaccum);
              sigmap = (uu___175_541.sigmap);
              iface = (uu___175_541.iface);
              admitted_iface = (uu___175_541.admitted_iface);
              expect_typ = (uu___175_541.expect_typ);
              docs = (uu___175_541.docs);
              remaining_iface_decls = ((l, ds) :: rest)
            }
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | None  -> let uu____556 = current_module env in qual uu____556 id
      | Some monad ->
          let uu____558 =
            let uu____559 = current_module env in qual uu____559 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____558 id
let new_sigmap uu____567 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____570  ->
    let uu____571 = new_sigmap () in
    let uu____573 = new_sigmap () in
    let uu____575 = new_sigmap () in
    let uu____581 = new_sigmap () in
    let uu____587 = new_sigmap () in
    {
      curmodule = None;
      curmonad = None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____571;
      trans_exported_ids = uu____573;
      includes = uu____575;
      sigaccum = [];
      sigmap = uu____581;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____587;
      remaining_iface_decls = []
    }
let sigmap: env -> (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap =
  fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____605  ->
         match uu____605 with
         | (m,uu____609) ->
             FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___176_617 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___176_617.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___177_618 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___177_618.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___177_618.FStar_Syntax_Syntax.sort)
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
        (fun uu____664  ->
           match uu____664 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____678 =
                   let uu____679 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____679 dd dq in
                 Some uu____678
               else None) in
    match t with | Some v1 -> Some (v1, false) | None  -> None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____709 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____733 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____744 -> false
let option_of_cont k_ignore uu___144_763 =
  match uu___144_763 with
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
        (fun uu____808  ->
           match uu____808 with
           | (f,uu____813) ->
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
  fun uu___145_849  ->
    match uu___145_849 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___146_898 =
    match uu___146_898 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
          let uu____906 = get_exported_id_set env mname in
          match uu____906 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____922 = mex eikind in FStar_ST.read uu____922 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____929 = FStar_Util.smap_try_find env.includes mname in
          match uu____929 with
          | None  -> []
          | Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
          then let uu____949 = qual modul id in find_in_module uu____949
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____952 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___147_956  ->
    match uu___147_956 with | Exported_id_field  -> true | uu____957 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___148_1046 =
    match uu___148_1046 with
    | (id',uu____1048,uu____1049) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___149_1053 =
    match uu___149_1053 with
    | (id',uu____1055,uu____1056) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____1059 = current_module env in FStar_Ident.ids_of_lid uu____1059 in
  let proc uu___150_1064 =
    match uu___150_1064 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____1069) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____1072 = FStar_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____1072 id
    | uu____1075 -> Cont_ignore in
  let rec aux uu___151_1081 =
    match uu___151_1081 with
    | a::q ->
        let uu____1087 = proc a in
        option_of_cont (fun uu____1089  -> aux q) uu____1087
    | [] ->
        let uu____1090 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____1092  -> None) uu____1090 in
  aux env.scope_mods
let found_local_binding r uu____1111 =
  match uu____1111 with
  | (id',x,mut) -> let uu____1118 = bv_to_name x r in (uu____1118, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____1155 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____1155 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found
let try_lookup_id:
  env ->
    FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  =
  fun env  ->
    fun id  ->
      let uu____1177 = unmangleOpName id in
      match uu____1177 with
      | Some f -> Some f
      | uu____1191 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1198 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1198) (fun uu____1203  -> Cont_fail)
            (fun uu____1206  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1213  -> fun uu____1214  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1221  -> fun uu____1222  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1274 ->
        let lid = qualify env id in
        let uu____1276 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____1276 with
         | Some r -> let uu____1289 = k_global_def lid r in Some uu____1289
         | None  -> None)
    | None  -> None in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1302 = current_module env in qual uu____1302 id in
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
           let uu____1311 = current_module env in
           FStar_Ident.lid_equals lid uu____1311)
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
        let rec aux uu___152_1335 =
          match uu___152_1335 with
          | [] ->
              let uu____1338 = module_is_defined env lid in
              if uu____1338 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1345 =
                  let uu____1347 = FStar_Ident.path_of_lid ns in
                  let uu____1349 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1347 uu____1349 in
                FStar_Ident.lid_of_path uu____1345
                  (FStar_Ident.range_of_lid lid) in
              let uu____1351 = module_is_defined env new_lid in
              if uu____1351 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1356 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1360::q -> aux q in
        aux env.scope_mods
let fail_if_curmodule:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____1372 =
          let uu____1373 = current_module env in
          FStar_Ident.lid_equals ns_resolved uu____1373 in
        if uu____1372
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Syntax_Const.prims_lid
           then ()
           else
             (let uu____1375 =
                let uu____1376 =
                  let uu____1379 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str in
                  (uu____1379, (FStar_Ident.range_of_lid ns_original)) in
                FStar_Errors.Error uu____1376 in
              Prims.raise uu____1375))
        else ()
let fail_if_qualified_by_curmodule: env -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____1387 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          let uu____1390 = resolve_module_name env modul_orig true in
          (match uu____1390 with
           | Some modul_res -> fail_if_curmodule env modul_orig modul_res
           | uu____1393 -> ())
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___153_1401  ->
           match uu___153_1401 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1403 -> false) env.scope_mods
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
                 let uu____1458 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____1458
                   (FStar_Util.map_option
                      (fun uu____1482  ->
                         match uu____1482 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____1499 =
          is_full_path &&
            (let uu____1500 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____1500) in
        if uu____1499
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1517 = aux ns_rev_prefix ns_last_id in
               (match uu____1517 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1630::uu____1631 ->
      let uu____1633 =
        let uu____1635 =
          let uu____1636 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____1636 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____1635 true in
      (match uu____1633 with
       | None  -> None
       | Some modul ->
           let uu____1639 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____1641  -> None) uu____1639)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___154_1656 =
  match uu___154_1656 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1735 = k_global_def lid1 def in cont_of_option k uu____1735 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1756 = k_local_binding l in
       cont_of_option Cont_fail uu____1756)
    (fun r  ->
       let uu____1759 = k_rec_binding r in
       cont_of_option Cont_fail uu____1759) (fun uu____1761  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual Prims.option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1767,uu____1768,uu____1769,l,uu____1771,quals,uu____1773) ->
        let qopt =
          FStar_Util.find_map quals
            (fun uu___155_1780  ->
               match uu___155_1780 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1782,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1789 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____1793,uu____1794,uu____1795,quals) -> None
    | uu____1799 -> None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1808 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____1812 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____1812 then Some fv else None) in
      FStar_All.pipe_right uu____1808 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1826 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____1826 ns)
let try_lookup_name:
  Prims.bool ->
    Prims.bool -> env -> FStar_Ident.lident -> foundname Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___159_1851 =
            match uu___159_1851 with
            | (uu____1855,true ) when exclude_interf -> None
            | (se,uu____1857) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1859 ->
                     let uu____1870 =
                       let uu____1871 =
                         let uu____1874 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____1874, false) in
                       Term_name uu____1871 in
                     Some uu____1870
                 | FStar_Syntax_Syntax.Sig_datacon uu____1875 ->
                     let uu____1885 =
                       let uu____1886 =
                         let uu____1889 =
                           let uu____1890 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1890 in
                         (uu____1889, false) in
                       Term_name uu____1886 in
                     Some uu____1885
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1892,lbs),uu____1894,uu____1895,uu____1896) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____1909 =
                       let uu____1910 =
                         let uu____1913 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____1913, false) in
                       Term_name uu____1910 in
                     Some uu____1909
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1915,uu____1916,quals) ->
                     let uu____1920 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___156_1922  ->
                                  match uu___156_1922 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1923 -> false))) in
                     if uu____1920
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____1927 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___157_1929  ->
                                         match uu___157_1929 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1932 -> false)))) in
                         if uu____1927
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____1934 =
                         FStar_Util.find_map quals
                           (fun uu___158_1936  ->
                              match uu___158_1936 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1939 -> None) in
                       (match uu____1934 with
                        | Some refl_monad ->
                            let refl_const =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reflect refl_monad)))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
                        | uu____1955 ->
                            let uu____1957 =
                              let uu____1958 =
                                let uu____1961 =
                                  let uu____1962 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____1962 in
                                (uu____1961, false) in
                              Term_name uu____1958 in
                            Some uu____1957)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1966 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1975 -> None) in
          let k_local_binding r =
            let uu____1987 =
              let uu____1988 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____1988 in
            Some uu____1987 in
          let k_rec_binding uu____1998 =
            match uu____1998 with
            | (id,l,dd) ->
                let uu____2006 =
                  let uu____2007 =
                    let uu____2010 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____2010, false) in
                  Term_name uu____2007 in
                Some uu____2006 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____2014 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____2014 with
                 | Some f -> Some (Term_name f)
                 | uu____2024 -> None)
            | uu____2028 -> None in
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
        let uu____2048 = try_lookup_name true exclude_interf env lid in
        match uu____2048 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____2057 -> None
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2068 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2068 with | Some (o,l1) -> Some l1 | uu____2077 -> None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list)
        Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____2091 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2091 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2100;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2109;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____2117,uu____2118,uu____2119,uu____2120,uu____2121,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____2123;_},l1)
          -> Some (l1, cattributes)
      | uu____2135 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      let uu____2149 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2149 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2155;_},uu____2156)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2160;_},uu____2161)
          -> Some ne
      | uu____2164 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2174 = try_lookup_effect_name env lid in
      match uu____2174 with | None  -> false | Some uu____2176 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2184 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____2184 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____2190,uu____2191,uu____2192,uu____2193,uu____2194);
             FStar_Syntax_Syntax.sigrng = uu____2195;_},uu____2196)
          ->
          let rec aux new_name =
            let uu____2208 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2208 with
            | None  -> None
            | Some (s,uu____2218) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____2223,uu____2224,uu____2225,cmp,uu____2227,uu____2228)
                     ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2234 -> None) in
          aux l'
      | Some (uu____2235,l') -> Some l'
      | uu____2239 -> None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___160_2260 =
        match uu___160_2260 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (lid2,uu____2266,uu____2267,quals);
             FStar_Syntax_Syntax.sigrng = uu____2269;_},uu____2270)
            -> Some quals
        | uu____2274 -> None in
      let uu____2278 =
        resolve_in_open_namespaces' env lid (fun uu____2282  -> None)
          (fun uu____2284  -> None) k_global_def in
      match uu____2278 with | Some quals -> quals | uu____2290 -> []
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul Prims.option =
  fun env  ->
    fun path  ->
      let uu____2302 =
        FStar_List.tryFind
          (fun uu____2308  ->
             match uu____2308 with
             | (mlid,modul) ->
                 let uu____2313 = FStar_Ident.path_of_lid mlid in
                 uu____2313 = path) env.modules in
      match uu____2302 with
      | Some (uu____2317,modul) -> Some modul
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___161_2339 =
        match uu___161_2339 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2343,lbs),uu____2345,uu____2346,uu____2347);
             FStar_Syntax_Syntax.sigrng = uu____2348;_},uu____2349)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2362 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2362
        | uu____2363 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2366  -> None)
        (fun uu____2367  -> None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___162_2386 =
        match uu___162_2386 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2393,uu____2394,uu____2395);
             FStar_Syntax_Syntax.sigrng = uu____2396;_},uu____2397)
            ->
            FStar_Util.find_map (Prims.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2414 -> None)
        | uu____2419 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2426  -> None)
        (fun uu____2429  -> None) k_global_def
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
          let uu____2456 = try_lookup_name any_val exclude_interf env lid in
          match uu____2456 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2465 -> None
let try_lookup_lid:
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2485 = try_lookup_lid env l in
      match uu____2485 with
      | None  -> None
      | Some (e,uu____2493) ->
          let uu____2496 =
            let uu____2497 = FStar_Syntax_Subst.compress e in
            uu____2497.FStar_Syntax_Syntax.n in
          (match uu____2496 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2506 -> None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___178_2517 = env in
        {
          curmodule = (uu___178_2517.curmodule);
          curmonad = (uu___178_2517.curmonad);
          modules = (uu___178_2517.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___178_2517.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___178_2517.sigaccum);
          sigmap = (uu___178_2517.sigmap);
          iface = (uu___178_2517.iface);
          admitted_iface = (uu___178_2517.admitted_iface);
          expect_typ = (uu___178_2517.expect_typ);
          docs = (uu___178_2517.docs);
          remaining_iface_decls = (uu___178_2517.remaining_iface_decls)
        } in
      try_lookup_lid env' l
let try_lookup_doc:
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___164_2541 =
        match uu___164_2541 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2545,uu____2546,uu____2547,quals);
             FStar_Syntax_Syntax.sigrng = uu____2549;_},uu____2550)
            ->
            let uu____2553 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___163_2555  ->
                      match uu___163_2555 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2556 -> false)) in
            if uu____2553
            then
              let uu____2558 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2558
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2560;
             FStar_Syntax_Syntax.sigrng = uu____2561;_},uu____2562)
            ->
            let uu____2572 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2572
        | uu____2573 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2576  -> None)
        (fun uu____2577  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___165_2596 =
        match uu___165_2596 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2601,uu____2602,uu____2603,uu____2604,uu____2605,datas,uu____2607);
             FStar_Syntax_Syntax.sigrng = uu____2608;_},uu____2609)
            -> Some datas
        | uu____2617 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2622  -> None)
        (fun uu____2624  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____2658 =
    let uu____2659 =
      let uu____2662 =
        let uu____2664 = FStar_ST.read record_cache in
        FStar_List.hd uu____2664 in
      let uu____2672 = FStar_ST.read record_cache in uu____2662 :: uu____2672 in
    FStar_ST.write record_cache uu____2659 in
  let pop1 uu____2687 =
    let uu____2688 =
      let uu____2691 = FStar_ST.read record_cache in FStar_List.tl uu____2691 in
    FStar_ST.write record_cache uu____2688 in
  let peek uu____2707 =
    let uu____2708 = FStar_ST.read record_cache in FStar_List.hd uu____2708 in
  let insert r =
    let uu____2720 =
      let uu____2723 = let uu____2725 = peek () in r :: uu____2725 in
      let uu____2727 =
        let uu____2730 = FStar_ST.read record_cache in
        FStar_List.tl uu____2730 in
      uu____2723 :: uu____2727 in
    FStar_ST.write record_cache uu____2720 in
  let commit1 uu____2746 =
    let uu____2747 = FStar_ST.read record_cache in
    match uu____2747 with
    | hd1::uu____2755::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2768 -> failwith "Impossible" in
  let filter1 uu____2774 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____2781 =
           let uu____2784 = FStar_ST.read record_cache in filtered ::
             uu____2784 in
         FStar_ST.write record_cache uu____2781) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____2858 = record_cache_aux_with_filter in
  match uu____2858 with | (aux,uu____2896) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____2935 = record_cache_aux_with_filter in
  match uu____2935 with | (uu____2958,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____2998 = record_cache_aux in
  match uu____2998 with
  | (push1,uu____3018,uu____3019,uu____3020,uu____3021) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____3046 = record_cache_aux in
  match uu____3046 with
  | (uu____3065,pop1,uu____3067,uu____3068,uu____3069) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____3095 = record_cache_aux in
  match uu____3095 with
  | (uu____3115,uu____3116,peek,uu____3118,uu____3119) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____3144 = record_cache_aux in
  match uu____3144 with
  | (uu____3163,uu____3164,uu____3165,insert,uu____3167) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____3192 = record_cache_aux in
  match uu____3192 with
  | (uu____3211,uu____3212,uu____3213,uu____3214,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3254,uu____3255) ->
            let is_rec =
              FStar_Util.for_some
                (fun uu___166_3266  ->
                   match uu___166_3266 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____3269 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___167_3277  ->
                      match uu___167_3277 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3279,uu____3280,uu____3281,uu____3282,uu____3283,uu____3284);
                          FStar_Syntax_Syntax.sigrng = uu____3285;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3290 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___168_3292  ->
                    match uu___168_3292 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____3296,uu____3297,dc::[],tags);
                        FStar_Syntax_Syntax.sigrng = uu____3300;_} ->
                        let uu____3306 =
                          let uu____3307 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3307 in
                        (match uu____3306 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3311,t,uu____3313,uu____3314,uu____3315,uu____3316);
                             FStar_Syntax_Syntax.sigrng = uu____3317;_} ->
                             let uu____3322 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3322 with
                              | (formals,uu____3331) ->
                                  let is_rec1 = is_rec tags in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3357  ->
                                            match uu____3357 with
                                            | (x,q) ->
                                                let uu____3365 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec1 &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3365
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3396  ->
                                            match uu____3396 with
                                            | (x,q) ->
                                                let uu____3405 =
                                                  if is_rec1
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____3405,
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
                                            FStar_Syntax_Syntax.Private tags)
                                           ||
                                           (FStar_List.contains
                                              FStar_Syntax_Syntax.Abstract
                                              tags));
                                      is_record = is_rec1
                                    } in
                                  ((let uu____3417 =
                                      let uu____3419 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3419 in
                                    FStar_ST.write new_globs uu____3417);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3435 =
                                            match uu____3435 with
                                            | (id,uu____3441) ->
                                                let modul =
                                                  let uu____3447 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3447.FStar_Ident.str in
                                                let uu____3448 =
                                                  get_exported_id_set e modul in
                                                (match uu____3448 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____3464 =
                                                         let uu____3465 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3465 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3464);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3472 =
                                                               let uu____3473
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____3473.FStar_Ident.ident in
                                                             uu____3472.FStar_Ident.idText in
                                                           let uu____3475 =
                                                             let uu____3476 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3476 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3475))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3489 -> ())
                    | uu____3490 -> ()))
        | uu____3491 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3504 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3504 with
        | (ns,id) ->
            let uu____3514 = peek_record_cache () in
            FStar_Util.find_map uu____3514
              (fun record  ->
                 let uu____3517 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3520  -> None) uu____3517) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3521  -> Cont_ignore) (fun uu____3522  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3525 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3525)
        (fun k  -> fun uu____3528  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let uu____3537 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3537 with
      | Some r when r.is_record -> Some r
      | uu____3541 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3552 = try_lookup_record_by_field_name env lid in
        match uu____3552 with
        | Some record' when
            let uu____3555 =
              let uu____3556 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3556 in
            let uu____3558 =
              let uu____3559 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3559 in
            uu____3555 = uu____3558 ->
            let uu____3561 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3563  -> Cont_ok ()) in
            (match uu____3561 with
             | Cont_ok uu____3564 -> true
             | uu____3565 -> false)
        | uu____3567 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) Prims.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____3578 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3578 with
      | Some r ->
          let uu____3584 =
            let uu____3587 =
              let uu____3588 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3588
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3587, (r.is_record)) in
          Some uu____3584
      | uu____3591 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3600  ->
    let uu____3601 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3601
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3612  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___169_3621  ->
      match uu___169_3621 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___170_3641 =
            match uu___170_3641 with
            | Rec_binding uu____3642 -> true
            | uu____3643 -> false in
          let this_env =
            let uu___179_3645 = env in
            let uu____3646 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___179_3645.curmodule);
              curmonad = (uu___179_3645.curmonad);
              modules = (uu___179_3645.modules);
              scope_mods = uu____3646;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___179_3645.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___179_3645.sigaccum);
              sigmap = (uu___179_3645.sigmap);
              iface = (uu___179_3645.iface);
              admitted_iface = (uu___179_3645.admitted_iface);
              expect_typ = (uu___179_3645.expect_typ);
              docs = (uu___179_3645.docs);
              remaining_iface_decls = (uu___179_3645.remaining_iface_decls)
            } in
          let uu____3648 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3648 with | None  -> true | Some uu____3654 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___180_3665 = env in
      {
        curmodule = (uu___180_3665.curmodule);
        curmonad = (uu___180_3665.curmonad);
        modules = (uu___180_3665.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___180_3665.exported_ids);
        trans_exported_ids = (uu___180_3665.trans_exported_ids);
        includes = (uu___180_3665.includes);
        sigaccum = (uu___180_3665.sigaccum);
        sigmap = (uu___180_3665.sigmap);
        iface = (uu___180_3665.iface);
        admitted_iface = (uu___180_3665.admitted_iface);
        expect_typ = (uu___180_3665.expect_typ);
        docs = (uu___180_3665.docs);
        remaining_iface_decls = (uu___180_3665.remaining_iface_decls)
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
        let uu____3704 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____3704
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
          | Some (se,uu____3724) ->
              let uu____3727 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____3727 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____3732 =
          let uu____3733 =
            let uu____3736 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____3736, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____3733 in
        Prims.raise uu____3732 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____3743 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3748 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3756 -> (true, true)
          | uu____3763 -> (false, false) in
        match uu____3743 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____3768 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3771 =
                     let uu____3772 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____3772 in
                   if uu____3771 then Some l else None) in
            (match uu____3768 with
             | Some l when
                 let uu____3776 = FStar_Options.interactive () in
                 Prims.op_Negation uu____3776 -> err1 l
             | uu____3777 ->
                 (extract_record env globals s;
                  (let uu___181_3782 = env in
                   {
                     curmodule = (uu___181_3782.curmodule);
                     curmonad = (uu___181_3782.curmonad);
                     modules = (uu___181_3782.modules);
                     scope_mods = (uu___181_3782.scope_mods);
                     exported_ids = (uu___181_3782.exported_ids);
                     trans_exported_ids = (uu___181_3782.trans_exported_ids);
                     includes = (uu___181_3782.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___181_3782.sigmap);
                     iface = (uu___181_3782.iface);
                     admitted_iface = (uu___181_3782.admitted_iface);
                     expect_typ = (uu___181_3782.expect_typ);
                     docs = (uu___181_3782.docs);
                     remaining_iface_decls =
                       (uu___181_3782.remaining_iface_decls)
                   }))) in
      let env2 =
        let uu___182_3784 = env1 in
        let uu____3785 = FStar_ST.read globals in
        {
          curmodule = (uu___182_3784.curmodule);
          curmonad = (uu___182_3784.curmonad);
          modules = (uu___182_3784.modules);
          scope_mods = uu____3785;
          exported_ids = (uu___182_3784.exported_ids);
          trans_exported_ids = (uu___182_3784.trans_exported_ids);
          includes = (uu___182_3784.includes);
          sigaccum = (uu___182_3784.sigaccum);
          sigmap = (uu___182_3784.sigmap);
          iface = (uu___182_3784.iface);
          admitted_iface = (uu___182_3784.admitted_iface);
          expect_typ = (uu___182_3784.expect_typ);
          docs = (uu___182_3784.docs);
          remaining_iface_decls = (uu___182_3784.remaining_iface_decls)
        } in
      let uu____3790 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3804,uu____3805) ->
            let uu____3812 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____3812)
        | uu____3826 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____3790 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3856  ->
                   match uu____3856 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3867 =
                                  let uu____3869 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3869 in
                                FStar_ST.write globals uu____3867);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3878 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____3878.FStar_Ident.str in
                                    ((let uu____3880 =
                                        get_exported_id_set env3 modul in
                                      match uu____3880 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____3895 =
                                            let uu____3896 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3896 in
                                          FStar_ST.write my_exported_ids
                                            uu____3895
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
              let uu___183_3908 = env3 in
              let uu____3909 = FStar_ST.read globals in
              {
                curmodule = (uu___183_3908.curmodule);
                curmonad = (uu___183_3908.curmonad);
                modules = (uu___183_3908.modules);
                scope_mods = uu____3909;
                exported_ids = (uu___183_3908.exported_ids);
                trans_exported_ids = (uu___183_3908.trans_exported_ids);
                includes = (uu___183_3908.includes);
                sigaccum = (uu___183_3908.sigaccum);
                sigmap = (uu___183_3908.sigmap);
                iface = (uu___183_3908.iface);
                admitted_iface = (uu___183_3908.admitted_iface);
                expect_typ = (uu___183_3908.expect_typ);
                docs = (uu___183_3908.docs);
                remaining_iface_decls = (uu___183_3908.remaining_iface_decls)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3920 =
        let uu____3923 = resolve_module_name env ns false in
        match uu____3923 with
        | None  ->
            let modules = env.modules in
            let uu____3931 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3937  ->
                      match uu____3937 with
                      | (m,uu____3941) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____3931
            then (ns, Open_namespace)
            else
              (let uu____3945 =
                 let uu____3946 =
                   let uu____3949 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____3949, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____3946 in
               Prims.raise uu____3945)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module)) in
      match uu____3920 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns in
      let uu____3963 = resolve_module_name env ns false in
      match uu____3963 with
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module)) in
            let curmod =
              let uu____3969 = current_module env1 in
              uu____3969.FStar_Ident.str in
            (let uu____3971 = FStar_Util.smap_try_find env1.includes curmod in
             match uu____3971 with
             | None  -> ()
             | Some incl ->
                 let uu____3984 =
                   let uu____3986 = FStar_ST.read incl in ns1 :: uu____3986 in
                 FStar_ST.write incl uu____3984);
            (match () with
             | () ->
                 let uu____3994 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                 (match uu____3994 with
                  | Some ns_trans_exports ->
                      ((let uu____4007 =
                          let uu____4018 = get_exported_id_set env1 curmod in
                          let uu____4023 =
                            get_trans_exported_id_set env1 curmod in
                          (uu____4018, uu____4023) in
                        match uu____4007 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____4063 = ns_trans_exports k in
                                FStar_ST.read uu____4063 in
                              let ex = cur_exports k in
                              (let uu____4072 =
                                 let uu____4073 = FStar_ST.read ex in
                                 FStar_Util.set_difference uu____4073 ns_ex in
                               FStar_ST.write ex uu____4072);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k in
                                   let uu____4083 =
                                     let uu____4084 = FStar_ST.read trans_ex in
                                     FStar_Util.set_union uu____4084 ns_ex in
                                   FStar_ST.write trans_ex uu____4083) in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____4090 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____4104 =
                        let uu____4105 =
                          let uu____4108 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str in
                          (uu____4108, (FStar_Ident.range_of_lid ns1)) in
                        FStar_Errors.Error uu____4105 in
                      Prims.raise uu____4104))))
      | uu____4109 ->
          let uu____4111 =
            let uu____4112 =
              let uu____4115 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____4115, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____4112 in
          Prims.raise uu____4111
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____4125 = module_is_defined env l in
        if uu____4125
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____4128 =
             let uu____4129 =
               let uu____4132 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____4132, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____4129 in
           Prims.raise uu____4128)
let push_doc:
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option -> env =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____4146 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____4146 with
              | None  -> ()
              | Some old_doc ->
                  let uu____4149 =
                    let uu____4150 = FStar_Ident.string_of_lid l in
                    let uu____4151 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____4152 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____4150 uu____4151 uu____4152 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____4149);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,quals) ->
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
                      FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                        ((let uu___184_4179 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_declare_typ
                                 (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                                   quals)));
                            FStar_Syntax_Syntax.sigrng =
                              (uu___184_4179.FStar_Syntax_Syntax.sigrng)
                          }), false))
                 | Some uu____4181 -> ())
            | uu____4186 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4197) ->
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
                                (lid,uu____4207,uu____4208,uu____4209,uu____4210,uu____4211,uu____4212)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4219 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4222,uu____4223,quals) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4230,lbs),uu____4232,quals,uu____4234) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4249 =
                               let uu____4250 =
                                 let uu____4251 =
                                   let uu____4256 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4256.FStar_Syntax_Syntax.fv_name in
                                 uu____4251.FStar_Syntax_Syntax.v in
                               uu____4250.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4249))
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
                               let uu____4266 =
                                 let uu____4271 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4271.FStar_Syntax_Syntax.fv_name in
                               uu____4266.FStar_Syntax_Syntax.v in
                             let decl =
                               let uu___185_4276 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp),
                                        (FStar_Syntax_Syntax.Assumption ::
                                        quals)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___185_4276.FStar_Syntax_Syntax.sigrng)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4284 -> ()));
      (let curmod =
         let uu____4286 = current_module env in uu____4286.FStar_Ident.str in
       (let uu____4288 =
          let uu____4299 = get_exported_id_set env curmod in
          let uu____4304 = get_trans_exported_id_set env curmod in
          (uu____4299, uu____4304) in
        match uu____4288 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4344 = cur_ex eikind in FStar_ST.read uu____4344 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4352 =
                let uu____4353 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4353 in
              FStar_ST.write cur_trans_ex_set_ref uu____4352 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4359 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___186_4371 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___186_4371.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___186_4371.exported_ids);
                    trans_exported_ids = (uu___186_4371.trans_exported_ids);
                    includes = (uu___186_4371.includes);
                    sigaccum = [];
                    sigmap = (uu___186_4371.sigmap);
                    iface = (uu___186_4371.iface);
                    admitted_iface = (uu___186_4371.admitted_iface);
                    expect_typ = (uu___186_4371.expect_typ);
                    docs = (uu___186_4371.docs);
                    remaining_iface_decls =
                      (uu___186_4371.remaining_iface_decls)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4384 =
       let uu____4386 = FStar_ST.read stack in env :: uu____4386 in
     FStar_ST.write stack uu____4384);
    (let uu___187_4394 = env in
     let uu____4395 = FStar_Util.smap_copy (sigmap env) in
     let uu____4401 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___187_4394.curmodule);
       curmonad = (uu___187_4394.curmonad);
       modules = (uu___187_4394.modules);
       scope_mods = (uu___187_4394.scope_mods);
       exported_ids = (uu___187_4394.exported_ids);
       trans_exported_ids = (uu___187_4394.trans_exported_ids);
       includes = (uu___187_4394.includes);
       sigaccum = (uu___187_4394.sigaccum);
       sigmap = uu____4395;
       iface = (uu___187_4394.iface);
       admitted_iface = (uu___187_4394.admitted_iface);
       expect_typ = (uu___187_4394.expect_typ);
       docs = uu____4401;
       remaining_iface_decls = (uu___187_4394.remaining_iface_decls)
     })
let pop: Prims.unit -> env =
  fun uu____4405  ->
    let uu____4406 = FStar_ST.read stack in
    match uu____4406 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4419 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4425 = FStar_ST.read stack in
     match uu____4425 with
     | uu____4430::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4437 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4444  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4456 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4458 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4476 = FStar_Util.smap_try_find sm' k in
              match uu____4476 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,q) ->
                          let uu___188_4495 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_declare_typ
                                 (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                                   q)));
                            FStar_Syntax_Syntax.sigrng =
                              (uu___188_4495.FStar_Syntax_Syntax.sigrng)
                          }
                      | uu____4497 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4500 -> ()));
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
            (let uu____4544 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4544);
            (match () with
             | () ->
                 ((let uu____4549 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4549);
                  (match () with
                   | () ->
                       ((let uu____4554 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4554);
                        (match () with
                         | () ->
                             let uu___189_4563 = env1 in
                             let uu____4564 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___189_4563.curmonad);
                               modules = (uu___189_4563.modules);
                               scope_mods = uu____4564;
                               exported_ids = (uu___189_4563.exported_ids);
                               trans_exported_ids =
                                 (uu___189_4563.trans_exported_ids);
                               includes = (uu___189_4563.includes);
                               sigaccum = (uu___189_4563.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___189_4563.expect_typ);
                               docs = (uu___189_4563.docs);
                               remaining_iface_decls =
                                 (uu___189_4563.remaining_iface_decls)
                             }))))) in
          let uu____4567 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4579  ->
                    match uu____4579 with
                    | (l,uu____4583) -> FStar_Ident.lid_equals l mname)) in
          match uu____4567 with
          | None  -> let uu____4588 = prep env in (uu____4588, false)
          | Some (uu____4589,m) ->
              ((let uu____4594 =
                  (let uu____4595 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4595) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4594
                then
                  let uu____4596 =
                    let uu____4597 =
                      let uu____4600 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4600, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4597 in
                  Prims.raise uu____4596
                else ());
               (let uu____4602 = let uu____4603 = push env in prep uu____4603 in
                (uu____4602, true)))
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
          let uu___190_4611 = env in
          {
            curmodule = (uu___190_4611.curmodule);
            curmonad = (Some mname);
            modules = (uu___190_4611.modules);
            scope_mods = (uu___190_4611.scope_mods);
            exported_ids = (uu___190_4611.exported_ids);
            trans_exported_ids = (uu___190_4611.trans_exported_ids);
            includes = (uu___190_4611.includes);
            sigaccum = (uu___190_4611.sigaccum);
            sigmap = (uu___190_4611.sigmap);
            iface = (uu___190_4611.iface);
            admitted_iface = (uu___190_4611.admitted_iface);
            expect_typ = (uu___190_4611.expect_typ);
            docs = (uu___190_4611.docs);
            remaining_iface_decls = (uu___190_4611.remaining_iface_decls)
          }
let fail_or env lookup lid =
  let uu____4636 = lookup lid in
  match uu____4636 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4642  ->
             match uu____4642 with
             | (lid1,uu____4646) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4653 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4653
               (FStar_Ident.range_of_lid lid) in
           let uu____4654 = resolve_module_name env modul true in
           match uu____4654 with
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
  let uu____4681 = lookup id in
  match uu____4681 with
  | None  ->
      Prims.raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r