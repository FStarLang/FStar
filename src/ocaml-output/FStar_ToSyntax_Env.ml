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
  expect_typ: Prims.bool;}
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ* Prims.bool)
  | Eff_name of (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident)
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____314 -> false
let __proj__Term_name__item___0:
  foundname -> (FStar_Syntax_Syntax.typ* Prims.bool) =
  fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____334 -> false
let __proj__Eff_name__item___0:
  foundname -> (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0
let all_exported_id_kinds: exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type]
let transitive_exported_ids:
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid in
      let uu____357 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____357 with
      | None  -> []
      | Some exported_id_set ->
          let uu____361 =
            let uu____362 = exported_id_set Exported_id_term_type in
            FStar_ST.read uu____362 in
          FStar_All.pipe_right uu____361 FStar_Util.set_elements
let open_modules:
  env -> (FStar_Ident.lident* FStar_Syntax_Syntax.modul) Prims.list =
  fun e  -> e.modules
let current_module: env -> FStar_Ident.lident =
  fun env  ->
    match env.curmodule with
    | None  -> failwith "Unset current module"
    | Some m -> m
let qual: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id
let qualify: env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | None  -> let uu____388 = current_module env in qual uu____388 id
      | Some monad ->
          let uu____390 =
            let uu____391 = current_module env in qual uu____391 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____390 id
let new_sigmap uu____399 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____402  ->
    let uu____403 = new_sigmap () in
    let uu____405 = new_sigmap () in
    let uu____407 = new_sigmap () in
    let uu____413 = new_sigmap () in
    {
      curmodule = None;
      curmonad = None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____403;
      trans_exported_ids = uu____405;
      includes = uu____407;
      sigaccum = [];
      sigmap = uu____413;
      iface = false;
      admitted_iface = false;
      expect_typ = false
    }
let sigmap: env -> (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap =
  fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____432  ->
         match uu____432 with
         | (m,uu____436) ->
             FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___175_444 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___175_444.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___176_445 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___176_445.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___176_445.FStar_Syntax_Syntax.sort)
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
        (fun uu____491  ->
           match uu____491 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____505 =
                   let uu____506 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____506 dd dq in
                 Some uu____505
               else None) in
    match t with | Some v1 -> Some (v1, false) | None  -> None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____536 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____560 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____571 -> false
let option_of_cont k_ignore uu___144_590 =
  match uu___144_590 with
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
        (fun uu____635  ->
           match uu____635 with
           | (f,uu____640) ->
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
  fun uu___145_676  ->
    match uu___145_676 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___146_725 =
    match uu___146_725 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
          let uu____733 = get_exported_id_set env mname in
          match uu____733 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____749 = mex eikind in FStar_ST.read uu____749 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____756 = FStar_Util.smap_try_find env.includes mname in
          match uu____756 with
          | None  -> []
          | Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
          then let uu____776 = qual modul id in find_in_module uu____776
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____779 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___147_783  ->
    match uu___147_783 with | Exported_id_field  -> true | uu____784 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___148_873 =
    match uu___148_873 with
    | (id',uu____875,uu____876) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___149_880 =
    match uu___149_880 with
    | (id',uu____882,uu____883) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____886 = current_module env in FStar_Ident.ids_of_lid uu____886 in
  let proc uu___150_891 =
    match uu___150_891 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____896) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____899 = FStar_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____899 id
    | uu____902 -> Cont_ignore in
  let rec aux uu___151_908 =
    match uu___151_908 with
    | a::q ->
        let uu____914 = proc a in
        option_of_cont (fun uu____916  -> aux q) uu____914
    | [] ->
        let uu____917 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____919  -> None) uu____917 in
  aux env.scope_mods
let found_local_binding r uu____938 =
  match uu____938 with
  | (id',x,mut) -> let uu____945 = bv_to_name x r in (uu____945, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____982 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____982 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found
let try_lookup_id:
  env ->
    FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  =
  fun env  ->
    fun id  ->
      let uu____1004 = unmangleOpName id in
      match uu____1004 with
      | Some f -> Some f
      | uu____1018 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1025 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1025) (fun uu____1030  -> Cont_fail)
            (fun uu____1033  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1040  -> fun uu____1041  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1048  -> fun uu____1049  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1101 ->
        let lid = qualify env id in
        let uu____1103 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____1103 with
         | Some r -> let uu____1116 = k_global_def lid r in Some uu____1116
         | None  -> None)
    | None  -> None in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1129 = current_module env in qual uu____1129 id in
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
           let uu____1138 = current_module env in
           FStar_Ident.lid_equals lid uu____1138)
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
        let rec aux uu___152_1162 =
          match uu___152_1162 with
          | [] ->
              let uu____1165 = module_is_defined env lid in
              if uu____1165 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1172 =
                  let uu____1174 = FStar_Ident.path_of_lid ns in
                  let uu____1176 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1174 uu____1176 in
                FStar_Ident.lid_of_path uu____1172
                  (FStar_Ident.range_of_lid lid) in
              let uu____1178 = module_is_defined env new_lid in
              if uu____1178 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1183 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1187::q -> aux q in
        aux env.scope_mods
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___153_1196  ->
           match uu___153_1196 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1198 -> false) env.scope_mods
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
                 let uu____1253 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____1253
                   (FStar_Util.map_option
                      (fun uu____1277  ->
                         match uu____1277 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____1294 =
          is_full_path &&
            (let uu____1295 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____1295) in
        if uu____1294
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1312 = aux ns_rev_prefix ns_last_id in
               (match uu____1312 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1425::uu____1426 ->
      let uu____1428 =
        let uu____1430 =
          let uu____1431 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____1431 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____1430 true in
      (match uu____1428 with
       | None  -> None
       | Some modul ->
           let uu____1434 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____1436  -> None) uu____1434)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___154_1451 =
  match uu___154_1451 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1530 = k_global_def lid1 def in cont_of_option k uu____1530 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1551 = k_local_binding l in
       cont_of_option Cont_fail uu____1551)
    (fun r  ->
       let uu____1554 = k_rec_binding r in
       cont_of_option Cont_fail uu____1554) (fun uu____1556  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual Prims.option =
  fun uu___156_1560  ->
    match uu___156_1560 with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1562,uu____1563,uu____1564,l,uu____1566,quals,uu____1568,uu____1569)
        ->
        let qopt =
          FStar_Util.find_map quals
            (fun uu___155_1576  ->
               match uu___155_1576 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1578,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1585 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____1589,uu____1590,uu____1591,quals,uu____1593) -> None
    | uu____1596 -> None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1605 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____1609 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____1609 then Some fv else None) in
      FStar_All.pipe_right uu____1605 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1623 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____1623 ns)
let try_lookup_name:
  Prims.bool ->
    Prims.bool -> env -> FStar_Ident.lident -> foundname Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___160_1648 =
            match uu___160_1648 with
            | (uu____1652,true ) when exclude_interf -> None
            | (se,uu____1654) ->
                (match se with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1656 ->
                     let uu____1668 =
                       let uu____1669 =
                         let uu____1672 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____1672, false) in
                       Term_name uu____1669 in
                     Some uu____1668
                 | FStar_Syntax_Syntax.Sig_datacon uu____1673 ->
                     let uu____1684 =
                       let uu____1685 =
                         let uu____1688 =
                           let uu____1689 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1689 in
                         (uu____1688, false) in
                       Term_name uu____1685 in
                     Some uu____1684
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1691,lbs),uu____1693,uu____1694,uu____1695,uu____1696)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____1709 =
                       let uu____1710 =
                         let uu____1713 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____1713, false) in
                       Term_name uu____1710 in
                     Some uu____1709
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1715,uu____1716,quals,uu____1718) ->
                     let uu____1721 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___157_1723  ->
                                  match uu___157_1723 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1724 -> false))) in
                     if uu____1721
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____1728 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___158_1730  ->
                                         match uu___158_1730 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1733 -> false)))) in
                         if uu____1728
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____1735 =
                         FStar_Util.find_map quals
                           (fun uu___159_1737  ->
                              match uu___159_1737 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1740 -> None) in
                       (match uu____1735 with
                        | Some refl_monad ->
                            let refl_const =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reflect refl_monad)))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
                        | uu____1756 ->
                            let uu____1758 =
                              let uu____1759 =
                                let uu____1762 =
                                  let uu____1763 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____1763 in
                                (uu____1762, false) in
                              Term_name uu____1759 in
                            Some uu____1758)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,_)
                   |FStar_Syntax_Syntax.Sig_new_effect (ne,_) ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1769 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1779 -> None) in
          let k_local_binding r =
            let uu____1791 =
              let uu____1792 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____1792 in
            Some uu____1791 in
          let k_rec_binding uu____1802 =
            match uu____1802 with
            | (id,l,dd) ->
                let uu____1810 =
                  let uu____1811 =
                    let uu____1814 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____1814, false) in
                  Term_name uu____1811 in
                Some uu____1810 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____1818 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____1818 with
                 | Some f -> Some (Term_name f)
                 | uu____1828 -> None)
            | uu____1832 -> None in
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
        let uu____1852 = try_lookup_name true exclude_interf env lid in
        match uu____1852 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____1861 -> None
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1872 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1872 with | Some (o,l1) -> Some l1 | uu____1881 -> None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list)
        Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____1895 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1895 with
      | Some (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1904),l1) ->
          Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,uu____1913),l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          (FStar_Syntax_Syntax.Sig_effect_abbrev
           (uu____1921,uu____1922,uu____1923,uu____1924,uu____1925,cattributes,uu____1927),l1)
          -> Some (l1, cattributes)
      | uu____1939 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      let uu____1953 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1953 with
      | Some (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1959),uu____1960)
          -> Some ne
      | Some
          (FStar_Syntax_Syntax.Sig_new_effect_for_free
           (ne,uu____1964),uu____1965)
          -> Some ne
      | uu____1968 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____1978 = try_lookup_effect_name env lid in
      match uu____1978 with | None  -> false | Some uu____1980 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1988 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1988 with
      | Some
          (FStar_Syntax_Syntax.Sig_effect_abbrev
           (l',uu____1994,uu____1995,uu____1996,uu____1997,uu____1998,uu____1999),uu____2000)
          ->
          let rec aux new_name =
            let uu____2012 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2012 with
            | None  -> None
            | Some (s,uu____2022) ->
                (match s with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,_)
                   |FStar_Syntax_Syntax.Sig_new_effect (ne,_) ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____2029,uu____2030,uu____2031,cmp,uu____2033,uu____2034,uu____2035)
                     ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2041 -> None) in
          aux l'
      | Some (uu____2042,l') -> Some l'
      | uu____2046 -> None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___161_2067 =
        match uu___161_2067 with
        | (FStar_Syntax_Syntax.Sig_declare_typ
           (lid2,uu____2073,uu____2074,quals,uu____2076),uu____2077) ->
            Some quals
        | uu____2081 -> None in
      let uu____2085 =
        resolve_in_open_namespaces' env lid (fun uu____2089  -> None)
          (fun uu____2091  -> None) k_global_def in
      match uu____2085 with | Some quals -> quals | uu____2097 -> []
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul Prims.option =
  fun env  ->
    fun path  ->
      let uu____2109 =
        FStar_List.tryFind
          (fun uu____2115  ->
             match uu____2115 with
             | (mlid,modul) ->
                 let uu____2120 = FStar_Ident.path_of_lid mlid in
                 uu____2120 = path) env.modules in
      match uu____2109 with
      | Some (uu____2124,modul) -> Some modul
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___162_2146 =
        match uu___162_2146 with
        | (FStar_Syntax_Syntax.Sig_let
           ((uu____2150,lbs),uu____2152,uu____2153,uu____2154,uu____2155),uu____2156)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2169 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2169
        | uu____2170 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2173  -> None)
        (fun uu____2174  -> None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___163_2193 =
        match uu___163_2193 with
        | (FStar_Syntax_Syntax.Sig_let
           (lbs,uu____2200,uu____2201,uu____2202,uu____2203),uu____2204) ->
            FStar_Util.find_map (Prims.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2221 -> None)
        | uu____2226 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2233  -> None)
        (fun uu____2236  -> None) k_global_def
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
          let uu____2263 = try_lookup_name any_val exclude_interf env lid in
          match uu____2263 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2272 -> None
let try_lookup_lid:
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let resolve_to_fully_qualified_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2292 = try_lookup_lid env l in
      match uu____2292 with
      | None  -> None
      | Some (e,uu____2300) ->
          let uu____2303 =
            let uu____2304 = FStar_Syntax_Subst.compress e in
            uu____2304.FStar_Syntax_Syntax.n in
          (match uu____2303 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2313 -> None)
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___177_2324 = env in
        {
          curmodule = (uu___177_2324.curmodule);
          curmonad = (uu___177_2324.curmonad);
          modules = (uu___177_2324.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___177_2324.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___177_2324.sigaccum);
          sigmap = (uu___177_2324.sigmap);
          iface = (uu___177_2324.iface);
          admitted_iface = (uu___177_2324.admitted_iface);
          expect_typ = (uu___177_2324.expect_typ)
        } in
      try_lookup_lid env' l
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___165_2341 =
        match uu___165_2341 with
        | (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2345,uu____2346,uu____2347,quals,uu____2349),uu____2350) ->
            let uu____2353 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___164_2355  ->
                      match uu___164_2355 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2356 -> false)) in
            if uu____2353
            then
              let uu____2358 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2358
            else None
        | (FStar_Syntax_Syntax.Sig_datacon uu____2360,uu____2361) ->
            let uu____2372 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2372
        | uu____2373 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2376  -> None)
        (fun uu____2377  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___166_2396 =
        match uu___166_2396 with
        | (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____2401,uu____2402,uu____2403,uu____2404,uu____2405,datas,uu____2407,uu____2408),uu____2409)
            -> Some datas
        | uu____2417 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2422  -> None)
        (fun uu____2424  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____2458 =
    let uu____2459 =
      let uu____2462 =
        let uu____2464 = FStar_ST.read record_cache in
        FStar_List.hd uu____2464 in
      let uu____2472 = FStar_ST.read record_cache in uu____2462 :: uu____2472 in
    FStar_ST.write record_cache uu____2459 in
  let pop1 uu____2487 =
    let uu____2488 =
      let uu____2491 = FStar_ST.read record_cache in FStar_List.tl uu____2491 in
    FStar_ST.write record_cache uu____2488 in
  let peek uu____2507 =
    let uu____2508 = FStar_ST.read record_cache in FStar_List.hd uu____2508 in
  let insert r =
    let uu____2520 =
      let uu____2523 = let uu____2525 = peek () in r :: uu____2525 in
      let uu____2527 =
        let uu____2530 = FStar_ST.read record_cache in
        FStar_List.tl uu____2530 in
      uu____2523 :: uu____2527 in
    FStar_ST.write record_cache uu____2520 in
  let commit1 uu____2546 =
    let uu____2547 = FStar_ST.read record_cache in
    match uu____2547 with
    | hd1::uu____2555::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2568 -> failwith "Impossible" in
  let filter1 uu____2574 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____2581 =
           let uu____2584 = FStar_ST.read record_cache in filtered ::
             uu____2584 in
         FStar_ST.write record_cache uu____2581) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____2658 = record_cache_aux_with_filter in
  match uu____2658 with | (aux,uu____2696) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____2735 = record_cache_aux_with_filter in
  match uu____2735 with | (uu____2758,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____2798 = record_cache_aux in
  match uu____2798 with
  | (push1,uu____2818,uu____2819,uu____2820,uu____2821) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____2846 = record_cache_aux in
  match uu____2846 with
  | (uu____2865,pop1,uu____2867,uu____2868,uu____2869) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____2895 = record_cache_aux in
  match uu____2895 with
  | (uu____2915,uu____2916,peek,uu____2918,uu____2919) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____2944 = record_cache_aux in
  match uu____2944 with
  | (uu____2963,uu____2964,uu____2965,insert,uu____2967) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____2992 = record_cache_aux in
  match uu____2992 with
  | (uu____3011,uu____3012,uu____3013,uu____3014,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun uu___170_3049  ->
        match uu___170_3049 with
        | FStar_Syntax_Syntax.Sig_bundle
            (sigs,uu____3054,uu____3055,uu____3056) ->
            let is_rec =
              FStar_Util.for_some
                (fun uu___167_3067  ->
                   match uu___167_3067 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____3070 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___168_3078  ->
                      match uu___168_3078 with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3080,uu____3081,uu____3082,uu____3083,uu____3084,uu____3085,uu____3086)
                          -> FStar_Ident.lid_equals dc lid
                      | uu____3091 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___169_3093  ->
                    match uu___169_3093 with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (typename,univs,parms,uu____3097,uu____3098,dc::[],tags,uu____3101)
                        ->
                        let uu____3107 =
                          let uu____3108 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3108 in
                        (match uu____3107 with
                         | FStar_Syntax_Syntax.Sig_datacon
                             (constrname,uu____3112,t,uu____3114,uu____3115,uu____3116,uu____3117,uu____3118)
                             ->
                             let uu____3123 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3123 with
                              | (formals,uu____3132) ->
                                  let is_rec1 = is_rec tags in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3158  ->
                                            match uu____3158 with
                                            | (x,q) ->
                                                let uu____3166 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec1 &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3166
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3197  ->
                                            match uu____3197 with
                                            | (x,q) ->
                                                let uu____3206 =
                                                  if is_rec1
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____3206,
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
                                  ((let uu____3218 =
                                      let uu____3220 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3220 in
                                    FStar_ST.write new_globs uu____3218);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3236 =
                                            match uu____3236 with
                                            | (id,uu____3242) ->
                                                let modul =
                                                  let uu____3248 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3248.FStar_Ident.str in
                                                let uu____3249 =
                                                  get_exported_id_set e modul in
                                                (match uu____3249 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____3265 =
                                                         let uu____3266 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3266 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3265);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3273 =
                                                               let uu____3274
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____3274.FStar_Ident.ident in
                                                             uu____3273.FStar_Ident.idText in
                                                           let uu____3276 =
                                                             let uu____3277 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3277 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3276))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3290 -> ())
                    | uu____3291 -> ()))
        | uu____3292 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3305 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3305 with
        | (ns,id) ->
            let uu____3315 = peek_record_cache () in
            FStar_Util.find_map uu____3315
              (fun record  ->
                 let uu____3318 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3321  -> None) uu____3318) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3322  -> Cont_ignore) (fun uu____3323  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3326 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3326)
        (fun k  -> fun uu____3329  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let uu____3338 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3338 with
      | Some r when r.is_record -> Some r
      | uu____3342 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3353 = try_lookup_record_by_field_name env lid in
        match uu____3353 with
        | Some record' when
            let uu____3356 =
              let uu____3357 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3357 in
            let uu____3359 =
              let uu____3360 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3360 in
            uu____3356 = uu____3359 ->
            let uu____3362 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3364  -> Cont_ok ()) in
            (match uu____3362 with
             | Cont_ok uu____3365 -> true
             | uu____3366 -> false)
        | uu____3368 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) Prims.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____3379 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3379 with
      | Some r ->
          let uu____3385 =
            let uu____3388 =
              let uu____3389 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3389
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3388, (r.is_record)) in
          Some uu____3385
      | uu____3392 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3401  ->
    let uu____3402 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3402
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3413  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___171_3422  ->
      match uu___171_3422 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___172_3442 =
            match uu___172_3442 with
            | Rec_binding uu____3443 -> true
            | uu____3444 -> false in
          let this_env =
            let uu___178_3446 = env in
            let uu____3447 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___178_3446.curmodule);
              curmonad = (uu___178_3446.curmonad);
              modules = (uu___178_3446.modules);
              scope_mods = uu____3447;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___178_3446.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___178_3446.sigaccum);
              sigmap = (uu___178_3446.sigmap);
              iface = (uu___178_3446.iface);
              admitted_iface = (uu___178_3446.admitted_iface);
              expect_typ = (uu___178_3446.expect_typ)
            } in
          let uu____3449 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3449 with | None  -> true | Some uu____3455 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___179_3466 = env in
      {
        curmodule = (uu___179_3466.curmodule);
        curmonad = (uu___179_3466.curmonad);
        modules = (uu___179_3466.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___179_3466.exported_ids);
        trans_exported_ids = (uu___179_3466.trans_exported_ids);
        includes = (uu___179_3466.includes);
        sigaccum = (uu___179_3466.sigaccum);
        sigmap = (uu___179_3466.sigmap);
        iface = (uu___179_3466.iface);
        admitted_iface = (uu___179_3466.admitted_iface);
        expect_typ = (uu___179_3466.expect_typ)
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
        let uu____3505 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____3505
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          Prims.raise
            (FStar_Errors.Error
               ((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str),
                 (FStar_Ident.range_of_lid l)))
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str in
        let r =
          match sopt with
          | Some (se,uu____3525) ->
              let uu____3528 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____3528 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____3533 =
          let uu____3534 =
            let uu____3537 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____3537, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____3534 in
        Prims.raise uu____3533 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____3544 =
          match s with
          | FStar_Syntax_Syntax.Sig_let uu____3549 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3558 -> (true, true)
          | uu____3566 -> (false, false) in
        match uu____3544 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____3571 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3574 =
                     let uu____3575 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____3575 in
                   if uu____3574 then Some l else None) in
            (match uu____3571 with
             | Some l when
                 let uu____3579 = FStar_Options.interactive () in
                 Prims.op_Negation uu____3579 -> err l
             | uu____3580 ->
                 (extract_record env globals s;
                  (let uu___180_3585 = env in
                   {
                     curmodule = (uu___180_3585.curmodule);
                     curmonad = (uu___180_3585.curmonad);
                     modules = (uu___180_3585.modules);
                     scope_mods = (uu___180_3585.scope_mods);
                     exported_ids = (uu___180_3585.exported_ids);
                     trans_exported_ids = (uu___180_3585.trans_exported_ids);
                     includes = (uu___180_3585.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___180_3585.sigmap);
                     iface = (uu___180_3585.iface);
                     admitted_iface = (uu___180_3585.admitted_iface);
                     expect_typ = (uu___180_3585.expect_typ)
                   }))) in
      let env2 =
        let uu___181_3587 = env1 in
        let uu____3588 = FStar_ST.read globals in
        {
          curmodule = (uu___181_3587.curmodule);
          curmonad = (uu___181_3587.curmonad);
          modules = (uu___181_3587.modules);
          scope_mods = uu____3588;
          exported_ids = (uu___181_3587.exported_ids);
          trans_exported_ids = (uu___181_3587.trans_exported_ids);
          includes = (uu___181_3587.includes);
          sigaccum = (uu___181_3587.sigaccum);
          sigmap = (uu___181_3587.sigmap);
          iface = (uu___181_3587.iface);
          admitted_iface = (uu___181_3587.admitted_iface);
          expect_typ = (uu___181_3587.expect_typ)
        } in
      let uu____3593 =
        match s with
        | FStar_Syntax_Syntax.Sig_bundle
            (ses,uu____3607,uu____3608,uu____3609) ->
            let uu____3616 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____3616)
        | uu____3630 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____3593 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3660  ->
                   match uu____3660 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3671 =
                                  let uu____3673 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3673 in
                                FStar_ST.write globals uu____3671);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3682 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____3682.FStar_Ident.str in
                                    ((let uu____3684 =
                                        get_exported_id_set env3 modul in
                                      match uu____3684 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____3699 =
                                            let uu____3700 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3700 in
                                          FStar_ST.write my_exported_ids
                                            uu____3699
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
              let uu___182_3712 = env3 in
              let uu____3713 = FStar_ST.read globals in
              {
                curmodule = (uu___182_3712.curmodule);
                curmonad = (uu___182_3712.curmonad);
                modules = (uu___182_3712.modules);
                scope_mods = uu____3713;
                exported_ids = (uu___182_3712.exported_ids);
                trans_exported_ids = (uu___182_3712.trans_exported_ids);
                includes = (uu___182_3712.includes);
                sigaccum = (uu___182_3712.sigaccum);
                sigmap = (uu___182_3712.sigmap);
                iface = (uu___182_3712.iface);
                admitted_iface = (uu___182_3712.admitted_iface);
                expect_typ = (uu___182_3712.expect_typ)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3724 =
        let uu____3727 = resolve_module_name env ns false in
        match uu____3727 with
        | None  ->
            let modules = env.modules in
            let uu____3735 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3741  ->
                      match uu____3741 with
                      | (m,uu____3745) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____3735
            then (ns, Open_namespace)
            else
              (let uu____3749 =
                 let uu____3750 =
                   let uu____3753 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____3753, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____3750 in
               Prims.raise uu____3749)
        | Some ns' -> (ns', Open_module) in
      match uu____3724 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3765 = resolve_module_name env ns false in
      match uu____3765 with
      | Some ns1 ->
          let env1 =
            push_scope_mod env (Open_module_or_namespace (ns1, Open_module)) in
          let curmod =
            let uu____3770 = current_module env1 in
            uu____3770.FStar_Ident.str in
          ((let uu____3772 = FStar_Util.smap_try_find env1.includes curmod in
            match uu____3772 with
            | None  -> ()
            | Some incl ->
                let uu____3785 =
                  let uu____3787 = FStar_ST.read incl in ns1 :: uu____3787 in
                FStar_ST.write incl uu____3785);
           (match () with
            | () ->
                let uu____3795 =
                  get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                (match uu____3795 with
                 | Some ns_trans_exports ->
                     ((let uu____3808 =
                         let uu____3819 = get_exported_id_set env1 curmod in
                         let uu____3824 =
                           get_trans_exported_id_set env1 curmod in
                         (uu____3819, uu____3824) in
                       match uu____3808 with
                       | (Some cur_exports,Some cur_trans_exports) ->
                           let update_exports k =
                             let ns_ex =
                               let uu____3864 = ns_trans_exports k in
                               FStar_ST.read uu____3864 in
                             let ex = cur_exports k in
                             (let uu____3873 =
                                let uu____3874 = FStar_ST.read ex in
                                FStar_Util.set_difference uu____3874 ns_ex in
                              FStar_ST.write ex uu____3873);
                             (match () with
                              | () ->
                                  let trans_ex = cur_trans_exports k in
                                  let uu____3884 =
                                    let uu____3885 = FStar_ST.read trans_ex in
                                    FStar_Util.set_union uu____3885 ns_ex in
                                  FStar_ST.write trans_ex uu____3884) in
                           FStar_List.iter update_exports
                             all_exported_id_kinds
                       | uu____3891 -> ());
                      (match () with | () -> env1))
                 | None  ->
                     let uu____3905 =
                       let uu____3906 =
                         let uu____3909 =
                           FStar_Util.format1
                             "include: Module %s was not prepared"
                             ns1.FStar_Ident.str in
                         (uu____3909, (FStar_Ident.range_of_lid ns1)) in
                       FStar_Errors.Error uu____3906 in
                     Prims.raise uu____3905)))
      | uu____3910 ->
          let uu____3912 =
            let uu____3913 =
              let uu____3916 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____3916, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____3913 in
          Prims.raise uu____3912
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____3926 = module_is_defined env l in
        if uu____3926
        then push_scope_mod env (Module_abbrev (x, l))
        else
          (let uu____3928 =
             let uu____3929 =
               let uu____3932 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____3932, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____3929 in
           Prims.raise uu____3928)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,quals,r) ->
                let uu____3944 = try_lookup_lid env l in
                (match uu____3944 with
                 | None  ->
                     ((let uu____3951 =
                         let uu____3952 = FStar_Options.interactive () in
                         Prims.op_Negation uu____3952 in
                       if uu____3951
                       then
                         let uu____3953 =
                           let uu____3954 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____3955 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____3954 uu____3955 in
                         FStar_Util.print_string uu____3953
                       else ());
                      FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                        ((FStar_Syntax_Syntax.Sig_declare_typ
                            (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                              quals), r)), false))
                 | Some uu____3960 -> ())
            | uu____3965 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun uu___174_3973  ->
              match uu___174_3973 with
              | FStar_Syntax_Syntax.Sig_bundle
                  (ses,quals,uu____3976,uu____3977) ->
                  if
                    (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                      ||
                      (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun uu___173_3985  ->
                            match uu___173_3985 with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid,uu____3987,uu____3988,uu____3989,uu____3990,uu____3991,uu____3992,uu____3993)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4000 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4003,uu____4004,quals,uu____4006) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4012,lbs),r,uu____4015,quals,uu____4017) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4032 =
                               let uu____4033 =
                                 let uu____4034 =
                                   let uu____4039 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4039.FStar_Syntax_Syntax.fv_name in
                                 uu____4034.FStar_Syntax_Syntax.v in
                               uu____4033.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4032))
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
                               let uu____4049 =
                                 let uu____4054 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4054.FStar_Syntax_Syntax.fv_name in
                               uu____4049.FStar_Syntax_Syntax.v in
                             let decl =
                               FStar_Syntax_Syntax.Sig_declare_typ
                                 (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                   (lb.FStar_Syntax_Syntax.lbtyp),
                                   (FStar_Syntax_Syntax.Assumption :: quals),
                                   r) in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4066 -> ()));
      (let curmod =
         let uu____4068 = current_module env in uu____4068.FStar_Ident.str in
       (let uu____4070 =
          let uu____4081 = get_exported_id_set env curmod in
          let uu____4086 = get_trans_exported_id_set env curmod in
          (uu____4081, uu____4086) in
        match uu____4070 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4126 = cur_ex eikind in FStar_ST.read uu____4126 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4134 =
                let uu____4135 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4135 in
              FStar_ST.write cur_trans_ex_set_ref uu____4134 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4141 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___183_4153 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___183_4153.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___183_4153.exported_ids);
                    trans_exported_ids = (uu___183_4153.trans_exported_ids);
                    includes = (uu___183_4153.includes);
                    sigaccum = [];
                    sigmap = (uu___183_4153.sigmap);
                    iface = (uu___183_4153.iface);
                    admitted_iface = (uu___183_4153.admitted_iface);
                    expect_typ = (uu___183_4153.expect_typ)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4166 =
       let uu____4168 = FStar_ST.read stack in env :: uu____4168 in
     FStar_ST.write stack uu____4166);
    (let uu___184_4176 = env in
     let uu____4177 = FStar_Util.smap_copy (sigmap env) in
     {
       curmodule = (uu___184_4176.curmodule);
       curmonad = (uu___184_4176.curmonad);
       modules = (uu___184_4176.modules);
       scope_mods = (uu___184_4176.scope_mods);
       exported_ids = (uu___184_4176.exported_ids);
       trans_exported_ids = (uu___184_4176.trans_exported_ids);
       includes = (uu___184_4176.includes);
       sigaccum = (uu___184_4176.sigaccum);
       sigmap = uu____4177;
       iface = (uu___184_4176.iface);
       admitted_iface = (uu___184_4176.admitted_iface);
       expect_typ = (uu___184_4176.expect_typ)
     })
let pop: Prims.unit -> env =
  fun uu____4185  ->
    let uu____4186 = FStar_ST.read stack in
    match uu____4186 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4199 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4205 = FStar_ST.read stack in
     match uu____4205 with
     | uu____4210::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4217 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4224  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4236 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4238 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4256 = FStar_Util.smap_try_find sm' k in
              match uu____4256 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,q,r) ->
                          FStar_Syntax_Syntax.Sig_declare_typ
                            (l, u, t, (FStar_Syntax_Syntax.Assumption :: q),
                              r)
                      | uu____4277 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4280 -> ()));
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
            (let uu____4324 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4324);
            (match () with
             | () ->
                 ((let uu____4329 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4329);
                  (match () with
                   | () ->
                       ((let uu____4334 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4334);
                        (match () with
                         | () ->
                             let uu___185_4343 = env1 in
                             let uu____4344 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___185_4343.curmonad);
                               modules = (uu___185_4343.modules);
                               scope_mods = uu____4344;
                               exported_ids = (uu___185_4343.exported_ids);
                               trans_exported_ids =
                                 (uu___185_4343.trans_exported_ids);
                               includes = (uu___185_4343.includes);
                               sigaccum = (uu___185_4343.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___185_4343.expect_typ)
                             }))))) in
          let uu____4347 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4359  ->
                    match uu____4359 with
                    | (l,uu____4363) -> FStar_Ident.lid_equals l mname)) in
          match uu____4347 with
          | None  -> let uu____4368 = prep env in (uu____4368, false)
          | Some (uu____4369,m) ->
              ((let uu____4374 =
                  (let uu____4375 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4375) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4374
                then
                  let uu____4376 =
                    let uu____4377 =
                      let uu____4380 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4380, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4377 in
                  Prims.raise uu____4376
                else ());
               (let uu____4382 = let uu____4383 = push env in prep uu____4383 in
                (uu____4382, true)))
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
          let uu___186_4391 = env in
          {
            curmodule = (uu___186_4391.curmodule);
            curmonad = (Some mname);
            modules = (uu___186_4391.modules);
            scope_mods = (uu___186_4391.scope_mods);
            exported_ids = (uu___186_4391.exported_ids);
            trans_exported_ids = (uu___186_4391.trans_exported_ids);
            includes = (uu___186_4391.includes);
            sigaccum = (uu___186_4391.sigaccum);
            sigmap = (uu___186_4391.sigmap);
            iface = (uu___186_4391.iface);
            admitted_iface = (uu___186_4391.admitted_iface);
            expect_typ = (uu___186_4391.expect_typ)
          }
let fail_or env lookup lid =
  let uu____4416 = lookup lid in
  match uu____4416 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4422  ->
             match uu____4422 with
             | (lid1,uu____4426) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4433 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4433
               (FStar_Ident.range_of_lid lid) in
           let uu____4434 = resolve_module_name env modul true in
           match uu____4434 with
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
  let uu____4461 = lookup id in
  match uu____4461 with
  | None  ->
      Prims.raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r