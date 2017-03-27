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
      | None  -> let uu____369 = current_module env in qual uu____369 id
      | Some monad ->
          let uu____371 =
            let uu____372 = current_module env in qual uu____372 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____371 id
let new_sigmap uu____380 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____383  ->
    let uu____384 = new_sigmap () in
    let uu____386 = new_sigmap () in
    let uu____388 = new_sigmap () in
    let uu____394 = new_sigmap () in
    {
      curmodule = None;
      curmonad = None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____384;
      trans_exported_ids = uu____386;
      includes = uu____388;
      sigaccum = [];
      sigmap = uu____394;
      iface = false;
      admitted_iface = false;
      expect_typ = false
    }
let sigmap: env -> (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap =
  fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____413  ->
         match uu____413 with
         | (m,uu____417) ->
             FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___175_425 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___175_425.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___176_426 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___176_426.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___176_426.FStar_Syntax_Syntax.sort)
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
        (fun uu____472  ->
           match uu____472 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____486 =
                   let uu____487 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____487 dd dq in
                 Some uu____486
               else None) in
    match t with | Some v1 -> Some (v1, false) | None  -> None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____517 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____541 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____552 -> false
let option_of_cont k_ignore uu___144_571 =
  match uu___144_571 with
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
        (fun uu____616  ->
           match uu____616 with
           | (f,uu____621) ->
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
  fun uu___145_657  ->
    match uu___145_657 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___146_706 =
    match uu___146_706 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
          let uu____714 = get_exported_id_set env mname in
          match uu____714 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____730 = mex eikind in FStar_ST.read uu____730 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____737 = FStar_Util.smap_try_find env.includes mname in
          match uu____737 with
          | None  -> []
          | Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
          then let uu____757 = qual modul id in find_in_module uu____757
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____760 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___147_764  ->
    match uu___147_764 with | Exported_id_field  -> true | uu____765 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___148_854 =
    match uu___148_854 with
    | (id',uu____856,uu____857) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___149_861 =
    match uu___149_861 with
    | (id',uu____863,uu____864) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____867 = current_module env in FStar_Ident.ids_of_lid uu____867 in
  let proc uu___150_872 =
    match uu___150_872 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____877) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____880 = FStar_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____880 id
    | uu____883 -> Cont_ignore in
  let rec aux uu___151_889 =
    match uu___151_889 with
    | a::q ->
        let uu____895 = proc a in
        option_of_cont (fun uu____897  -> aux q) uu____895
    | [] ->
        let uu____898 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____900  -> None) uu____898 in
  aux env.scope_mods
let found_local_binding r uu____919 =
  match uu____919 with
  | (id',x,mut) -> let uu____926 = bv_to_name x r in (uu____926, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____963 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____963 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found
let try_lookup_id:
  env ->
    FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  =
  fun env  ->
    fun id  ->
      let uu____985 = unmangleOpName id in
      match uu____985 with
      | Some f -> Some f
      | uu____999 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1006 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1006) (fun uu____1011  -> Cont_fail)
            (fun uu____1014  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1021  -> fun uu____1022  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1029  -> fun uu____1030  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1082 ->
        let lid = qualify env id in
        let uu____1084 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____1084 with
         | Some r -> let uu____1097 = k_global_def lid r in Some uu____1097
         | None  -> None)
    | None  -> None in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1110 = current_module env in qual uu____1110 id in
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
           let uu____1119 = current_module env in
           FStar_Ident.lid_equals lid uu____1119)
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
        let rec aux uu___152_1143 =
          match uu___152_1143 with
          | [] ->
              let uu____1146 = module_is_defined env lid in
              if uu____1146 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1153 =
                  let uu____1155 = FStar_Ident.path_of_lid ns in
                  let uu____1157 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1155 uu____1157 in
                FStar_Ident.lid_of_path uu____1153
                  (FStar_Ident.range_of_lid lid) in
              let uu____1159 = module_is_defined env new_lid in
              if uu____1159 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1164 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1168::q -> aux q in
        aux env.scope_mods
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___153_1177  ->
           match uu___153_1177 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1179 -> false) env.scope_mods
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
                 let uu____1234 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____1234
                   (FStar_Util.map_option
                      (fun uu____1258  ->
                         match uu____1258 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____1275 =
          is_full_path &&
            (let uu____1276 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____1276) in
        if uu____1275
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1293 = aux ns_rev_prefix ns_last_id in
               (match uu____1293 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1406::uu____1407 ->
      let uu____1409 =
        let uu____1411 =
          let uu____1412 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____1412 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____1411 true in
      (match uu____1409 with
       | None  -> None
       | Some modul ->
           let uu____1415 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____1417  -> None) uu____1415)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___154_1432 =
  match uu___154_1432 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1511 = k_global_def lid1 def in cont_of_option k uu____1511 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1532 = k_local_binding l in
       cont_of_option Cont_fail uu____1532)
    (fun r  ->
       let uu____1535 = k_rec_binding r in
       cont_of_option Cont_fail uu____1535) (fun uu____1537  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual Prims.option =
  fun uu___156_1541  ->
    match uu___156_1541 with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1543,uu____1544,uu____1545,l,uu____1547,quals,uu____1549,uu____1550)
        ->
        let qopt =
          FStar_Util.find_map quals
            (fun uu___155_1557  ->
               match uu___155_1557 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1559,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1566 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____1570,uu____1571,uu____1572,quals,uu____1574) -> None
    | uu____1577 -> None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1586 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____1590 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____1590 then Some fv else None) in
      FStar_All.pipe_right uu____1586 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1604 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____1604 ns)
let try_lookup_name:
  Prims.bool ->
    Prims.bool -> env -> FStar_Ident.lident -> foundname Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___160_1629 =
            match uu___160_1629 with
            | (uu____1633,true ) when exclude_interf -> None
            | (se,uu____1635) ->
                (match se with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1637 ->
                     let uu____1649 =
                       let uu____1650 =
                         let uu____1653 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____1653, false) in
                       Term_name uu____1650 in
                     Some uu____1649
                 | FStar_Syntax_Syntax.Sig_datacon uu____1654 ->
                     let uu____1665 =
                       let uu____1666 =
                         let uu____1669 =
                           let uu____1670 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1670 in
                         (uu____1669, false) in
                       Term_name uu____1666 in
                     Some uu____1665
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1672,lbs),uu____1674,uu____1675,uu____1676,uu____1677)
                     ->
                     let fv = lb_fv lbs source_lid in
                     let uu____1690 =
                       let uu____1691 =
                         let uu____1694 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____1694, false) in
                       Term_name uu____1691 in
                     Some uu____1690
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1696,uu____1697,quals,uu____1699) ->
                     let uu____1702 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___157_1704  ->
                                  match uu___157_1704 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1705 -> false))) in
                     if uu____1702
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____1709 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___158_1711  ->
                                         match uu___158_1711 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1714 -> false)))) in
                         if uu____1709
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____1716 =
                         FStar_Util.find_map quals
                           (fun uu___159_1718  ->
                              match uu___159_1718 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1721 -> None) in
                       (match uu____1716 with
                        | Some refl_monad ->
                            let refl_const =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reflect refl_monad)))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
                        | uu____1737 ->
                            let uu____1739 =
                              let uu____1740 =
                                let uu____1743 =
                                  let uu____1744 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____1744 in
                                (uu____1743, false) in
                              Term_name uu____1740 in
                            Some uu____1739)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,_)
                   |FStar_Syntax_Syntax.Sig_new_effect (ne,_) ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1750 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1760 -> None) in
          let k_local_binding r =
            let uu____1772 =
              let uu____1773 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____1773 in
            Some uu____1772 in
          let k_rec_binding uu____1783 =
            match uu____1783 with
            | (id,l,dd) ->
                let uu____1791 =
                  let uu____1792 =
                    let uu____1795 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____1795, false) in
                  Term_name uu____1792 in
                Some uu____1791 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____1799 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____1799 with
                 | Some f -> Some (Term_name f)
                 | uu____1809 -> None)
            | uu____1813 -> None in
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
        let uu____1833 = try_lookup_name true exclude_interf env lid in
        match uu____1833 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____1842 -> None
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1853 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1853 with | Some (o,l1) -> Some l1 | uu____1862 -> None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list)
        Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____1876 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1876 with
      | Some (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1885),l1) ->
          Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,uu____1894),l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          (FStar_Syntax_Syntax.Sig_effect_abbrev
           (uu____1902,uu____1903,uu____1904,uu____1905,uu____1906,cattributes,uu____1908),l1)
          -> Some (l1, cattributes)
      | uu____1920 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      let uu____1934 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1934 with
      | Some (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1940),uu____1941)
          -> Some ne
      | Some
          (FStar_Syntax_Syntax.Sig_new_effect_for_free
           (ne,uu____1945),uu____1946)
          -> Some ne
      | uu____1949 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____1959 = try_lookup_effect_name env lid in
      match uu____1959 with | None  -> false | Some uu____1961 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1969 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1969 with
      | Some
          (FStar_Syntax_Syntax.Sig_effect_abbrev
           (l',uu____1975,uu____1976,uu____1977,uu____1978,uu____1979,uu____1980),uu____1981)
          ->
          let rec aux new_name =
            let uu____1993 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____1993 with
            | None  -> None
            | Some (s,uu____2003) ->
                (match s with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,_)
                   |FStar_Syntax_Syntax.Sig_new_effect (ne,_) ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____2010,uu____2011,uu____2012,cmp,uu____2014,uu____2015,uu____2016)
                     ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp in
                     aux l''
                 | uu____2022 -> None) in
          aux l'
      | Some (uu____2023,l') -> Some l'
      | uu____2027 -> None
let lookup_letbinding_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___161_2048 =
        match uu___161_2048 with
        | (FStar_Syntax_Syntax.Sig_declare_typ
           (lid2,uu____2054,uu____2055,quals,uu____2057),uu____2058) ->
            Some quals
        | uu____2062 -> None in
      let uu____2066 =
        resolve_in_open_namespaces' env lid (fun uu____2070  -> None)
          (fun uu____2072  -> None) k_global_def in
      match uu____2066 with | Some quals -> quals | uu____2078 -> []
let try_lookup_module:
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul Prims.option =
  fun env  ->
    fun path  ->
      let uu____2090 =
        FStar_List.tryFind
          (fun uu____2096  ->
             match uu____2096 with
             | (mlid,modul) ->
                 let uu____2101 = FStar_Ident.path_of_lid mlid in
                 uu____2101 = path) env.modules in
      match uu____2090 with
      | Some (uu____2105,modul) -> Some modul
      | None  -> None
let try_lookup_let:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___162_2127 =
        match uu___162_2127 with
        | (FStar_Syntax_Syntax.Sig_let
           ((uu____2131,lbs),uu____2133,uu____2134,uu____2135,uu____2136),uu____2137)
            ->
            let fv = lb_fv lbs lid1 in
            let uu____2150 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual in
            Some uu____2150
        | uu____2151 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2154  -> None)
        (fun uu____2155  -> None) k_global_def
let try_lookup_definition:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___163_2174 =
        match uu___163_2174 with
        | (FStar_Syntax_Syntax.Sig_let
           (lbs,uu____2181,uu____2182,uu____2183,uu____2184),uu____2185) ->
            FStar_Util.find_map (Prims.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2202 -> None)
        | uu____2207 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2214  -> None)
        (fun uu____2217  -> None) k_global_def
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
          let uu____2244 = try_lookup_name any_val exclude_interf env lid in
          match uu____2244 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2253 -> None
let try_lookup_lid:
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l
let try_lookup_lid_no_resolve:
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___177_2276 = env in
        {
          curmodule = (uu___177_2276.curmodule);
          curmonad = (uu___177_2276.curmonad);
          modules = (uu___177_2276.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___177_2276.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___177_2276.sigaccum);
          sigmap = (uu___177_2276.sigmap);
          iface = (uu___177_2276.iface);
          admitted_iface = (uu___177_2276.admitted_iface);
          expect_typ = (uu___177_2276.expect_typ)
        } in
      try_lookup_lid env' l
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___165_2293 =
        match uu___165_2293 with
        | (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2297,uu____2298,uu____2299,quals,uu____2301),uu____2302) ->
            let uu____2305 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___164_2307  ->
                      match uu___164_2307 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2308 -> false)) in
            if uu____2305
            then
              let uu____2310 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2310
            else None
        | (FStar_Syntax_Syntax.Sig_datacon uu____2312,uu____2313) ->
            let uu____2324 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2324
        | uu____2325 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2328  -> None)
        (fun uu____2329  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___166_2348 =
        match uu___166_2348 with
        | (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____2353,uu____2354,uu____2355,uu____2356,uu____2357,datas,uu____2359,uu____2360),uu____2361)
            -> Some datas
        | uu____2369 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2374  -> None)
        (fun uu____2376  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____2410 =
    let uu____2411 =
      let uu____2414 =
        let uu____2416 = FStar_ST.read record_cache in
        FStar_List.hd uu____2416 in
      let uu____2424 = FStar_ST.read record_cache in uu____2414 :: uu____2424 in
    FStar_ST.write record_cache uu____2411 in
  let pop1 uu____2439 =
    let uu____2440 =
      let uu____2443 = FStar_ST.read record_cache in FStar_List.tl uu____2443 in
    FStar_ST.write record_cache uu____2440 in
  let peek uu____2459 =
    let uu____2460 = FStar_ST.read record_cache in FStar_List.hd uu____2460 in
  let insert r =
    let uu____2472 =
      let uu____2475 = let uu____2477 = peek () in r :: uu____2477 in
      let uu____2479 =
        let uu____2482 = FStar_ST.read record_cache in
        FStar_List.tl uu____2482 in
      uu____2475 :: uu____2479 in
    FStar_ST.write record_cache uu____2472 in
  let commit1 uu____2498 =
    let uu____2499 = FStar_ST.read record_cache in
    match uu____2499 with
    | hd1::uu____2507::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2520 -> failwith "Impossible" in
  let filter1 uu____2526 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____2533 =
           let uu____2536 = FStar_ST.read record_cache in filtered ::
             uu____2536 in
         FStar_ST.write record_cache uu____2533) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____2610 = record_cache_aux_with_filter in
  match uu____2610 with | (aux,uu____2648) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____2687 = record_cache_aux_with_filter in
  match uu____2687 with | (uu____2710,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____2750 = record_cache_aux in
  match uu____2750 with
  | (push1,uu____2770,uu____2771,uu____2772,uu____2773) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____2798 = record_cache_aux in
  match uu____2798 with
  | (uu____2817,pop1,uu____2819,uu____2820,uu____2821) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____2847 = record_cache_aux in
  match uu____2847 with
  | (uu____2867,uu____2868,peek,uu____2870,uu____2871) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____2896 = record_cache_aux in
  match uu____2896 with
  | (uu____2915,uu____2916,uu____2917,insert,uu____2919) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____2944 = record_cache_aux in
  match uu____2944 with
  | (uu____2963,uu____2964,uu____2965,uu____2966,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun uu___170_3001  ->
        match uu___170_3001 with
        | FStar_Syntax_Syntax.Sig_bundle
            (sigs,uu____3006,uu____3007,uu____3008) ->
            let is_rec =
              FStar_Util.for_some
                (fun uu___167_3019  ->
                   match uu___167_3019 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____3022 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___168_3030  ->
                      match uu___168_3030 with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3032,uu____3033,uu____3034,uu____3035,uu____3036,uu____3037,uu____3038)
                          -> FStar_Ident.lid_equals dc lid
                      | uu____3043 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___169_3045  ->
                    match uu___169_3045 with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (typename,univs,parms,uu____3049,uu____3050,dc::[],tags,uu____3053)
                        ->
                        let uu____3059 =
                          let uu____3060 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3060 in
                        (match uu____3059 with
                         | FStar_Syntax_Syntax.Sig_datacon
                             (constrname,uu____3064,t,uu____3066,uu____3067,uu____3068,uu____3069,uu____3070)
                             ->
                             let uu____3075 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3075 with
                              | (formals,uu____3084) ->
                                  let is_rec1 = is_rec tags in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3110  ->
                                            match uu____3110 with
                                            | (x,q) ->
                                                let uu____3118 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec1 &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3118
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3149  ->
                                            match uu____3149 with
                                            | (x,q) ->
                                                let uu____3158 =
                                                  if is_rec1
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____3158,
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
                                  ((let uu____3170 =
                                      let uu____3172 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3172 in
                                    FStar_ST.write new_globs uu____3170);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3188 =
                                            match uu____3188 with
                                            | (id,uu____3194) ->
                                                let modul =
                                                  let uu____3200 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3200.FStar_Ident.str in
                                                let uu____3201 =
                                                  get_exported_id_set e modul in
                                                (match uu____3201 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____3217 =
                                                         let uu____3218 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3218 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3217);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3225 =
                                                               let uu____3226
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____3226.FStar_Ident.ident in
                                                             uu____3225.FStar_Ident.idText in
                                                           let uu____3228 =
                                                             let uu____3229 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3229 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3228))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3242 -> ())
                    | uu____3243 -> ()))
        | uu____3244 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3257 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3257 with
        | (ns,id) ->
            let uu____3267 = peek_record_cache () in
            FStar_Util.find_map uu____3267
              (fun record  ->
                 let uu____3270 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3273  -> None) uu____3270) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3274  -> Cont_ignore) (fun uu____3275  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3278 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3278)
        (fun k  -> fun uu____3281  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let uu____3290 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3290 with
      | Some r when r.is_record -> Some r
      | uu____3294 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3305 = try_lookup_record_by_field_name env lid in
        match uu____3305 with
        | Some record' when
            let uu____3308 =
              let uu____3309 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3309 in
            let uu____3311 =
              let uu____3312 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3312 in
            uu____3308 = uu____3311 ->
            let uu____3314 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3316  -> Cont_ok ()) in
            (match uu____3314 with
             | Cont_ok uu____3317 -> true
             | uu____3318 -> false)
        | uu____3320 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) Prims.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____3331 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3331 with
      | Some r ->
          let uu____3337 =
            let uu____3340 =
              let uu____3341 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3341
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3340, (r.is_record)) in
          Some uu____3337
      | uu____3344 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3353  ->
    let uu____3354 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3354
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3365  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___171_3374  ->
      match uu___171_3374 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___172_3394 =
            match uu___172_3394 with
            | Rec_binding uu____3395 -> true
            | uu____3396 -> false in
          let this_env =
            let uu___178_3398 = env in
            let uu____3399 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___178_3398.curmodule);
              curmonad = (uu___178_3398.curmonad);
              modules = (uu___178_3398.modules);
              scope_mods = uu____3399;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___178_3398.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___178_3398.sigaccum);
              sigmap = (uu___178_3398.sigmap);
              iface = (uu___178_3398.iface);
              admitted_iface = (uu___178_3398.admitted_iface);
              expect_typ = (uu___178_3398.expect_typ)
            } in
          let uu____3401 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3401 with | None  -> true | Some uu____3407 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___179_3418 = env in
      {
        curmodule = (uu___179_3418.curmodule);
        curmonad = (uu___179_3418.curmonad);
        modules = (uu___179_3418.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___179_3418.exported_ids);
        trans_exported_ids = (uu___179_3418.trans_exported_ids);
        includes = (uu___179_3418.includes);
        sigaccum = (uu___179_3418.sigaccum);
        sigmap = (uu___179_3418.sigmap);
        iface = (uu___179_3418.iface);
        admitted_iface = (uu___179_3418.admitted_iface);
        expect_typ = (uu___179_3418.expect_typ)
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
        let uu____3457 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____3457
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
          | Some (se,uu____3477) ->
              let uu____3480 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____3480 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____3485 =
          let uu____3486 =
            let uu____3489 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____3489, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____3486 in
        Prims.raise uu____3485 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____3496 =
          match s with
          | FStar_Syntax_Syntax.Sig_let uu____3501 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3510 -> (true, true)
          | uu____3518 -> (false, false) in
        match uu____3496 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____3523 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3526 =
                     let uu____3527 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____3527 in
                   if uu____3526 then Some l else None) in
            (match uu____3523 with
             | Some l when
                 let uu____3531 = FStar_Options.interactive () in
                 Prims.op_Negation uu____3531 -> err l
             | uu____3532 ->
                 (extract_record env globals s;
                  (let uu___180_3537 = env in
                   {
                     curmodule = (uu___180_3537.curmodule);
                     curmonad = (uu___180_3537.curmonad);
                     modules = (uu___180_3537.modules);
                     scope_mods = (uu___180_3537.scope_mods);
                     exported_ids = (uu___180_3537.exported_ids);
                     trans_exported_ids = (uu___180_3537.trans_exported_ids);
                     includes = (uu___180_3537.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___180_3537.sigmap);
                     iface = (uu___180_3537.iface);
                     admitted_iface = (uu___180_3537.admitted_iface);
                     expect_typ = (uu___180_3537.expect_typ)
                   }))) in
      let env2 =
        let uu___181_3539 = env1 in
        let uu____3540 = FStar_ST.read globals in
        {
          curmodule = (uu___181_3539.curmodule);
          curmonad = (uu___181_3539.curmonad);
          modules = (uu___181_3539.modules);
          scope_mods = uu____3540;
          exported_ids = (uu___181_3539.exported_ids);
          trans_exported_ids = (uu___181_3539.trans_exported_ids);
          includes = (uu___181_3539.includes);
          sigaccum = (uu___181_3539.sigaccum);
          sigmap = (uu___181_3539.sigmap);
          iface = (uu___181_3539.iface);
          admitted_iface = (uu___181_3539.admitted_iface);
          expect_typ = (uu___181_3539.expect_typ)
        } in
      let uu____3545 =
        match s with
        | FStar_Syntax_Syntax.Sig_bundle
            (ses,uu____3559,uu____3560,uu____3561) ->
            let uu____3568 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____3568)
        | uu____3582 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____3545 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3612  ->
                   match uu____3612 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3623 =
                                  let uu____3625 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3625 in
                                FStar_ST.write globals uu____3623);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3634 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____3634.FStar_Ident.str in
                                    ((let uu____3636 =
                                        get_exported_id_set env3 modul in
                                      match uu____3636 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____3651 =
                                            let uu____3652 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3652 in
                                          FStar_ST.write my_exported_ids
                                            uu____3651
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
              let uu___182_3664 = env3 in
              let uu____3665 = FStar_ST.read globals in
              {
                curmodule = (uu___182_3664.curmodule);
                curmonad = (uu___182_3664.curmonad);
                modules = (uu___182_3664.modules);
                scope_mods = uu____3665;
                exported_ids = (uu___182_3664.exported_ids);
                trans_exported_ids = (uu___182_3664.trans_exported_ids);
                includes = (uu___182_3664.includes);
                sigaccum = (uu___182_3664.sigaccum);
                sigmap = (uu___182_3664.sigmap);
                iface = (uu___182_3664.iface);
                admitted_iface = (uu___182_3664.admitted_iface);
                expect_typ = (uu___182_3664.expect_typ)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3676 =
        let uu____3679 = resolve_module_name env ns false in
        match uu____3679 with
        | None  ->
            let modules = env.modules in
            let uu____3687 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3693  ->
                      match uu____3693 with
                      | (m,uu____3697) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____3687
            then (ns, Open_namespace)
            else
              (let uu____3701 =
                 let uu____3702 =
                   let uu____3705 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____3705, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____3702 in
               Prims.raise uu____3701)
        | Some ns' -> (ns', Open_module) in
      match uu____3676 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3717 = resolve_module_name env ns false in
      match uu____3717 with
      | Some ns1 ->
          let env1 =
            push_scope_mod env (Open_module_or_namespace (ns1, Open_module)) in
          let curmod =
            let uu____3722 = current_module env1 in
            uu____3722.FStar_Ident.str in
          ((let uu____3724 = FStar_Util.smap_try_find env1.includes curmod in
            match uu____3724 with
            | None  -> ()
            | Some incl ->
                let uu____3737 =
                  let uu____3739 = FStar_ST.read incl in ns1 :: uu____3739 in
                FStar_ST.write incl uu____3737);
           (match () with
            | () ->
                let uu____3747 =
                  get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                (match uu____3747 with
                 | Some ns_trans_exports ->
                     ((let uu____3760 =
                         let uu____3771 = get_exported_id_set env1 curmod in
                         let uu____3776 =
                           get_trans_exported_id_set env1 curmod in
                         (uu____3771, uu____3776) in
                       match uu____3760 with
                       | (Some cur_exports,Some cur_trans_exports) ->
                           let update_exports k =
                             let ns_ex =
                               let uu____3816 = ns_trans_exports k in
                               FStar_ST.read uu____3816 in
                             let ex = cur_exports k in
                             (let uu____3825 =
                                let uu____3826 = FStar_ST.read ex in
                                FStar_Util.set_difference uu____3826 ns_ex in
                              FStar_ST.write ex uu____3825);
                             (match () with
                              | () ->
                                  let trans_ex = cur_trans_exports k in
                                  let uu____3836 =
                                    let uu____3837 = FStar_ST.read ex in
                                    FStar_Util.set_union uu____3837 ns_ex in
                                  FStar_ST.write trans_ex uu____3836) in
                           FStar_List.iter update_exports
                             all_exported_id_kinds
                       | uu____3843 -> ());
                      (match () with | () -> env1))
                 | None  ->
                     let uu____3857 =
                       let uu____3858 =
                         let uu____3861 =
                           FStar_Util.format1
                             "include: Module %s was not prepared"
                             ns1.FStar_Ident.str in
                         (uu____3861, (FStar_Ident.range_of_lid ns1)) in
                       FStar_Errors.Error uu____3858 in
                     Prims.raise uu____3857)))
      | uu____3862 ->
          let uu____3864 =
            let uu____3865 =
              let uu____3868 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____3868, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____3865 in
          Prims.raise uu____3864
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____3878 = module_is_defined env l in
        if uu____3878
        then push_scope_mod env (Module_abbrev (x, l))
        else
          (let uu____3880 =
             let uu____3881 =
               let uu____3884 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____3884, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____3881 in
           Prims.raise uu____3880)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,quals,r) ->
                let uu____3896 = try_lookup_lid env l in
                (match uu____3896 with
                 | None  ->
                     ((let uu____3903 =
                         let uu____3904 = FStar_Options.interactive () in
                         Prims.op_Negation uu____3904 in
                       if uu____3903
                       then
                         let uu____3905 =
                           let uu____3906 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____3907 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____3906 uu____3907 in
                         FStar_Util.print_string uu____3905
                       else ());
                      FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                        ((FStar_Syntax_Syntax.Sig_declare_typ
                            (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                              quals), r)), false))
                 | Some uu____3912 -> ())
            | uu____3917 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun uu___174_3925  ->
              match uu___174_3925 with
              | FStar_Syntax_Syntax.Sig_bundle
                  (ses,quals,uu____3928,uu____3929) ->
                  if
                    (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                      ||
                      (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun uu___173_3937  ->
                            match uu___173_3937 with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid,uu____3939,uu____3940,uu____3941,uu____3942,uu____3943,uu____3944,uu____3945)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____3952 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____3955,uu____3956,quals,uu____3958) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____3964,lbs),r,uu____3967,quals,uu____3969) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____3984 =
                               let uu____3985 =
                                 let uu____3986 =
                                   let uu____3991 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____3991.FStar_Syntax_Syntax.fv_name in
                                 uu____3986.FStar_Syntax_Syntax.v in
                               uu____3985.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____3984))
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
                               let uu____4001 =
                                 let uu____4006 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4006.FStar_Syntax_Syntax.fv_name in
                               uu____4001.FStar_Syntax_Syntax.v in
                             let decl =
                               FStar_Syntax_Syntax.Sig_declare_typ
                                 (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                   (lb.FStar_Syntax_Syntax.lbtyp),
                                   (FStar_Syntax_Syntax.Assumption :: quals),
                                   r) in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4018 -> ()));
      (let curmod =
         let uu____4020 = current_module env in uu____4020.FStar_Ident.str in
       (let uu____4022 =
          let uu____4033 = get_exported_id_set env curmod in
          let uu____4038 = get_trans_exported_id_set env curmod in
          (uu____4033, uu____4038) in
        match uu____4022 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4078 = cur_ex eikind in FStar_ST.read uu____4078 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4086 =
                let uu____4087 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4087 in
              FStar_ST.write cur_trans_ex_set_ref uu____4086 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4093 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___183_4105 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___183_4105.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___183_4105.exported_ids);
                    trans_exported_ids = (uu___183_4105.trans_exported_ids);
                    includes = (uu___183_4105.includes);
                    sigaccum = [];
                    sigmap = (uu___183_4105.sigmap);
                    iface = (uu___183_4105.iface);
                    admitted_iface = (uu___183_4105.admitted_iface);
                    expect_typ = (uu___183_4105.expect_typ)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4118 =
       let uu____4120 = FStar_ST.read stack in env :: uu____4120 in
     FStar_ST.write stack uu____4118);
    (let uu___184_4128 = env in
     let uu____4129 = FStar_Util.smap_copy (sigmap env) in
     {
       curmodule = (uu___184_4128.curmodule);
       curmonad = (uu___184_4128.curmonad);
       modules = (uu___184_4128.modules);
       scope_mods = (uu___184_4128.scope_mods);
       exported_ids = (uu___184_4128.exported_ids);
       trans_exported_ids = (uu___184_4128.trans_exported_ids);
       includes = (uu___184_4128.includes);
       sigaccum = (uu___184_4128.sigaccum);
       sigmap = uu____4129;
       iface = (uu___184_4128.iface);
       admitted_iface = (uu___184_4128.admitted_iface);
       expect_typ = (uu___184_4128.expect_typ)
     })
let pop: Prims.unit -> env =
  fun uu____4137  ->
    let uu____4138 = FStar_ST.read stack in
    match uu____4138 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4151 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4157 = FStar_ST.read stack in
     match uu____4157 with
     | uu____4162::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4169 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4176  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4188 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4190 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4208 = FStar_Util.smap_try_find sm' k in
              match uu____4208 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,q,r) ->
                          FStar_Syntax_Syntax.Sig_declare_typ
                            (l, u, t, (FStar_Syntax_Syntax.Assumption :: q),
                              r)
                      | uu____4229 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4232 -> ()));
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
            (let uu____4276 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4276);
            (match () with
             | () ->
                 ((let uu____4281 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4281);
                  (match () with
                   | () ->
                       ((let uu____4286 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4286);
                        (match () with
                         | () ->
                             let uu___185_4295 = env1 in
                             let uu____4296 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___185_4295.curmonad);
                               modules = (uu___185_4295.modules);
                               scope_mods = uu____4296;
                               exported_ids = (uu___185_4295.exported_ids);
                               trans_exported_ids =
                                 (uu___185_4295.trans_exported_ids);
                               includes = (uu___185_4295.includes);
                               sigaccum = (uu___185_4295.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___185_4295.expect_typ)
                             }))))) in
          let uu____4299 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4311  ->
                    match uu____4311 with
                    | (l,uu____4315) -> FStar_Ident.lid_equals l mname)) in
          match uu____4299 with
          | None  -> let uu____4320 = prep env in (uu____4320, false)
          | Some (uu____4321,m) ->
              ((let uu____4326 =
                  (let uu____4327 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4327) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4326
                then
                  let uu____4328 =
                    let uu____4329 =
                      let uu____4332 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4332, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4329 in
                  Prims.raise uu____4328
                else ());
               (let uu____4334 = let uu____4335 = push env in prep uu____4335 in
                (uu____4334, true)))
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
          let uu___186_4343 = env in
          {
            curmodule = (uu___186_4343.curmodule);
            curmonad = (Some mname);
            modules = (uu___186_4343.modules);
            scope_mods = (uu___186_4343.scope_mods);
            exported_ids = (uu___186_4343.exported_ids);
            trans_exported_ids = (uu___186_4343.trans_exported_ids);
            includes = (uu___186_4343.includes);
            sigaccum = (uu___186_4343.sigaccum);
            sigmap = (uu___186_4343.sigmap);
            iface = (uu___186_4343.iface);
            admitted_iface = (uu___186_4343.admitted_iface);
            expect_typ = (uu___186_4343.expect_typ)
          }
let fail_or env lookup lid =
  let uu____4368 = lookup lid in
  match uu____4368 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4374  ->
             match uu____4374 with
             | (lid1,uu____4378) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4385 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4385
               (FStar_Ident.range_of_lid lid) in
           let uu____4386 = resolve_module_name env modul true in
           match uu____4386 with
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
  let uu____4413 = lookup id in
  match uu____4413 with
  | None  ->
      Prims.raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r