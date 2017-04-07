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
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap;}
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ* Prims.bool)
  | Eff_name of (FStar_Syntax_Syntax.sigelt* FStar_Ident.lident)
let uu___is_Term_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____324 -> false
let __proj__Term_name__item___0:
  foundname -> (FStar_Syntax_Syntax.typ* Prims.bool) =
  fun projectee  -> match projectee with | Term_name _0 -> _0
let uu___is_Eff_name: foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____344 -> false
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
      let uu____367 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name in
      match uu____367 with
      | None  -> []
      | Some exported_id_set ->
          let uu____371 =
            let uu____372 = exported_id_set Exported_id_term_type in
            FStar_ST.read uu____372 in
          FStar_All.pipe_right uu____371 FStar_Util.set_elements
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
      | None  -> let uu____398 = current_module env in qual uu____398 id
      | Some monad ->
          let uu____400 =
            let uu____401 = current_module env in qual uu____401 monad in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____400 id
let new_sigmap uu____409 = FStar_Util.smap_create (Prims.parse_int "100")
let empty_env: Prims.unit -> env =
  fun uu____412  ->
    let uu____413 = new_sigmap () in
    let uu____415 = new_sigmap () in
    let uu____417 = new_sigmap () in
    let uu____423 = new_sigmap () in
    let uu____429 = new_sigmap () in
    {
      curmodule = None;
      curmonad = None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____413;
      trans_exported_ids = uu____415;
      includes = uu____417;
      sigaccum = [];
      sigmap = uu____423;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____429
    }
let sigmap: env -> (FStar_Syntax_Syntax.sigelt* Prims.bool) FStar_Util.smap =
  fun env  -> env.sigmap
let has_all_in_scope: env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____444  ->
         match uu____444 with
         | (m,uu____448) ->
             FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid) env.modules
let set_bv_range:
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___166_456 = bv.FStar_Syntax_Syntax.ppname in
        {
          FStar_Ident.idText = (uu___166_456.FStar_Ident.idText);
          FStar_Ident.idRange = r
        } in
      let uu___167_457 = bv in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___167_457.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___167_457.FStar_Syntax_Syntax.sort)
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
        (fun uu____503  ->
           match uu____503 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____517 =
                   let uu____518 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange in
                   FStar_Syntax_Syntax.fvar uu____518 dd dq in
                 Some uu____517
               else None) in
    match t with | Some v1 -> Some (v1, false) | None  -> None
type 'a cont_t =
  | Cont_ok of 'a
  | Cont_fail
  | Cont_ignore
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____548 -> false
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____572 -> false
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____583 -> false
let option_of_cont k_ignore uu___139_602 =
  match uu___139_602 with
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
        (fun uu____647  ->
           match uu____647 with
           | (f,uu____652) ->
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
  fun uu___140_688  ->
    match uu___140_688 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText in
  let rec aux uu___141_737 =
    match uu___141_737 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str in
        let not_shadowed =
          let uu____745 = get_exported_id_set env mname in
          match uu____745 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____761 = mex eikind in FStar_ST.read uu____761 in
              FStar_Util.set_mem idstr mexports in
        let mincludes =
          let uu____768 = FStar_Util.smap_try_find env.includes mname in
          match uu____768 with
          | None  -> []
          | Some minc -> FStar_ST.read minc in
        let look_into =
          if not_shadowed
          then let uu____788 = qual modul id in find_in_module uu____788
          else Cont_ignore in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____791 -> look_into) in
  aux [ns]
let is_exported_id_field: exported_id_kind -> Prims.bool =
  fun uu___142_795  ->
    match uu___142_795 with | Exported_id_field  -> true | uu____796 -> false
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___143_885 =
    match uu___143_885 with
    | (id',uu____887,uu____888) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let check_rec_binding_id uu___144_892 =
    match uu___144_892 with
    | (id',uu____894,uu____895) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText in
  let curmod_ns =
    let uu____898 = current_module env in FStar_Ident.ids_of_lid uu____898 in
  let proc uu___145_903 =
    match uu___145_903 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____908) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____911 = FStar_Ident.lid_of_ids curmod_ns in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____911 id
    | uu____914 -> Cont_ignore in
  let rec aux uu___146_920 =
    match uu___146_920 with
    | a::q ->
        let uu____926 = proc a in
        option_of_cont (fun uu____928  -> aux q) uu____926
    | [] ->
        let uu____929 = lookup_default_id Cont_fail id in
        option_of_cont (fun uu____931  -> None) uu____929 in
  aux env.scope_mods
let found_local_binding r uu____950 =
  match uu____950 with
  | (id',x,mut) -> let uu____957 = bv_to_name x r in (uu____957, mut)
let find_in_module env lid k_global_def k_not_found =
  let uu____994 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
  match uu____994 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found
let try_lookup_id:
  env ->
    FStar_Ident.ident -> (FStar_Syntax_Syntax.term* Prims.bool) Prims.option
  =
  fun env  ->
    fun id  ->
      let uu____1016 = unmangleOpName id in
      match uu____1016 with
      | Some f -> Some f
      | uu____1030 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1037 = found_local_binding id.FStar_Ident.idRange r in
               Cont_ok uu____1037) (fun uu____1042  -> Cont_fail)
            (fun uu____1045  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1052  -> fun uu____1053  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1060  -> fun uu____1061  -> Cont_fail)
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1113 ->
        let lid = qualify env id in
        let uu____1115 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str in
        (match uu____1115 with
         | Some r -> let uu____1128 = k_global_def lid r in Some uu____1128
         | None  -> None)
    | None  -> None in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1141 = current_module env in qual uu____1141 id in
      find_in_module env lid k_global_def k_not_found
let module_is_defined: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
           let uu____1150 = current_module env in
           FStar_Ident.lid_equals lid uu____1150)
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
        let rec aux uu___147_1174 =
          match uu___147_1174 with
          | [] ->
              let uu____1177 = module_is_defined env lid in
              if uu____1177 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1184 =
                  let uu____1186 = FStar_Ident.path_of_lid ns in
                  let uu____1188 = FStar_Ident.path_of_lid lid in
                  FStar_List.append uu____1186 uu____1188 in
                FStar_Ident.lid_of_path uu____1184
                  (FStar_Ident.range_of_lid lid) in
              let uu____1190 = module_is_defined env new_lid in
              if uu____1190 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1195 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1199::q -> aux q in
        aux env.scope_mods
let namespace_is_open: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___148_1208  ->
           match uu___148_1208 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1210 -> false) env.scope_mods
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
                 let uu____1265 = aux rev_ns_prefix ns_last_id in
                 FStar_All.pipe_right uu____1265
                   (FStar_Util.map_option
                      (fun uu____1289  ->
                         match uu____1289 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids))))) in
        let uu____1306 =
          is_full_path &&
            (let uu____1307 = FStar_Ident.lid_of_ids ids in
             module_is_defined env uu____1307) in
        if uu____1306
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1324 = aux ns_rev_prefix ns_last_id in
               (match uu____1324 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1437::uu____1438 ->
      let uu____1440 =
        let uu____1442 =
          let uu____1443 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_Ident.set_lid_range uu____1443 (FStar_Ident.range_of_lid lid) in
        resolve_module_name env uu____1442 true in
      (match uu____1440 with
       | None  -> None
       | Some modul ->
           let uu____1446 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident in
           option_of_cont (fun uu____1448  -> None) uu____1446)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
let cont_of_option k_none uu___149_1463 =
  match uu___149_1463 with | Some v1 -> Cont_ok v1 | None  -> k_none
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1542 = k_global_def lid1 def in cont_of_option k uu____1542 in
  let f_module lid' =
    let k = Cont_ignore in find_in_module env lid' (k_global_def' k) k in
  let l_default k i = lookup_default_id env i (k_global_def' k) k in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1563 = k_local_binding l in
       cont_of_option Cont_fail uu____1563)
    (fun r  ->
       let uu____1566 = k_rec_binding r in
       cont_of_option Cont_fail uu____1566) (fun uu____1568  -> Cont_ignore)
    f_module l_default
let fv_qual_of_se:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual Prims.option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1574,uu____1575,uu____1576,l,uu____1578,quals,uu____1580) ->
        let qopt =
          FStar_Util.find_map quals
            (fun uu___150_1587  ->
               match uu___150_1587 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1589,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1596 -> None) in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____1600,uu____1601,uu____1602,quals) -> None
    | uu____1606 -> None
let lb_fv:
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1615 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
             let uu____1619 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
             if uu____1619 then Some fv else None) in
      FStar_All.pipe_right uu____1615 FStar_Util.must
let ns_of_lid_equals: FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1633 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
         FStar_Ident.lid_equals uu____1633 ns)
let try_lookup_name:
  Prims.bool ->
    Prims.bool -> env -> FStar_Ident.lident -> foundname Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid in
          let k_global_def source_lid uu___154_1658 =
            match uu___154_1658 with
            | (uu____1662,true ) when exclude_interf -> None
            | (se,uu____1664) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1666 ->
                     let uu____1677 =
                       let uu____1678 =
                         let uu____1681 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None in
                         (uu____1681, false) in
                       Term_name uu____1678 in
                     Some uu____1677
                 | FStar_Syntax_Syntax.Sig_datacon uu____1682 ->
                     let uu____1692 =
                       let uu____1693 =
                         let uu____1696 =
                           let uu____1697 = fv_qual_of_se se in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1697 in
                         (uu____1696, false) in
                       Term_name uu____1693 in
                     Some uu____1692
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1699,lbs),uu____1701,uu____1702,uu____1703) ->
                     let fv = lb_fv lbs source_lid in
                     let uu____1716 =
                       let uu____1717 =
                         let uu____1720 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual in
                         (uu____1720, false) in
                       Term_name uu____1717 in
                     Some uu____1716
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1722,uu____1723,quals) ->
                     let uu____1727 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___151_1729  ->
                                  match uu___151_1729 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1730 -> false))) in
                     if uu____1727
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid) in
                       let dd =
                         let uu____1734 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___152_1736  ->
                                         match uu___152_1736 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1739 -> false)))) in
                         if uu____1734
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant in
                       let uu____1741 =
                         FStar_Util.find_map quals
                           (fun uu___153_1743  ->
                              match uu___153_1743 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1746 -> None) in
                       (match uu____1741 with
                        | Some refl_monad ->
                            let refl_const =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reflect refl_monad)))
                                None occurrence_range in
                            Some (Term_name (refl_const, false))
                        | uu____1762 ->
                            let uu____1764 =
                              let uu____1765 =
                                let uu____1768 =
                                  let uu____1769 = fv_qual_of_se se in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____1769 in
                                (uu____1768, false) in
                              Term_name uu____1765 in
                            Some uu____1764)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1773 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1782 -> None) in
          let k_local_binding r =
            let uu____1794 =
              let uu____1795 =
                found_local_binding (FStar_Ident.range_of_lid lid) r in
              Term_name uu____1795 in
            Some uu____1794 in
          let k_rec_binding uu____1805 =
            match uu____1805 with
            | (id,l,dd) ->
                let uu____1813 =
                  let uu____1814 =
                    let uu____1817 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None in
                    (uu____1817, false) in
                  Term_name uu____1814 in
                Some uu____1813 in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____1821 = unmangleOpName lid.FStar_Ident.ident in
                (match uu____1821 with
                 | Some f -> Some (Term_name f)
                 | uu____1831 -> None)
            | uu____1835 -> None in
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
        let uu____1855 = try_lookup_name true exclude_interf env lid in
        match uu____1855 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____1864 -> None
let try_lookup_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1875 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1875 with | Some (o,l1) -> Some l1 | uu____1884 -> None
let try_lookup_effect_name_and_attributes:
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident* FStar_Syntax_Syntax.cflags Prims.list)
        Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____1898 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1898 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____1907;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____1916;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____1924,uu____1925,uu____1926,uu____1927,uu____1928,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____1930;_},l1)
          -> Some (l1, cattributes)
      | uu____1942 -> None
let try_lookup_effect_defn:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      let uu____1956 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1956 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____1962;_},uu____1963)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____1967;_},uu____1968)
          -> Some ne
      | uu____1971 -> None
let is_effect_name: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____1981 = try_lookup_effect_name env lid in
      match uu____1981 with | None  -> false | Some uu____1983 -> true
let try_lookup_root_effect_name:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1991 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l in
      match uu____1991 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____1997,uu____1998,uu____1999,uu____2000,uu____2001);
             FStar_Syntax_Syntax.sigrng = uu____2002;_},uu____2003)
          ->
          let rec aux new_name =
            let uu____2015 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str in
            match uu____2015 with
            | None  -> None
            | Some (s,uu____2025) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____2030,uu____2031,uu____2032,cmp,uu____2034,uu____2035)
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
      let k_global_def lid1 uu___155_2067 =
        match uu___155_2067 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (lid2,uu____2073,uu____2074,quals);
             FStar_Syntax_Syntax.sigrng = uu____2076;_},uu____2077)
            -> Some quals
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
      let k_global_def lid1 uu___156_2146 =
        match uu___156_2146 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2150,lbs),uu____2152,uu____2153,uu____2154);
             FStar_Syntax_Syntax.sigrng = uu____2155;_},uu____2156)
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
      let k_global_def lid1 uu___157_2193 =
        match uu___157_2193 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2200,uu____2201,uu____2202);
             FStar_Syntax_Syntax.sigrng = uu____2203;_},uu____2204)
            ->
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
        let uu___168_2324 = env in
        {
          curmodule = (uu___168_2324.curmodule);
          curmonad = (uu___168_2324.curmonad);
          modules = (uu___168_2324.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___168_2324.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___168_2324.sigaccum);
          sigmap = (uu___168_2324.sigmap);
          iface = (uu___168_2324.iface);
          admitted_iface = (uu___168_2324.admitted_iface);
          expect_typ = (uu___168_2324.expect_typ);
          docs = (uu___168_2324.docs)
        } in
      try_lookup_lid env' l
let try_lookup_doc:
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str
let try_lookup_datacon:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___159_2348 =
        match uu___159_2348 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2352,uu____2353,uu____2354,quals);
             FStar_Syntax_Syntax.sigrng = uu____2356;_},uu____2357)
            ->
            let uu____2360 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___158_2362  ->
                      match uu___158_2362 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2363 -> false)) in
            if uu____2360
            then
              let uu____2365 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None in
              Some uu____2365
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2367;
             FStar_Syntax_Syntax.sigrng = uu____2368;_},uu____2369)
            ->
            let uu____2379 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            Some uu____2379
        | uu____2380 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2383  -> None)
        (fun uu____2384  -> None) k_global_def
let find_all_datacons:
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___160_2403 =
        match uu___160_2403 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2408,uu____2409,uu____2410,uu____2411,uu____2412,datas,uu____2414);
             FStar_Syntax_Syntax.sigrng = uu____2415;_},uu____2416)
            -> Some datas
        | uu____2424 -> None in
      resolve_in_open_namespaces' env lid (fun uu____2429  -> None)
        (fun uu____2431  -> None) k_global_def
let record_cache_aux_with_filter:
  (((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))* (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]] in
  let push1 uu____2465 =
    let uu____2466 =
      let uu____2469 =
        let uu____2471 = FStar_ST.read record_cache in
        FStar_List.hd uu____2471 in
      let uu____2479 = FStar_ST.read record_cache in uu____2469 :: uu____2479 in
    FStar_ST.write record_cache uu____2466 in
  let pop1 uu____2494 =
    let uu____2495 =
      let uu____2498 = FStar_ST.read record_cache in FStar_List.tl uu____2498 in
    FStar_ST.write record_cache uu____2495 in
  let peek uu____2514 =
    let uu____2515 = FStar_ST.read record_cache in FStar_List.hd uu____2515 in
  let insert r =
    let uu____2527 =
      let uu____2530 = let uu____2532 = peek () in r :: uu____2532 in
      let uu____2534 =
        let uu____2537 = FStar_ST.read record_cache in
        FStar_List.tl uu____2537 in
      uu____2530 :: uu____2534 in
    FStar_ST.write record_cache uu____2527 in
  let commit1 uu____2553 =
    let uu____2554 = FStar_ST.read record_cache in
    match uu____2554 with
    | hd1::uu____2562::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2575 -> failwith "Impossible" in
  let filter1 uu____2581 =
    let rc = peek () in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc in
         let uu____2588 =
           let uu____2591 = FStar_ST.read record_cache in filtered ::
             uu____2591 in
         FStar_ST.write record_cache uu____2588) in
  let aux = (push1, pop1, peek, insert, commit1) in (aux, filter1)
let record_cache_aux:
  ((Prims.unit -> Prims.unit)* (Prims.unit -> Prims.unit)*
    (Prims.unit -> record_or_dc Prims.list)* (record_or_dc -> Prims.unit)*
    (Prims.unit -> Prims.unit))
  =
  let uu____2665 = record_cache_aux_with_filter in
  match uu____2665 with | (aux,uu____2703) -> aux
let filter_record_cache: Prims.unit -> Prims.unit =
  let uu____2742 = record_cache_aux_with_filter in
  match uu____2742 with | (uu____2765,filter1) -> filter1
let push_record_cache: Prims.unit -> Prims.unit =
  let uu____2805 = record_cache_aux in
  match uu____2805 with
  | (push1,uu____2825,uu____2826,uu____2827,uu____2828) -> push1
let pop_record_cache: Prims.unit -> Prims.unit =
  let uu____2853 = record_cache_aux in
  match uu____2853 with
  | (uu____2872,pop1,uu____2874,uu____2875,uu____2876) -> pop1
let peek_record_cache: Prims.unit -> record_or_dc Prims.list =
  let uu____2902 = record_cache_aux in
  match uu____2902 with
  | (uu____2922,uu____2923,peek,uu____2925,uu____2926) -> peek
let insert_record_cache: record_or_dc -> Prims.unit =
  let uu____2951 = record_cache_aux in
  match uu____2951 with
  | (uu____2970,uu____2971,uu____2972,insert,uu____2974) -> insert
let commit_record_cache: Prims.unit -> Prims.unit =
  let uu____2999 = record_cache_aux in
  match uu____2999 with
  | (uu____3018,uu____3019,uu____3020,uu____3021,commit1) -> commit1
let extract_record:
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3061,uu____3062) ->
            let is_rec =
              FStar_Util.for_some
                (fun uu___161_3073  ->
                   match uu___161_3073 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____3076 -> false) in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___162_3084  ->
                      match uu___162_3084 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3086,uu____3087,uu____3088,uu____3089,uu____3090,uu____3091);
                          FStar_Syntax_Syntax.sigrng = uu____3092;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3097 -> false)) in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___163_3099  ->
                    match uu___163_3099 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____3103,uu____3104,dc::[],tags);
                        FStar_Syntax_Syntax.sigrng = uu____3107;_} ->
                        let uu____3113 =
                          let uu____3114 = find_dc dc in
                          FStar_All.pipe_left FStar_Util.must uu____3114 in
                        (match uu____3113 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3118,t,uu____3120,uu____3121,uu____3122,uu____3123);
                             FStar_Syntax_Syntax.sigrng = uu____3124;_} ->
                             let uu____3129 =
                               FStar_Syntax_Util.arrow_formals t in
                             (match uu____3129 with
                              | (formals,uu____3138) ->
                                  let is_rec1 = is_rec tags in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3164  ->
                                            match uu____3164 with
                                            | (x,q) ->
                                                let uu____3172 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec1 &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q)) in
                                                if uu____3172
                                                then []
                                                else [(x, q)])) in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3203  ->
                                            match uu____3203 with
                                            | (x,q) ->
                                                let uu____3212 =
                                                  if is_rec1
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname in
                                                (uu____3212,
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
                                  ((let uu____3224 =
                                      let uu____3226 =
                                        FStar_ST.read new_globs in
                                      (Record_or_dc record) :: uu____3226 in
                                    FStar_ST.write new_globs uu____3224);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3242 =
                                            match uu____3242 with
                                            | (id,uu____3248) ->
                                                let modul =
                                                  let uu____3254 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns in
                                                  uu____3254.FStar_Ident.str in
                                                let uu____3255 =
                                                  get_exported_id_set e modul in
                                                (match uu____3255 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field in
                                                     ((let uu____3271 =
                                                         let uu____3272 =
                                                           FStar_ST.read
                                                             my_exported_ids in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3272 in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3271);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3279 =
                                                               let uu____3280
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id in
                                                               uu____3280.FStar_Ident.ident in
                                                             uu____3279.FStar_Ident.idText in
                                                           let uu____3282 =
                                                             let uu____3283 =
                                                               FStar_ST.read
                                                                 my_exported_ids in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3283 in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3282))
                                                 | None  -> ()) in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3296 -> ())
                    | uu____3297 -> ()))
        | uu____3298 -> ()
let try_lookup_record_or_dc_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3311 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident)) in
        match uu____3311 with
        | (ns,id) ->
            let uu____3321 = peek_record_cache () in
            FStar_Util.find_map uu____3321
              (fun record  ->
                 let uu____3324 =
                   find_in_record ns id record (fun r  -> Cont_ok r) in
                 option_of_cont (fun uu____3327  -> None) uu____3324) in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3328  -> Cont_ignore) (fun uu____3329  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3332 = find_in_cache fn in
           cont_of_option Cont_ignore uu____3332)
        (fun k  -> fun uu____3335  -> k)
let try_lookup_record_by_field_name:
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let uu____3344 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3344 with
      | Some r when r.is_record -> Some r
      | uu____3348 -> None
let belongs_to_record:
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3359 = try_lookup_record_by_field_name env lid in
        match uu____3359 with
        | Some record' when
            let uu____3362 =
              let uu____3363 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3363 in
            let uu____3365 =
              let uu____3366 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns in
              FStar_Ident.text_of_path uu____3366 in
            uu____3362 = uu____3365 ->
            let uu____3368 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3370  -> Cont_ok ()) in
            (match uu____3368 with
             | Cont_ok uu____3371 -> true
             | uu____3372 -> false)
        | uu____3374 -> false
let try_lookup_dc_by_field_name:
  env -> FStar_Ident.lident -> (FStar_Ident.lident* Prims.bool) Prims.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____3385 = try_lookup_record_or_dc_by_field_name env fieldname in
      match uu____3385 with
      | Some r ->
          let uu____3391 =
            let uu____3394 =
              let uu____3395 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname]) in
              FStar_Ident.set_lid_range uu____3395
                (FStar_Ident.range_of_lid fieldname) in
            (uu____3394, (r.is_record)) in
          Some uu____3391
      | uu____3398 -> None
let string_set_ref_new:
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3407  ->
    let uu____3408 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode in
    FStar_Util.mk_ref uu____3408
let exported_id_set_new:
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3419  ->
    let term_type_set = string_set_ref_new () in
    let field_set = string_set_ref_new () in
    fun uu___164_3428  ->
      match uu___164_3428 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
let unique:
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___165_3448 =
            match uu___165_3448 with
            | Rec_binding uu____3449 -> true
            | uu____3450 -> false in
          let this_env =
            let uu___169_3452 = env in
            let uu____3453 =
              FStar_List.filter filter_scope_mods env.scope_mods in
            {
              curmodule = (uu___169_3452.curmodule);
              curmonad = (uu___169_3452.curmonad);
              modules = (uu___169_3452.modules);
              scope_mods = uu____3453;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___169_3452.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___169_3452.sigaccum);
              sigmap = (uu___169_3452.sigmap);
              iface = (uu___169_3452.iface);
              admitted_iface = (uu___169_3452.admitted_iface);
              expect_typ = (uu___169_3452.expect_typ);
              docs = (uu___169_3452.docs)
            } in
          let uu____3455 = try_lookup_lid' any_val exclude_if this_env lid in
          match uu____3455 with | None  -> true | Some uu____3461 -> false
let push_scope_mod: env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___170_3472 = env in
      {
        curmodule = (uu___170_3472.curmodule);
        curmonad = (uu___170_3472.curmonad);
        modules = (uu___170_3472.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___170_3472.exported_ids);
        trans_exported_ids = (uu___170_3472.trans_exported_ids);
        includes = (uu___170_3472.includes);
        sigaccum = (uu___170_3472.sigaccum);
        sigmap = (uu___170_3472.sigmap);
        iface = (uu___170_3472.iface);
        admitted_iface = (uu___170_3472.admitted_iface);
        expect_typ = (uu___170_3472.expect_typ);
        docs = (uu___170_3472.docs)
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
        let uu____3511 =
          (unique false true env l) || (FStar_Options.interactive ()) in
        if uu____3511
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
          | Some (se,uu____3531) ->
              let uu____3534 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se) in
              (match uu____3534 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>" in
        let uu____3539 =
          let uu____3540 =
            let uu____3543 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r in
            (uu____3543, (FStar_Ident.range_of_lid l)) in
          FStar_Errors.Error uu____3540 in
        Prims.raise uu____3539 in
      let globals = FStar_Util.mk_ref env.scope_mods in
      let env1 =
        let uu____3550 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3555 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3563 -> (true, true)
          | uu____3570 -> (false, false) in
        match uu____3550 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s in
            let uu____3575 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3578 =
                     let uu____3579 = unique any_val exclude_if env l in
                     Prims.op_Negation uu____3579 in
                   if uu____3578 then Some l else None) in
            (match uu____3575 with
             | Some l when
                 let uu____3583 = FStar_Options.interactive () in
                 Prims.op_Negation uu____3583 -> err l
             | uu____3584 ->
                 (extract_record env globals s;
                  (let uu___171_3589 = env in
                   {
                     curmodule = (uu___171_3589.curmodule);
                     curmonad = (uu___171_3589.curmonad);
                     modules = (uu___171_3589.modules);
                     scope_mods = (uu___171_3589.scope_mods);
                     exported_ids = (uu___171_3589.exported_ids);
                     trans_exported_ids = (uu___171_3589.trans_exported_ids);
                     includes = (uu___171_3589.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___171_3589.sigmap);
                     iface = (uu___171_3589.iface);
                     admitted_iface = (uu___171_3589.admitted_iface);
                     expect_typ = (uu___171_3589.expect_typ);
                     docs = (uu___171_3589.docs)
                   }))) in
      let env2 =
        let uu___172_3591 = env1 in
        let uu____3592 = FStar_ST.read globals in
        {
          curmodule = (uu___172_3591.curmodule);
          curmonad = (uu___172_3591.curmonad);
          modules = (uu___172_3591.modules);
          scope_mods = uu____3592;
          exported_ids = (uu___172_3591.exported_ids);
          trans_exported_ids = (uu___172_3591.trans_exported_ids);
          includes = (uu___172_3591.includes);
          sigaccum = (uu___172_3591.sigaccum);
          sigmap = (uu___172_3591.sigmap);
          iface = (uu___172_3591.iface);
          admitted_iface = (uu___172_3591.admitted_iface);
          expect_typ = (uu___172_3591.expect_typ);
          docs = (uu___172_3591.docs)
        } in
      let uu____3597 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3611,uu____3612) ->
            let uu____3619 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses in
            (env2, uu____3619)
        | uu____3633 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)]) in
      match uu____3597 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3663  ->
                   match uu____3663 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3674 =
                                  let uu____3676 = FStar_ST.read globals in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3676 in
                                FStar_ST.write globals uu____3674);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3685 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns in
                                      uu____3685.FStar_Ident.str in
                                    ((let uu____3687 =
                                        get_exported_id_set env3 modul in
                                      match uu____3687 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type in
                                          let uu____3702 =
                                            let uu____3703 =
                                              FStar_ST.read my_exported_ids in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3703 in
                                          FStar_ST.write my_exported_ids
                                            uu____3702
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
              let uu___173_3715 = env3 in
              let uu____3716 = FStar_ST.read globals in
              {
                curmodule = (uu___173_3715.curmodule);
                curmonad = (uu___173_3715.curmonad);
                modules = (uu___173_3715.modules);
                scope_mods = uu____3716;
                exported_ids = (uu___173_3715.exported_ids);
                trans_exported_ids = (uu___173_3715.trans_exported_ids);
                includes = (uu___173_3715.includes);
                sigaccum = (uu___173_3715.sigaccum);
                sigmap = (uu___173_3715.sigmap);
                iface = (uu___173_3715.iface);
                admitted_iface = (uu___173_3715.admitted_iface);
                expect_typ = (uu___173_3715.expect_typ);
                docs = (uu___173_3715.docs)
              } in
            env4))
let push_namespace: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3727 =
        let uu____3730 = resolve_module_name env ns false in
        match uu____3730 with
        | None  ->
            let modules = env.modules in
            let uu____3738 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3744  ->
                      match uu____3744 with
                      | (m,uu____3748) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) "."))) in
            if uu____3738
            then (ns, Open_namespace)
            else
              (let uu____3752 =
                 let uu____3753 =
                   let uu____3756 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns) in
                   (uu____3756, (FStar_Ident.range_of_lid ns)) in
                 FStar_Errors.Error uu____3753 in
               Prims.raise uu____3752)
        | Some ns' -> (ns', Open_module) in
      match uu____3727 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
let push_include: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3768 = resolve_module_name env ns false in
      match uu____3768 with
      | Some ns1 ->
          let env1 =
            push_scope_mod env (Open_module_or_namespace (ns1, Open_module)) in
          let curmod =
            let uu____3773 = current_module env1 in
            uu____3773.FStar_Ident.str in
          ((let uu____3775 = FStar_Util.smap_try_find env1.includes curmod in
            match uu____3775 with
            | None  -> ()
            | Some incl ->
                let uu____3788 =
                  let uu____3790 = FStar_ST.read incl in ns1 :: uu____3790 in
                FStar_ST.write incl uu____3788);
           (match () with
            | () ->
                let uu____3798 =
                  get_trans_exported_id_set env1 ns1.FStar_Ident.str in
                (match uu____3798 with
                 | Some ns_trans_exports ->
                     ((let uu____3811 =
                         let uu____3822 = get_exported_id_set env1 curmod in
                         let uu____3827 =
                           get_trans_exported_id_set env1 curmod in
                         (uu____3822, uu____3827) in
                       match uu____3811 with
                       | (Some cur_exports,Some cur_trans_exports) ->
                           let update_exports k =
                             let ns_ex =
                               let uu____3867 = ns_trans_exports k in
                               FStar_ST.read uu____3867 in
                             let ex = cur_exports k in
                             (let uu____3876 =
                                let uu____3877 = FStar_ST.read ex in
                                FStar_Util.set_difference uu____3877 ns_ex in
                              FStar_ST.write ex uu____3876);
                             (match () with
                              | () ->
                                  let trans_ex = cur_trans_exports k in
                                  let uu____3887 =
                                    let uu____3888 = FStar_ST.read trans_ex in
                                    FStar_Util.set_union uu____3888 ns_ex in
                                  FStar_ST.write trans_ex uu____3887) in
                           FStar_List.iter update_exports
                             all_exported_id_kinds
                       | uu____3894 -> ());
                      (match () with | () -> env1))
                 | None  ->
                     let uu____3908 =
                       let uu____3909 =
                         let uu____3912 =
                           FStar_Util.format1
                             "include: Module %s was not prepared"
                             ns1.FStar_Ident.str in
                         (uu____3912, (FStar_Ident.range_of_lid ns1)) in
                       FStar_Errors.Error uu____3909 in
                     Prims.raise uu____3908)))
      | uu____3913 ->
          let uu____3915 =
            let uu____3916 =
              let uu____3919 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str in
              (uu____3919, (FStar_Ident.range_of_lid ns)) in
            FStar_Errors.Error uu____3916 in
          Prims.raise uu____3915
let push_module_abbrev: env -> FStar_Ident.ident -> FStar_Ident.lident -> env
  =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____3929 = module_is_defined env l in
        if uu____3929
        then push_scope_mod env (Module_abbrev (x, l))
        else
          (let uu____3931 =
             let uu____3932 =
               let uu____3935 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l) in
               (uu____3935, (FStar_Ident.range_of_lid l)) in
             FStar_Errors.Error uu____3932 in
           Prims.raise uu____3931)
let push_doc:
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option -> env =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____3949 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str in
              match uu____3949 with
              | None  -> ()
              | Some old_doc ->
                  let uu____3952 =
                    let uu____3953 = FStar_Ident.string_of_lid l in
                    let uu____3954 = FStar_Parser_AST.string_of_fsdoc old_doc in
                    let uu____3955 = FStar_Parser_AST.string_of_fsdoc doc1 in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____3953 uu____3954 uu____3955 in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____3952);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
let check_admits: env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,quals) ->
                let uu____3967 = try_lookup_lid env l in
                (match uu____3967 with
                 | None  ->
                     ((let uu____3974 =
                         let uu____3975 = FStar_Options.interactive () in
                         Prims.op_Negation uu____3975 in
                       if uu____3974
                       then
                         let uu____3976 =
                           let uu____3977 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l) in
                           let uu____3978 =
                             FStar_Syntax_Print.lid_to_string l in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____3977 uu____3978 in
                         FStar_Util.print_string uu____3976
                       else ());
                      FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                        ((let uu___174_3982 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_declare_typ
                                 (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                                   quals)));
                            FStar_Syntax_Syntax.sigrng =
                              (uu___174_3982.FStar_Syntax_Syntax.sigrng)
                          }), false))
                 | Some uu____3984 -> ())
            | uu____3989 -> ()))
let finish: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4000) ->
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
                                (lid,uu____4010,uu____4011,uu____4012,uu____4013,uu____4014,uu____4015)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4022 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4025,uu____4026,quals) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4033,lbs),uu____4035,quals,uu____4037) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4052 =
                               let uu____4053 =
                                 let uu____4054 =
                                   let uu____4059 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname in
                                   uu____4059.FStar_Syntax_Syntax.fv_name in
                                 uu____4054.FStar_Syntax_Syntax.v in
                               uu____4053.FStar_Ident.str in
                             FStar_Util.smap_remove (sigmap env) uu____4052))
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
                               let uu____4069 =
                                 let uu____4074 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname in
                                 uu____4074.FStar_Syntax_Syntax.fv_name in
                               uu____4069.FStar_Syntax_Syntax.v in
                             let decl =
                               let uu___175_4079 = se in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp),
                                        (FStar_Syntax_Syntax.Assumption ::
                                        quals)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___175_4079.FStar_Syntax_Syntax.sigrng)
                               } in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4087 -> ()));
      (let curmod =
         let uu____4089 = current_module env in uu____4089.FStar_Ident.str in
       (let uu____4091 =
          let uu____4102 = get_exported_id_set env curmod in
          let uu____4107 = get_trans_exported_id_set env curmod in
          (uu____4102, uu____4107) in
        match uu____4091 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4147 = cur_ex eikind in FStar_ST.read uu____4147 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind in
              let uu____4155 =
                let uu____4156 = FStar_ST.read cur_trans_ex_set_ref in
                FStar_Util.set_union cur_ex_set uu____4156 in
              FStar_ST.write cur_trans_ex_set_ref uu____4155 in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4162 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___176_4174 = env in
                  {
                    curmodule = None;
                    curmonad = (uu___176_4174.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___176_4174.exported_ids);
                    trans_exported_ids = (uu___176_4174.trans_exported_ids);
                    includes = (uu___176_4174.includes);
                    sigaccum = [];
                    sigmap = (uu___176_4174.sigmap);
                    iface = (uu___176_4174.iface);
                    admitted_iface = (uu___176_4174.admitted_iface);
                    expect_typ = (uu___176_4174.expect_typ);
                    docs = (uu___176_4174.docs)
                  }))))
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push: env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4187 =
       let uu____4189 = FStar_ST.read stack in env :: uu____4189 in
     FStar_ST.write stack uu____4187);
    (let uu___177_4197 = env in
     let uu____4198 = FStar_Util.smap_copy (sigmap env) in
     let uu____4204 = FStar_Util.smap_copy env.docs in
     {
       curmodule = (uu___177_4197.curmodule);
       curmonad = (uu___177_4197.curmonad);
       modules = (uu___177_4197.modules);
       scope_mods = (uu___177_4197.scope_mods);
       exported_ids = (uu___177_4197.exported_ids);
       trans_exported_ids = (uu___177_4197.trans_exported_ids);
       includes = (uu___177_4197.includes);
       sigaccum = (uu___177_4197.sigaccum);
       sigmap = uu____4198;
       iface = (uu___177_4197.iface);
       admitted_iface = (uu___177_4197.admitted_iface);
       expect_typ = (uu___177_4197.expect_typ);
       docs = uu____4204
     })
let pop: Prims.unit -> env =
  fun uu____4208  ->
    let uu____4209 = FStar_ST.read stack in
    match uu____4209 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4222 -> failwith "Impossible: Too many pops"
let commit_mark: env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4228 = FStar_ST.read stack in
     match uu____4228 with
     | uu____4233::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4240 -> failwith "Impossible: Too many pops")
let mark: env -> env = fun x  -> push x
let reset_mark: Prims.unit -> env = fun uu____4247  -> pop ()
let export_interface: FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4259 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4261 -> false in
      let sm = sigmap env in
      let env1 = pop () in
      let keys = FStar_Util.smap_keys sm in
      let sm' = sigmap env1 in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4279 = FStar_Util.smap_try_find sm' k in
              match uu____4279 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,q) ->
                          let uu___178_4298 = se in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_declare_typ
                                 (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                                   q)));
                            FStar_Syntax_Syntax.sigrng =
                              (uu___178_4298.FStar_Syntax_Syntax.sigrng)
                          }
                      | uu____4300 -> se in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4303 -> ()));
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
            (let uu____4347 = exported_id_set_new () in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4347);
            (match () with
             | () ->
                 ((let uu____4352 = exported_id_set_new () in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4352);
                  (match () with
                   | () ->
                       ((let uu____4357 = FStar_Util.mk_ref [] in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4357);
                        (match () with
                         | () ->
                             let uu___179_4366 = env1 in
                             let uu____4367 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1 in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___179_4366.curmonad);
                               modules = (uu___179_4366.modules);
                               scope_mods = uu____4367;
                               exported_ids = (uu___179_4366.exported_ids);
                               trans_exported_ids =
                                 (uu___179_4366.trans_exported_ids);
                               includes = (uu___179_4366.includes);
                               sigaccum = (uu___179_4366.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___179_4366.expect_typ);
                               docs = (uu___179_4366.docs)
                             }))))) in
          let uu____4370 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4382  ->
                    match uu____4382 with
                    | (l,uu____4386) -> FStar_Ident.lid_equals l mname)) in
          match uu____4370 with
          | None  -> let uu____4391 = prep env in (uu____4391, false)
          | Some (uu____4392,m) ->
              ((let uu____4397 =
                  (let uu____4398 = FStar_Options.interactive () in
                   Prims.op_Negation uu____4398) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf) in
                if uu____4397
                then
                  let uu____4399 =
                    let uu____4400 =
                      let uu____4403 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str in
                      (uu____4403, (FStar_Ident.range_of_lid mname)) in
                    FStar_Errors.Error uu____4400 in
                  Prims.raise uu____4399
                else ());
               (let uu____4405 = let uu____4406 = push env in prep uu____4406 in
                (uu____4405, true)))
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
          let uu___180_4414 = env in
          {
            curmodule = (uu___180_4414.curmodule);
            curmonad = (Some mname);
            modules = (uu___180_4414.modules);
            scope_mods = (uu___180_4414.scope_mods);
            exported_ids = (uu___180_4414.exported_ids);
            trans_exported_ids = (uu___180_4414.trans_exported_ids);
            includes = (uu___180_4414.includes);
            sigaccum = (uu___180_4414.sigaccum);
            sigmap = (uu___180_4414.sigmap);
            iface = (uu___180_4414.iface);
            admitted_iface = (uu___180_4414.admitted_iface);
            expect_typ = (uu___180_4414.expect_typ);
            docs = (uu___180_4414.docs)
          }
let fail_or env lookup lid =
  let uu____4439 = lookup lid in
  match uu____4439 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4445  ->
             match uu____4445 with
             | (lid1,uu____4449) -> FStar_Ident.text_of_lid lid1) env.modules in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid) in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4456 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
             FStar_Ident.set_lid_range uu____4456
               (FStar_Ident.range_of_lid lid) in
           let uu____4457 = resolve_module_name env modul true in
           match uu____4457 with
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
  let uu____4484 = lookup id in
  match uu____4484 with
  | None  ->
      Prims.raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r