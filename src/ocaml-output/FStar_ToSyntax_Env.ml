open Prims
type local_binding =
  (FStar_Ident.ident * FStar_Syntax_Syntax.bv * Prims.bool)
type rec_binding =
  (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth)
type module_abbrev = (FStar_Ident.ident * FStar_Ident.lident)
type open_kind =
  | Open_module 
  | Open_namespace 
let uu___is_Open_module : open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____12 -> false
  
let uu___is_Open_namespace : open_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____16 -> false
  
type open_module_or_namespace = (FStar_Ident.lident * open_kind)
type record_or_dc =
  {
  typename: FStar_Ident.lident ;
  constrname: FStar_Ident.ident ;
  parms: FStar_Syntax_Syntax.binders ;
  fields: (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list ;
  is_private_or_abstract: Prims.bool ;
  is_record: Prims.bool }
type scope_mod =
  | Local_binding of local_binding 
  | Rec_binding of rec_binding 
  | Module_abbrev of module_abbrev 
  | Open_module_or_namespace of open_module_or_namespace 
  | Top_level_def of FStar_Ident.ident 
  | Record_or_dc of record_or_dc 
let uu___is_Local_binding : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Local_binding _0 -> true | uu____92 -> false
  
let __proj__Local_binding__item___0 : scope_mod -> local_binding =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let uu___is_Rec_binding : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____104 -> false
  
let __proj__Rec_binding__item___0 : scope_mod -> rec_binding =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let uu___is_Module_abbrev : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____116 -> false
  
let __proj__Module_abbrev__item___0 : scope_mod -> module_abbrev =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let uu___is_Open_module_or_namespace : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____128 -> false
  
let __proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let uu___is_Top_level_def : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____140 -> false
  
let __proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let uu___is_Record_or_dc : scope_mod -> Prims.bool =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____152 -> false
  
let __proj__Record_or_dc__item___0 : scope_mod -> record_or_dc =
  fun projectee  -> match projectee with | Record_or_dc _0 -> _0 
type string_set = Prims.string FStar_Util.set
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field 
let uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____164 -> false
  
let uu___is_Exported_id_field : exported_id_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____168 -> false
  
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref
type env =
  {
  curmodule: FStar_Ident.lident Prims.option ;
  curmonad: FStar_Ident.ident Prims.option ;
  modules: (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list ;
  scope_mods: scope_mod Prims.list ;
  exported_ids: exported_id_set FStar_Util.smap ;
  trans_exported_ids: exported_id_set FStar_Util.smap ;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap ;
  sigaccum: FStar_Syntax_Syntax.sigelts ;
  sigmap: (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap ;
  iface: Prims.bool ;
  admitted_iface: Prims.bool ;
  expect_typ: Prims.bool }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * Prims.bool) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let uu___is_Term_name : foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____314 -> false
  
let __proj__Term_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.typ * Prims.bool) =
  fun projectee  -> match projectee with | Term_name _0 -> _0 
let uu___is_Eff_name : foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____334 -> false
  
let __proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let all_exported_id_kinds : exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type] 
let transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____357 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____357 with
      | None  -> []
      | Some exported_id_set ->
          let uu____361 =
            let uu____362 = exported_id_set Exported_id_term_type  in
            FStar_ST.read uu____362  in
          FStar_All.pipe_right uu____361 FStar_Util.set_elements
  
let open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list =
  fun e  -> e.modules 
let current_module : env -> FStar_Ident.lident =
  fun env  ->
    match env.curmodule with
    | None  -> failwith "Unset current module"
    | Some m -> m
  
let qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  FStar_Syntax_Util.qual_id 
let qualify : env -> FStar_Ident.ident -> FStar_Ident.lident =
  fun env  ->
    fun id  ->
      match env.curmonad with
      | None  -> let uu____388 = current_module env  in qual uu____388 id
      | Some monad ->
          let uu____390 =
            let uu____391 = current_module env  in qual uu____391 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____390 id
  
let new_sigmap uu____399 = FStar_Util.smap_create (Prims.parse_int "100") 
let empty_env : Prims.unit -> env =
  fun uu____402  ->
    let uu____403 = new_sigmap ()  in
    let uu____405 = new_sigmap ()  in
    let uu____407 = new_sigmap ()  in
    let uu____413 = new_sigmap ()  in
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
  
let sigmap : env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap
  = fun env  -> env.sigmap 
let has_all_in_scope : env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____432  ->
         match uu____432 with
         | (m,uu____436) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___166_444 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___166_444.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___167_445 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___167_445.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___167_445.FStar_Syntax_Syntax.sort)
      }
  
let bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r) 
let unmangleMap :
  (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth *
    FStar_Syntax_Syntax.fv_qual Prims.option) Prims.list
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.Delta_constant,
     (Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.Delta_equational, None)] 
let unmangleOpName :
  FStar_Ident.ident -> (FStar_Syntax_Syntax.term * Prims.bool) Prims.option =
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
                       id.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____506 dd dq  in
                 Some uu____505
               else None)
       in
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
let option_of_cont k_ignore uu___139_590 =
  match uu___139_590 with
  | Cont_ok a -> Some a
  | Cont_fail  -> None
  | Cont_ignore  -> k_ignore () 
let find_in_record ns id record cont =
  let typename' =
    FStar_Ident.lid_of_ids
      (FStar_List.append ns [(record.typename).FStar_Ident.ident])
     in
  if FStar_Ident.lid_equals typename' record.typename
  then
    let fname =
      FStar_Ident.lid_of_ids
        (FStar_List.append (record.typename).FStar_Ident.ns [id])
       in
    let find1 =
      FStar_Util.find_map record.fields
        (fun uu____635  ->
           match uu____635 with
           | (f,uu____640) ->
               if id.FStar_Ident.idText = f.FStar_Ident.idText
               then Some record
               else None)
       in
    match find1 with | Some r -> cont r | None  -> Cont_ignore
  else Cont_ignore 
let get_exported_id_set : env -> Prims.string -> exported_id_set Prims.option
  = fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname 
let get_trans_exported_id_set :
  env -> Prims.string -> exported_id_set Prims.option =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname 
let string_of_exported_id_kind : exported_id_kind -> Prims.string =
  fun uu___140_676  ->
    match uu___140_676 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
  
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText  in
  let rec aux uu___141_725 =
    match uu___141_725 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str  in
        let not_shadowed =
          let uu____733 = get_exported_id_set env mname  in
          match uu____733 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____749 = mex eikind  in FStar_ST.read uu____749  in
              FStar_Util.set_mem idstr mexports
           in
        let mincludes =
          let uu____756 = FStar_Util.smap_try_find env.includes mname  in
          match uu____756 with
          | None  -> []
          | Some minc -> FStar_ST.read minc  in
        let look_into =
          if not_shadowed
          then let uu____776 = qual modul id  in find_in_module uu____776
          else Cont_ignore  in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____779 -> look_into)
     in
  aux [ns] 
let is_exported_id_field : exported_id_kind -> Prims.bool =
  fun uu___142_783  ->
    match uu___142_783 with | Exported_id_field  -> true | uu____784 -> false
  
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___143_873 =
    match uu___143_873 with
    | (id',uu____875,uu____876) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText
     in
  let check_rec_binding_id uu___144_880 =
    match uu___144_880 with
    | (id',uu____882,uu____883) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText
     in
  let curmod_ns =
    let uu____886 = current_module env  in FStar_Ident.ids_of_lid uu____886
     in
  let proc uu___145_891 =
    match uu___145_891 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____896) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____899 = FStar_Ident.lid_of_ids curmod_ns  in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident  in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____899 id
    | uu____902 -> Cont_ignore  in
  let rec aux uu___146_908 =
    match uu___146_908 with
    | a::q ->
        let uu____914 = proc a  in
        option_of_cont (fun uu____916  -> aux q) uu____914
    | [] ->
        let uu____917 = lookup_default_id Cont_fail id  in
        option_of_cont (fun uu____919  -> None) uu____917
     in
  aux env.scope_mods 
let found_local_binding r uu____938 =
  match uu____938 with
  | (id',x,mut) -> let uu____945 = bv_to_name x r  in (uu____945, mut) 
let find_in_module env lid k_global_def k_not_found =
  let uu____982 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
     in
  match uu____982 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found 
let try_lookup_id :
  env ->
    FStar_Ident.ident -> (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  =
  fun env  ->
    fun id  ->
      let uu____1004 = unmangleOpName id  in
      match uu____1004 with
      | Some f -> Some f
      | uu____1018 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1025 = found_local_binding id.FStar_Ident.idRange r
                  in
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
        let lid = qualify env id  in
        let uu____1103 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
        (match uu____1103 with
         | Some r -> let uu____1116 = k_global_def lid r  in Some uu____1116
         | None  -> None)
    | None  -> None  in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1129 = current_module env  in qual uu____1129 id
         in
      find_in_module env lid k_global_def k_not_found
  
let module_is_defined : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
           let uu____1138 = current_module env  in
           FStar_Ident.lid_equals lid uu____1138)
        ||
        (FStar_List.existsb
           (fun x  -> FStar_Ident.lid_equals lid (Prims.fst x)) env.modules)
  
let resolve_module_name :
  env -> FStar_Ident.lident -> Prims.bool -> FStar_Ident.lident Prims.option
  =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns  in
        let rec aux uu___147_1162 =
          match uu___147_1162 with
          | [] ->
              let uu____1165 = module_is_defined env lid  in
              if uu____1165 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1172 =
                  let uu____1174 = FStar_Ident.path_of_lid ns  in
                  let uu____1176 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____1174 uu____1176  in
                FStar_Ident.lid_of_path uu____1172
                  (FStar_Ident.range_of_lid lid)
                 in
              let uu____1178 = module_is_defined env new_lid  in
              if uu____1178 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1183 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1187::q -> aux q  in
        aux env.scope_mods
  
let namespace_is_open : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___148_1196  ->
           match uu___148_1196 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1198 -> false) env.scope_mods
  
let shorten_module_path :
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun ids  ->
      fun is_full_path  ->
        let rec aux revns id =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id
             in
          if namespace_is_open env lid
          then Some ((FStar_List.rev (id :: revns)), [])
          else
            (match revns with
             | [] -> None
             | ns_last_id::rev_ns_prefix ->
                 let uu____1253 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____1253
                   (FStar_Util.map_option
                      (fun uu____1277  ->
                         match uu____1277 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids)))))
           in
        let uu____1294 =
          is_full_path &&
            (let uu____1295 = FStar_Ident.lid_of_ids ids  in
             module_is_defined env uu____1295)
           in
        if uu____1294
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1312 = aux ns_rev_prefix ns_last_id  in
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
          let uu____1431 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_Ident.set_lid_range uu____1431 (FStar_Ident.range_of_lid lid)
           in
        resolve_module_name env uu____1430 true  in
      (match uu____1428 with
       | None  -> None
       | Some modul ->
           let uu____1434 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident
              in
           option_of_cont (fun uu____1436  -> None) uu____1434)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
  
let cont_of_option k_none uu___149_1451 =
  match uu___149_1451 with | Some v1 -> Cont_ok v1 | None  -> k_none 
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1530 = k_global_def lid1 def  in cont_of_option k uu____1530
     in
  let f_module lid' =
    let k = Cont_ignore  in find_in_module env lid' (k_global_def' k) k  in
  let l_default k i = lookup_default_id env i (k_global_def' k) k  in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1551 = k_local_binding l  in
       cont_of_option Cont_fail uu____1551)
    (fun r  ->
       let uu____1554 = k_rec_binding r  in
       cont_of_option Cont_fail uu____1554) (fun uu____1556  -> Cont_ignore)
    f_module l_default
  
let fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual Prims.option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1562,uu____1563,uu____1564,l,uu____1566,quals,uu____1568) ->
        let qopt =
          FStar_Util.find_map quals
            (fun uu___150_1575  ->
               match uu___150_1575 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1577,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1584 -> None)
           in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____1588,uu____1589,uu____1590,quals) -> None
    | uu____1594 -> None
  
let lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1603 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____1607 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____1607 then Some fv else None)
         in
      FStar_All.pipe_right uu____1603 FStar_Util.must
  
let ns_of_lid_equals : FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1621 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____1621 ns)
  
let try_lookup_name :
  Prims.bool ->
    Prims.bool -> env -> FStar_Ident.lident -> foundname Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid  in
          let k_global_def source_lid uu___154_1646 =
            match uu___154_1646 with
            | (uu____1650,true ) when exclude_interf -> None
            | (se,uu____1652) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1654 ->
                     let uu____1665 =
                       let uu____1666 =
                         let uu____1669 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None
                            in
                         (uu____1669, false)  in
                       Term_name uu____1666  in
                     Some uu____1665
                 | FStar_Syntax_Syntax.Sig_datacon uu____1670 ->
                     let uu____1680 =
                       let uu____1681 =
                         let uu____1684 =
                           let uu____1685 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1685
                            in
                         (uu____1684, false)  in
                       Term_name uu____1681  in
                     Some uu____1680
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1687,lbs),uu____1689,uu____1690,uu____1691) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____1704 =
                       let uu____1705 =
                         let uu____1708 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____1708, false)  in
                       Term_name uu____1705  in
                     Some uu____1704
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1710,uu____1711,quals) ->
                     let uu____1715 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___151_1717  ->
                                  match uu___151_1717 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1718 -> false)))
                        in
                     if uu____1715
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid)
                          in
                       let dd =
                         let uu____1722 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___152_1724  ->
                                         match uu___152_1724 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1727 -> false))))
                            in
                         if uu____1722
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let uu____1729 =
                         FStar_Util.find_map quals
                           (fun uu___153_1731  ->
                              match uu___153_1731 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1734 -> None)
                          in
                       (match uu____1729 with
                        | Some refl_monad ->
                            let refl_const =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reflect refl_monad)))
                                None occurrence_range
                               in
                            Some (Term_name (refl_const, false))
                        | uu____1750 ->
                            let uu____1752 =
                              let uu____1753 =
                                let uu____1756 =
                                  let uu____1757 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____1757
                                   in
                                (uu____1756, false)  in
                              Term_name uu____1753  in
                            Some uu____1752)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1761 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1770 -> None)
             in
          let k_local_binding r =
            let uu____1782 =
              let uu____1783 =
                found_local_binding (FStar_Ident.range_of_lid lid) r  in
              Term_name uu____1783  in
            Some uu____1782  in
          let k_rec_binding uu____1793 =
            match uu____1793 with
            | (id,l,dd) ->
                let uu____1801 =
                  let uu____1802 =
                    let uu____1805 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None
                       in
                    (uu____1805, false)  in
                  Term_name uu____1802  in
                Some uu____1801
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____1809 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____1809 with
                 | Some f -> Some (Term_name f)
                 | uu____1819 -> None)
            | uu____1823 -> None  in
          match found_unmangled with
          | None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
  
let try_lookup_effect_name' :
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) Prims.option
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____1843 = try_lookup_name true exclude_interf env lid  in
        match uu____1843 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____1852 -> None
  
let try_lookup_effect_name :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1863 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1863 with | Some (o,l1) -> Some l1 | uu____1872 -> None
  
let try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)
        Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____1886 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1886 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigdoc = uu____1895;
             FStar_Syntax_Syntax.sigrng = uu____1896;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigdoc = uu____1906;
             FStar_Syntax_Syntax.sigrng = uu____1907;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____1916,uu____1917,uu____1918,uu____1919,uu____1920,cattributes);
             FStar_Syntax_Syntax.sigdoc = uu____1922;
             FStar_Syntax_Syntax.sigrng = uu____1923;_},l1)
          -> Some (l1, cattributes)
      | uu____1936 -> None
  
let try_lookup_effect_defn :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      let uu____1950 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1950 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigdoc = uu____1956;
             FStar_Syntax_Syntax.sigrng = uu____1957;_},uu____1958)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigdoc = uu____1963;
             FStar_Syntax_Syntax.sigrng = uu____1964;_},uu____1965)
          -> Some ne
      | uu____1969 -> None
  
let is_effect_name : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____1979 = try_lookup_effect_name env lid  in
      match uu____1979 with | None  -> false | Some uu____1981 -> true
  
let try_lookup_root_effect_name :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1989 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1989 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____1995,uu____1996,uu____1997,uu____1998,uu____1999);
             FStar_Syntax_Syntax.sigdoc = uu____2000;
             FStar_Syntax_Syntax.sigrng = uu____2001;_},uu____2002)
          ->
          let rec aux new_name =
            let uu____2015 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
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
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____2041 -> None)
             in
          aux l'
      | Some (uu____2042,l') -> Some l'
      | uu____2046 -> None
  
let lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___155_2067 =
        match uu___155_2067 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (lid2,uu____2073,uu____2074,quals);
             FStar_Syntax_Syntax.sigdoc = uu____2076;
             FStar_Syntax_Syntax.sigrng = uu____2077;_},uu____2078)
            -> Some quals
        | uu____2083 -> None  in
      let uu____2087 =
        resolve_in_open_namespaces' env lid (fun uu____2091  -> None)
          (fun uu____2093  -> None) k_global_def
         in
      match uu____2087 with | Some quals -> quals | uu____2099 -> []
  
let try_lookup_module :
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul Prims.option =
  fun env  ->
    fun path  ->
      let uu____2111 =
        FStar_List.tryFind
          (fun uu____2117  ->
             match uu____2117 with
             | (mlid,modul) ->
                 let uu____2122 = FStar_Ident.path_of_lid mlid  in
                 uu____2122 = path) env.modules
         in
      match uu____2111 with
      | Some (uu____2126,modul) -> Some modul
      | None  -> None
  
let try_lookup_let :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___156_2148 =
        match uu___156_2148 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2152,lbs),uu____2154,uu____2155,uu____2156);
             FStar_Syntax_Syntax.sigdoc = uu____2157;
             FStar_Syntax_Syntax.sigrng = uu____2158;_},uu____2159)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____2173 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            Some uu____2173
        | uu____2174 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2177  -> None)
        (fun uu____2178  -> None) k_global_def
  
let try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___157_2197 =
        match uu___157_2197 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2204,uu____2205,uu____2206);
             FStar_Syntax_Syntax.sigdoc = uu____2207;
             FStar_Syntax_Syntax.sigrng = uu____2208;_},uu____2209)
            ->
            FStar_Util.find_map (Prims.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2227 -> None)
        | uu____2232 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2239  -> None)
        (fun uu____2242  -> None) k_global_def
  
let empty_include_smap :
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = new_sigmap () 
let empty_exported_id_smap : exported_id_set FStar_Util.smap = new_sigmap () 
let try_lookup_lid' :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let uu____2269 = try_lookup_name any_val exclude_interf env lid  in
          match uu____2269 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2278 -> None
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l 
let resolve_to_fully_qualified_name :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2298 = try_lookup_lid env l  in
      match uu____2298 with
      | None  -> None
      | Some (e,uu____2306) ->
          let uu____2309 =
            let uu____2310 = FStar_Syntax_Subst.compress e  in
            uu____2310.FStar_Syntax_Syntax.n  in
          (match uu____2309 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2319 -> None)
  
let try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___168_2330 = env  in
        {
          curmodule = (uu___168_2330.curmodule);
          curmonad = (uu___168_2330.curmonad);
          modules = (uu___168_2330.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___168_2330.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___168_2330.sigaccum);
          sigmap = (uu___168_2330.sigmap);
          iface = (uu___168_2330.iface);
          admitted_iface = (uu___168_2330.admitted_iface);
          expect_typ = (uu___168_2330.expect_typ)
        }  in
      try_lookup_lid env' l
  
let try_lookup_datacon :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___159_2347 =
        match uu___159_2347 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2351,uu____2352,uu____2353,quals);
             FStar_Syntax_Syntax.sigdoc = uu____2355;
             FStar_Syntax_Syntax.sigrng = uu____2356;_},uu____2357)
            ->
            let uu____2361 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___158_2363  ->
                      match uu___158_2363 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2364 -> false))
               in
            if uu____2361
            then
              let uu____2366 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None
                 in
              Some uu____2366
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2368;
             FStar_Syntax_Syntax.sigdoc = uu____2369;
             FStar_Syntax_Syntax.sigrng = uu____2370;_},uu____2371)
            ->
            let uu____2382 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor)
               in
            Some uu____2382
        | uu____2383 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2386  -> None)
        (fun uu____2387  -> None) k_global_def
  
let find_all_datacons :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___160_2406 =
        match uu___160_2406 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2411,uu____2412,uu____2413,uu____2414,uu____2415,datas,uu____2417);
             FStar_Syntax_Syntax.sigdoc = uu____2418;
             FStar_Syntax_Syntax.sigrng = uu____2419;_},uu____2420)
            -> Some datas
        | uu____2429 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2434  -> None)
        (fun uu____2436  -> None) k_global_def
  
let record_cache_aux_with_filter :
  (((Prims.unit -> Prims.unit) * (Prims.unit -> Prims.unit) *
    (Prims.unit -> record_or_dc Prims.list) * (record_or_dc -> Prims.unit) *
    (Prims.unit -> Prims.unit)) * (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____2470 =
    let uu____2471 =
      let uu____2474 =
        let uu____2476 = FStar_ST.read record_cache  in
        FStar_List.hd uu____2476  in
      let uu____2484 = FStar_ST.read record_cache  in uu____2474 ::
        uu____2484
       in
    FStar_ST.write record_cache uu____2471  in
  let pop1 uu____2499 =
    let uu____2500 =
      let uu____2503 = FStar_ST.read record_cache  in
      FStar_List.tl uu____2503  in
    FStar_ST.write record_cache uu____2500  in
  let peek uu____2519 =
    let uu____2520 = FStar_ST.read record_cache  in FStar_List.hd uu____2520
     in
  let insert r =
    let uu____2532 =
      let uu____2535 = let uu____2537 = peek ()  in r :: uu____2537  in
      let uu____2539 =
        let uu____2542 = FStar_ST.read record_cache  in
        FStar_List.tl uu____2542  in
      uu____2535 :: uu____2539  in
    FStar_ST.write record_cache uu____2532  in
  let commit1 uu____2558 =
    let uu____2559 = FStar_ST.read record_cache  in
    match uu____2559 with
    | hd1::uu____2567::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2580 -> failwith "Impossible"  in
  let filter1 uu____2586 =
    let rc = peek ()  in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
            in
         let uu____2593 =
           let uu____2596 = FStar_ST.read record_cache  in filtered ::
             uu____2596
            in
         FStar_ST.write record_cache uu____2593)
     in
  let aux = (push1, pop1, peek, insert, commit1)  in (aux, filter1) 
let record_cache_aux :
  ((Prims.unit -> Prims.unit) * (Prims.unit -> Prims.unit) *
    (Prims.unit -> record_or_dc Prims.list) * (record_or_dc -> Prims.unit) *
    (Prims.unit -> Prims.unit))
  =
  let uu____2670 = record_cache_aux_with_filter  in
  match uu____2670 with | (aux,uu____2708) -> aux 
let filter_record_cache : Prims.unit -> Prims.unit =
  let uu____2747 = record_cache_aux_with_filter  in
  match uu____2747 with | (uu____2770,filter1) -> filter1 
let push_record_cache : Prims.unit -> Prims.unit =
  let uu____2810 = record_cache_aux  in
  match uu____2810 with
  | (push1,uu____2830,uu____2831,uu____2832,uu____2833) -> push1 
let pop_record_cache : Prims.unit -> Prims.unit =
  let uu____2858 = record_cache_aux  in
  match uu____2858 with
  | (uu____2877,pop1,uu____2879,uu____2880,uu____2881) -> pop1 
let peek_record_cache : Prims.unit -> record_or_dc Prims.list =
  let uu____2907 = record_cache_aux  in
  match uu____2907 with
  | (uu____2927,uu____2928,peek,uu____2930,uu____2931) -> peek 
let insert_record_cache : record_or_dc -> Prims.unit =
  let uu____2956 = record_cache_aux  in
  match uu____2956 with
  | (uu____2975,uu____2976,uu____2977,insert,uu____2979) -> insert 
let commit_record_cache : Prims.unit -> Prims.unit =
  let uu____3004 = record_cache_aux  in
  match uu____3004 with
  | (uu____3023,uu____3024,uu____3025,uu____3026,commit1) -> commit1 
let extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3066,uu____3067) ->
            let is_rec =
              FStar_Util.for_some
                (fun uu___161_3078  ->
                   match uu___161_3078 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____3081 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___162_3089  ->
                      match uu___162_3089 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3091,uu____3092,uu____3093,uu____3094,uu____3095,uu____3096);
                          FStar_Syntax_Syntax.sigdoc = uu____3097;
                          FStar_Syntax_Syntax.sigrng = uu____3098;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3104 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___163_3106  ->
                    match uu___163_3106 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____3110,uu____3111,dc::[],tags);
                        FStar_Syntax_Syntax.sigdoc = uu____3114;
                        FStar_Syntax_Syntax.sigrng = uu____3115;_} ->
                        let uu____3122 =
                          let uu____3123 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____3123  in
                        (match uu____3122 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3127,t,uu____3129,uu____3130,uu____3131,uu____3132);
                             FStar_Syntax_Syntax.sigdoc = uu____3133;
                             FStar_Syntax_Syntax.sigrng = uu____3134;_} ->
                             let uu____3140 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____3140 with
                              | (formals,uu____3149) ->
                                  let is_rec1 = is_rec tags  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3175  ->
                                            match uu____3175 with
                                            | (x,q) ->
                                                let uu____3183 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec1 &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____3183
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3214  ->
                                            match uu____3214 with
                                            | (x,q) ->
                                                let uu____3223 =
                                                  if is_rec1
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____3223,
                                                  (x.FStar_Syntax_Syntax.sort))))
                                     in
                                  let fields = fields'  in
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
                                    }  in
                                  ((let uu____3235 =
                                      let uu____3237 =
                                        FStar_ST.read new_globs  in
                                      (Record_or_dc record) :: uu____3237  in
                                    FStar_ST.write new_globs uu____3235);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3253 =
                                            match uu____3253 with
                                            | (id,uu____3259) ->
                                                let modul =
                                                  let uu____3265 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____3265.FStar_Ident.str
                                                   in
                                                let uu____3266 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____3266 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____3282 =
                                                         let uu____3283 =
                                                           FStar_ST.read
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3283
                                                          in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3282);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3290 =
                                                               let uu____3291
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id
                                                                  in
                                                               uu____3291.FStar_Ident.ident
                                                                in
                                                             uu____3290.FStar_Ident.idText
                                                              in
                                                           let uu____3293 =
                                                             let uu____3294 =
                                                               FStar_ST.read
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3294
                                                              in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3293))
                                                 | None  -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3307 -> ())
                    | uu____3308 -> ()))
        | uu____3309 -> ()
  
let try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3322 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____3322 with
        | (ns,id) ->
            let uu____3332 = peek_record_cache ()  in
            FStar_Util.find_map uu____3332
              (fun record  ->
                 let uu____3335 =
                   find_in_record ns id record (fun r  -> Cont_ok r)  in
                 option_of_cont (fun uu____3338  -> None) uu____3335)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3339  -> Cont_ignore) (fun uu____3340  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3343 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____3343)
        (fun k  -> fun uu____3346  -> k)
  
let try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let uu____3355 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____3355 with
      | Some r when r.is_record -> Some r
      | uu____3359 -> None
  
let belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3370 = try_lookup_record_by_field_name env lid  in
        match uu____3370 with
        | Some record' when
            let uu____3373 =
              let uu____3374 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____3374  in
            let uu____3376 =
              let uu____3377 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____3377  in
            uu____3373 = uu____3376 ->
            let uu____3379 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3381  -> Cont_ok ())
               in
            (match uu____3379 with
             | Cont_ok uu____3382 -> true
             | uu____3383 -> false)
        | uu____3385 -> false
  
let try_lookup_dc_by_field_name :
  env -> FStar_Ident.lident -> (FStar_Ident.lident * Prims.bool) Prims.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____3396 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____3396 with
      | Some r ->
          let uu____3402 =
            let uu____3405 =
              let uu____3406 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              FStar_Ident.set_lid_range uu____3406
                (FStar_Ident.range_of_lid fieldname)
               in
            (uu____3405, (r.is_record))  in
          Some uu____3402
      | uu____3409 -> None
  
let string_set_ref_new :
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3418  ->
    let uu____3419 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode  in
    FStar_Util.mk_ref uu____3419
  
let exported_id_set_new :
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3430  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___164_3439  ->
      match uu___164_3439 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___165_3459 =
            match uu___165_3459 with
            | Rec_binding uu____3460 -> true
            | uu____3461 -> false  in
          let this_env =
            let uu___169_3463 = env  in
            let uu____3464 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___169_3463.curmodule);
              curmonad = (uu___169_3463.curmonad);
              modules = (uu___169_3463.modules);
              scope_mods = uu____3464;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___169_3463.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___169_3463.sigaccum);
              sigmap = (uu___169_3463.sigmap);
              iface = (uu___169_3463.iface);
              admitted_iface = (uu___169_3463.admitted_iface);
              expect_typ = (uu___169_3463.expect_typ)
            }  in
          let uu____3466 = try_lookup_lid' any_val exclude_if this_env lid
             in
          match uu____3466 with | None  -> true | Some uu____3472 -> false
  
let push_scope_mod : env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___170_3483 = env  in
      {
        curmodule = (uu___170_3483.curmodule);
        curmonad = (uu___170_3483.curmonad);
        modules = (uu___170_3483.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___170_3483.exported_ids);
        trans_exported_ids = (uu___170_3483.trans_exported_ids);
        includes = (uu___170_3483.includes);
        sigaccum = (uu___170_3483.sigaccum);
        sigmap = (uu___170_3483.sigmap);
        iface = (uu___170_3483.iface);
        admitted_iface = (uu___170_3483.admitted_iface);
        expect_typ = (uu___170_3483.expect_typ)
      }
  
let push_bv' :
  env -> FStar_Ident.ident -> Prims.bool -> (env * FStar_Syntax_Syntax.bv) =
  fun env  ->
    fun x  ->
      fun is_mutable  ->
        let bv =
          FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
            (Some (x.FStar_Ident.idRange)) FStar_Syntax_Syntax.tun
           in
        ((push_scope_mod env (Local_binding (x, bv, is_mutable))), bv)
  
let push_bv_mutable :
  env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv) =
  fun env  -> fun x  -> push_bv' env x true 
let push_bv : env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv) =
  fun env  -> fun x  -> push_bv' env x false 
let push_top_level_rec_binding :
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x  in
        let uu____3522 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____3522
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          Prims.raise
            (FStar_Errors.Error
               ((Prims.strcat "Duplicate top-level names " l.FStar_Ident.str),
                 (FStar_Ident.range_of_lid l)))
  
let push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let err l =
        let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
           in
        let r =
          match sopt with
          | Some (se,uu____3542) ->
              let uu____3545 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____3545 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>"  in
        let uu____3550 =
          let uu____3551 =
            let uu____3554 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r
               in
            (uu____3554, (FStar_Ident.range_of_lid l))  in
          FStar_Errors.Error uu____3551  in
        Prims.raise uu____3550  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____3561 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3566 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3574 -> (true, true)
          | uu____3581 -> (false, false)  in
        match uu____3561 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____3586 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3589 =
                     let uu____3590 = unique any_val exclude_if env l  in
                     Prims.op_Negation uu____3590  in
                   if uu____3589 then Some l else None)
               in
            (match uu____3586 with
             | Some l when
                 let uu____3594 = FStar_Options.interactive ()  in
                 Prims.op_Negation uu____3594 -> err l
             | uu____3595 ->
                 (extract_record env globals s;
                  (let uu___171_3600 = env  in
                   {
                     curmodule = (uu___171_3600.curmodule);
                     curmonad = (uu___171_3600.curmonad);
                     modules = (uu___171_3600.modules);
                     scope_mods = (uu___171_3600.scope_mods);
                     exported_ids = (uu___171_3600.exported_ids);
                     trans_exported_ids = (uu___171_3600.trans_exported_ids);
                     includes = (uu___171_3600.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___171_3600.sigmap);
                     iface = (uu___171_3600.iface);
                     admitted_iface = (uu___171_3600.admitted_iface);
                     expect_typ = (uu___171_3600.expect_typ)
                   })))
         in
      let env2 =
        let uu___172_3602 = env1  in
        let uu____3603 = FStar_ST.read globals  in
        {
          curmodule = (uu___172_3602.curmodule);
          curmonad = (uu___172_3602.curmonad);
          modules = (uu___172_3602.modules);
          scope_mods = uu____3603;
          exported_ids = (uu___172_3602.exported_ids);
          trans_exported_ids = (uu___172_3602.trans_exported_ids);
          includes = (uu___172_3602.includes);
          sigaccum = (uu___172_3602.sigaccum);
          sigmap = (uu___172_3602.sigmap);
          iface = (uu___172_3602.iface);
          admitted_iface = (uu___172_3602.admitted_iface);
          expect_typ = (uu___172_3602.expect_typ)
        }  in
      let uu____3608 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3622,uu____3623) ->
            let uu____3630 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____3630)
        | uu____3644 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____3608 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3674  ->
                   match uu____3674 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3685 =
                                  let uu____3687 = FStar_ST.read globals  in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3687
                                   in
                                FStar_ST.write globals uu____3685);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3696 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____3696.FStar_Ident.str  in
                                    ((let uu____3698 =
                                        get_exported_id_set env3 modul  in
                                      match uu____3698 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____3713 =
                                            let uu____3714 =
                                              FStar_ST.read my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3714
                                             in
                                          FStar_ST.write my_exported_ids
                                            uu____3713
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
              let uu___173_3726 = env3  in
              let uu____3727 = FStar_ST.read globals  in
              {
                curmodule = (uu___173_3726.curmodule);
                curmonad = (uu___173_3726.curmonad);
                modules = (uu___173_3726.modules);
                scope_mods = uu____3727;
                exported_ids = (uu___173_3726.exported_ids);
                trans_exported_ids = (uu___173_3726.trans_exported_ids);
                includes = (uu___173_3726.includes);
                sigaccum = (uu___173_3726.sigaccum);
                sigmap = (uu___173_3726.sigmap);
                iface = (uu___173_3726.iface);
                admitted_iface = (uu___173_3726.admitted_iface);
                expect_typ = (uu___173_3726.expect_typ)
              }  in
            env4))
  
let push_namespace : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3738 =
        let uu____3741 = resolve_module_name env ns false  in
        match uu____3741 with
        | None  ->
            let modules = env.modules  in
            let uu____3749 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3755  ->
                      match uu____3755 with
                      | (m,uu____3759) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) ".")))
               in
            if uu____3749
            then (ns, Open_namespace)
            else
              (let uu____3763 =
                 let uu____3764 =
                   let uu____3767 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns)
                      in
                   (uu____3767, (FStar_Ident.range_of_lid ns))  in
                 FStar_Errors.Error uu____3764  in
               Prims.raise uu____3763)
        | Some ns' -> (ns', Open_module)  in
      match uu____3738 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
  
let push_include : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3779 = resolve_module_name env ns false  in
      match uu____3779 with
      | Some ns1 ->
          let env1 =
            push_scope_mod env (Open_module_or_namespace (ns1, Open_module))
             in
          let curmod =
            let uu____3784 = current_module env1  in
            uu____3784.FStar_Ident.str  in
          ((let uu____3786 = FStar_Util.smap_try_find env1.includes curmod
               in
            match uu____3786 with
            | None  -> ()
            | Some incl ->
                let uu____3799 =
                  let uu____3801 = FStar_ST.read incl  in ns1 :: uu____3801
                   in
                FStar_ST.write incl uu____3799);
           (match () with
            | () ->
                let uu____3809 =
                  get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                (match uu____3809 with
                 | Some ns_trans_exports ->
                     ((let uu____3822 =
                         let uu____3833 = get_exported_id_set env1 curmod  in
                         let uu____3838 =
                           get_trans_exported_id_set env1 curmod  in
                         (uu____3833, uu____3838)  in
                       match uu____3822 with
                       | (Some cur_exports,Some cur_trans_exports) ->
                           let update_exports k =
                             let ns_ex =
                               let uu____3878 = ns_trans_exports k  in
                               FStar_ST.read uu____3878  in
                             let ex = cur_exports k  in
                             (let uu____3887 =
                                let uu____3888 = FStar_ST.read ex  in
                                FStar_Util.set_difference uu____3888 ns_ex
                                 in
                              FStar_ST.write ex uu____3887);
                             (match () with
                              | () ->
                                  let trans_ex = cur_trans_exports k  in
                                  let uu____3898 =
                                    let uu____3899 = FStar_ST.read trans_ex
                                       in
                                    FStar_Util.set_union uu____3899 ns_ex  in
                                  FStar_ST.write trans_ex uu____3898)
                              in
                           FStar_List.iter update_exports
                             all_exported_id_kinds
                       | uu____3905 -> ());
                      (match () with | () -> env1))
                 | None  ->
                     let uu____3919 =
                       let uu____3920 =
                         let uu____3923 =
                           FStar_Util.format1
                             "include: Module %s was not prepared"
                             ns1.FStar_Ident.str
                            in
                         (uu____3923, (FStar_Ident.range_of_lid ns1))  in
                       FStar_Errors.Error uu____3920  in
                     Prims.raise uu____3919)))
      | uu____3924 ->
          let uu____3926 =
            let uu____3927 =
              let uu____3930 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str
                 in
              (uu____3930, (FStar_Ident.range_of_lid ns))  in
            FStar_Errors.Error uu____3927  in
          Prims.raise uu____3926
  
let push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____3940 = module_is_defined env l  in
        if uu____3940
        then push_scope_mod env (Module_abbrev (x, l))
        else
          (let uu____3942 =
             let uu____3943 =
               let uu____3946 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l)
                  in
               (uu____3946, (FStar_Ident.range_of_lid l))  in
             FStar_Errors.Error uu____3943  in
           Prims.raise uu____3942)
  
let check_admits : env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,quals) ->
                let uu____3957 = try_lookup_lid env l  in
                (match uu____3957 with
                 | None  ->
                     ((let uu____3964 =
                         let uu____3965 = FStar_Options.interactive ()  in
                         Prims.op_Negation uu____3965  in
                       if uu____3964
                       then
                         let uu____3966 =
                           let uu____3967 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l)
                              in
                           let uu____3968 =
                             FStar_Syntax_Print.lid_to_string l  in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____3967 uu____3968
                            in
                         FStar_Util.print_string uu____3966
                       else ());
                      FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                        ((let uu___174_3972 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_declare_typ
                                 (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                                   quals)));
                            FStar_Syntax_Syntax.sigdoc =
                              (uu___174_3972.FStar_Syntax_Syntax.sigdoc);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___174_3972.FStar_Syntax_Syntax.sigrng)
                          }), false))
                 | Some uu____3974 -> ())
            | uu____3979 -> ()))
  
let finish : env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____3990) ->
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
                                (lid,uu____4000,uu____4001,uu____4002,uu____4003,uu____4004,uu____4005)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4012 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4015,uu____4016,quals) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4023,lbs),uu____4025,quals,uu____4027) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4042 =
                               let uu____4043 =
                                 let uu____4044 =
                                   let uu____4049 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____4049.FStar_Syntax_Syntax.fv_name  in
                                 uu____4044.FStar_Syntax_Syntax.v  in
                               uu____4043.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____4042))
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
                               let uu____4059 =
                                 let uu____4064 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____4064.FStar_Syntax_Syntax.fv_name  in
                               uu____4059.FStar_Syntax_Syntax.v  in
                             let decl =
                               let uu___175_4069 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp),
                                        (FStar_Syntax_Syntax.Assumption ::
                                        quals)));
                                 FStar_Syntax_Syntax.sigdoc =
                                   (uu___175_4069.FStar_Syntax_Syntax.sigdoc);
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___175_4069.FStar_Syntax_Syntax.sigrng)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4077 -> ()));
      (let curmod =
         let uu____4079 = current_module env  in uu____4079.FStar_Ident.str
          in
       (let uu____4081 =
          let uu____4092 = get_exported_id_set env curmod  in
          let uu____4097 = get_trans_exported_id_set env curmod  in
          (uu____4092, uu____4097)  in
        match uu____4081 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4137 = cur_ex eikind  in FStar_ST.read uu____4137
                 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____4145 =
                let uu____4146 = FStar_ST.read cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____4146  in
              FStar_ST.write cur_trans_ex_set_ref uu____4145  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4152 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___176_4164 = env  in
                  {
                    curmodule = None;
                    curmonad = (uu___176_4164.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___176_4164.exported_ids);
                    trans_exported_ids = (uu___176_4164.trans_exported_ids);
                    includes = (uu___176_4164.includes);
                    sigaccum = [];
                    sigmap = (uu___176_4164.sigmap);
                    iface = (uu___176_4164.iface);
                    admitted_iface = (uu___176_4164.admitted_iface);
                    expect_typ = (uu___176_4164.expect_typ)
                  }))))
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push : env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4177 =
       let uu____4179 = FStar_ST.read stack  in env :: uu____4179  in
     FStar_ST.write stack uu____4177);
    (let uu___177_4187 = env  in
     let uu____4188 = FStar_Util.smap_copy (sigmap env)  in
     {
       curmodule = (uu___177_4187.curmodule);
       curmonad = (uu___177_4187.curmonad);
       modules = (uu___177_4187.modules);
       scope_mods = (uu___177_4187.scope_mods);
       exported_ids = (uu___177_4187.exported_ids);
       trans_exported_ids = (uu___177_4187.trans_exported_ids);
       includes = (uu___177_4187.includes);
       sigaccum = (uu___177_4187.sigaccum);
       sigmap = uu____4188;
       iface = (uu___177_4187.iface);
       admitted_iface = (uu___177_4187.admitted_iface);
       expect_typ = (uu___177_4187.expect_typ)
     })
  
let pop : Prims.unit -> env =
  fun uu____4196  ->
    let uu____4197 = FStar_ST.read stack  in
    match uu____4197 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4210 -> failwith "Impossible: Too many pops"
  
let commit_mark : env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4216 = FStar_ST.read stack  in
     match uu____4216 with
     | uu____4221::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4228 -> failwith "Impossible: Too many pops")
  
let mark : env -> env = fun x  -> push x 
let reset_mark : Prims.unit -> env = fun uu____4235  -> pop () 
let export_interface : FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4247 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4249 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4267 = FStar_Util.smap_try_find sm' k  in
              match uu____4267 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,q) ->
                          let uu___178_4286 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_declare_typ
                                 (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                                   q)));
                            FStar_Syntax_Syntax.sigdoc =
                              (uu___178_4286.FStar_Syntax_Syntax.sigdoc);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___178_4286.FStar_Syntax_Syntax.sigrng)
                          }
                      | uu____4288 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4291 -> ()));
      env1
  
let finish_module_or_interface : env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
      then check_admits env
      else ();
      finish env modul
  
let prepare_module_or_interface :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> (env * Prims.bool)
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
                  FStar_Parser_Const.fstar_ns_lid]
               in
            let open_ns1 =
              if
                (FStar_List.length mname.FStar_Ident.ns) <>
                  (Prims.parse_int "0")
              then
                let ns = FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in ns
                  :: open_ns
              else open_ns  in
            (let uu____4335 = exported_id_set_new ()  in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4335);
            (match () with
             | () ->
                 ((let uu____4340 = exported_id_set_new ()  in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4340);
                  (match () with
                   | () ->
                       ((let uu____4345 = FStar_Util.mk_ref []  in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4345);
                        (match () with
                         | () ->
                             let uu___179_4354 = env1  in
                             let uu____4355 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1
                                in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___179_4354.curmonad);
                               modules = (uu___179_4354.modules);
                               scope_mods = uu____4355;
                               exported_ids = (uu___179_4354.exported_ids);
                               trans_exported_ids =
                                 (uu___179_4354.trans_exported_ids);
                               includes = (uu___179_4354.includes);
                               sigaccum = (uu___179_4354.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___179_4354.expect_typ)
                             })))))
             in
          let uu____4358 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4370  ->
                    match uu____4370 with
                    | (l,uu____4374) -> FStar_Ident.lid_equals l mname))
             in
          match uu____4358 with
          | None  -> let uu____4379 = prep env  in (uu____4379, false)
          | Some (uu____4380,m) ->
              ((let uu____4385 =
                  (let uu____4386 = FStar_Options.interactive ()  in
                   Prims.op_Negation uu____4386) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf)
                   in
                if uu____4385
                then
                  let uu____4387 =
                    let uu____4388 =
                      let uu____4391 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (uu____4391, (FStar_Ident.range_of_lid mname))  in
                    FStar_Errors.Error uu____4388  in
                  Prims.raise uu____4387
                else ());
               (let uu____4393 =
                  let uu____4394 = push env  in prep uu____4394  in
                (uu____4393, true)))
  
let enter_monad_scope : env -> FStar_Ident.ident -> env =
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
          let uu___180_4402 = env  in
          {
            curmodule = (uu___180_4402.curmodule);
            curmonad = (Some mname);
            modules = (uu___180_4402.modules);
            scope_mods = (uu___180_4402.scope_mods);
            exported_ids = (uu___180_4402.exported_ids);
            trans_exported_ids = (uu___180_4402.trans_exported_ids);
            includes = (uu___180_4402.includes);
            sigaccum = (uu___180_4402.sigaccum);
            sigmap = (uu___180_4402.sigmap);
            iface = (uu___180_4402.iface);
            admitted_iface = (uu___180_4402.admitted_iface);
            expect_typ = (uu___180_4402.expect_typ)
          }
  
let fail_or env lookup lid =
  let uu____4427 = lookup lid  in
  match uu____4427 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4433  ->
             match uu____4433 with
             | (lid1,uu____4437) -> FStar_Ident.text_of_lid lid1) env.modules
         in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid)
         in
      let msg1 =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let uu____4444 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
             FStar_Ident.set_lid_range uu____4444
               (FStar_Ident.range_of_lid lid)
              in
           let uu____4445 = resolve_module_name env modul true  in
           match uu____4445 with
           | None  ->
               let opened_modules1 = FStar_String.concat ", " opened_modules
                  in
               FStar_Util.format3
                 "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str opened_modules1
           | Some modul' when
               Prims.op_Negation
                 (FStar_List.existsb (fun m  -> m = modul'.FStar_Ident.str)
                    opened_modules)
               ->
               let opened_modules1 = FStar_String.concat ", " opened_modules
                  in
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 opened_modules1
           | Some modul' ->
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, definition %s not found"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 (lid.FStar_Ident.ident).FStar_Ident.idText)
         in
      Prims.raise (FStar_Errors.Error (msg1, (FStar_Ident.range_of_lid lid)))
  | Some r -> r 
let fail_or2 lookup id =
  let uu____4472 = lookup id  in
  match uu____4472 with
  | None  ->
      Prims.raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r 