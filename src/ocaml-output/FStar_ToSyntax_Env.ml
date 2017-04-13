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
  expect_typ: Prims.bool ;
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap }
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * Prims.bool) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let uu___is_Term_name : foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____324 -> false
  
let __proj__Term_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.typ * Prims.bool) =
  fun projectee  -> match projectee with | Term_name _0 -> _0 
let uu___is_Eff_name : foundname -> Prims.bool =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____344 -> false
  
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
      let uu____367 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____367 with
      | None  -> []
      | Some exported_id_set ->
          let uu____371 =
            let uu____372 = exported_id_set Exported_id_term_type  in
            FStar_ST.read uu____372  in
          FStar_All.pipe_right uu____371 FStar_Util.set_elements
  
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
      | None  -> let uu____398 = current_module env  in qual uu____398 id
      | Some monad ->
          let uu____400 =
            let uu____401 = current_module env  in qual uu____401 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____400 id
  
let new_sigmap uu____409 = FStar_Util.smap_create (Prims.parse_int "100") 
let empty_env : Prims.unit -> env =
  fun uu____412  ->
    let uu____413 = new_sigmap ()  in
    let uu____415 = new_sigmap ()  in
    let uu____417 = new_sigmap ()  in
    let uu____423 = new_sigmap ()  in
    let uu____429 = new_sigmap ()  in
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
  
let sigmap : env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap
  = fun env  -> env.sigmap 
let has_all_in_scope : env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____444  ->
         match uu____444 with
         | (m,uu____448) ->
             FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid) env.modules
  
let set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___166_456 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___166_456.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___167_457 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___167_457.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___167_457.FStar_Syntax_Syntax.sort)
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
        (fun uu____503  ->
           match uu____503 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____517 =
                   let uu____518 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____518 dd dq  in
                 Some uu____517
               else None)
       in
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
        (fun uu____647  ->
           match uu____647 with
           | (f,uu____652) ->
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
  fun uu___140_688  ->
    match uu___140_688 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
  
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText  in
  let rec aux uu___141_737 =
    match uu___141_737 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str  in
        let not_shadowed =
          let uu____745 = get_exported_id_set env mname  in
          match uu____745 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____761 = mex eikind  in FStar_ST.read uu____761  in
              FStar_Util.set_mem idstr mexports
           in
        let mincludes =
          let uu____768 = FStar_Util.smap_try_find env.includes mname  in
          match uu____768 with
          | None  -> []
          | Some minc -> FStar_ST.read minc  in
        let look_into =
          if not_shadowed
          then let uu____788 = qual modul id  in find_in_module uu____788
          else Cont_ignore  in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____791 -> look_into)
     in
  aux [ns] 
let is_exported_id_field : exported_id_kind -> Prims.bool =
  fun uu___142_795  ->
    match uu___142_795 with | Exported_id_field  -> true | uu____796 -> false
  
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___143_885 =
    match uu___143_885 with
    | (id',uu____887,uu____888) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText
     in
  let check_rec_binding_id uu___144_892 =
    match uu___144_892 with
    | (id',uu____894,uu____895) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText
     in
  let curmod_ns =
    let uu____898 = current_module env  in FStar_Ident.ids_of_lid uu____898
     in
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
        let uu____911 = FStar_Ident.lid_of_ids curmod_ns  in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident  in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____911 id
    | uu____914 -> Cont_ignore  in
  let rec aux uu___146_920 =
    match uu___146_920 with
    | a::q ->
        let uu____926 = proc a  in
        option_of_cont (fun uu____928  -> aux q) uu____926
    | [] ->
        let uu____929 = lookup_default_id Cont_fail id  in
        option_of_cont (fun uu____931  -> None) uu____929
     in
  aux env.scope_mods 
let found_local_binding r uu____950 =
  match uu____950 with
  | (id',x,mut) -> let uu____957 = bv_to_name x r  in (uu____957, mut) 
let find_in_module env lid k_global_def k_not_found =
  let uu____994 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
     in
  match uu____994 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found 
let try_lookup_id :
  env ->
    FStar_Ident.ident -> (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  =
  fun env  ->
    fun id  ->
      let uu____1016 = unmangleOpName id  in
      match uu____1016 with
      | Some f -> Some f
      | uu____1030 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1037 = found_local_binding id.FStar_Ident.idRange r
                  in
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
        let lid = qualify env id  in
        let uu____1115 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
        (match uu____1115 with
         | Some r -> let uu____1128 = k_global_def lid r  in Some uu____1128
         | None  -> None)
    | None  -> None  in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1141 = current_module env  in qual uu____1141 id
         in
      find_in_module env lid k_global_def k_not_found
  
let module_is_defined : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
           let uu____1150 = current_module env  in
           FStar_Ident.lid_equals lid uu____1150)
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
        let rec aux uu___147_1174 =
          match uu___147_1174 with
          | [] ->
              let uu____1177 = module_is_defined env lid  in
              if uu____1177 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1184 =
                  let uu____1186 = FStar_Ident.path_of_lid ns  in
                  let uu____1188 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____1186 uu____1188  in
                FStar_Ident.lid_of_path uu____1184
                  (FStar_Ident.range_of_lid lid)
                 in
              let uu____1190 = module_is_defined env new_lid  in
              if uu____1190 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1195 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1199::q -> aux q  in
        aux env.scope_mods
  
let fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____1211 =
          let uu____1212 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____1212  in
        if uu____1211
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Syntax_Const.prims_lid
           then ()
           else
             (let uu____1214 =
                let uu____1215 =
                  let uu____1218 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str
                     in
                  (uu____1218, (FStar_Ident.range_of_lid ns_original))  in
                FStar_Errors.Error uu____1215  in
              Prims.raise uu____1214))
        else ()
  
let fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> Prims.unit
  =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____1226 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____1229 = resolve_module_name env modul_orig true  in
          (match uu____1229 with
           | Some modul_res -> fail_if_curmodule env modul_orig modul_res
           | uu____1232 -> ())
  
let namespace_is_open : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___148_1240  ->
           match uu___148_1240 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1242 -> false) env.scope_mods
  
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
                 let uu____1297 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____1297
                   (FStar_Util.map_option
                      (fun uu____1321  ->
                         match uu____1321 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids)))))
           in
        let uu____1338 =
          is_full_path &&
            (let uu____1339 = FStar_Ident.lid_of_ids ids  in
             module_is_defined env uu____1339)
           in
        if uu____1338
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1356 = aux ns_rev_prefix ns_last_id  in
               (match uu____1356 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
  
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1469::uu____1470 ->
      let uu____1472 =
        let uu____1474 =
          let uu____1475 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_Ident.set_lid_range uu____1475 (FStar_Ident.range_of_lid lid)
           in
        resolve_module_name env uu____1474 true  in
      (match uu____1472 with
       | None  -> None
       | Some modul ->
           let uu____1478 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident
              in
           option_of_cont (fun uu____1480  -> None) uu____1478)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
  
let cont_of_option k_none uu___149_1495 =
  match uu___149_1495 with | Some v1 -> Cont_ok v1 | None  -> k_none 
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1574 = k_global_def lid1 def  in cont_of_option k uu____1574
     in
  let f_module lid' =
    let k = Cont_ignore  in find_in_module env lid' (k_global_def' k) k  in
  let l_default k i = lookup_default_id env i (k_global_def' k) k  in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1595 = k_local_binding l  in
       cont_of_option Cont_fail uu____1595)
    (fun r  ->
       let uu____1598 = k_rec_binding r  in
       cont_of_option Cont_fail uu____1598) (fun uu____1600  -> Cont_ignore)
    f_module l_default
  
let fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual Prims.option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1606,uu____1607,uu____1608,l,uu____1610,quals,uu____1612) ->
        let qopt =
          FStar_Util.find_map quals
            (fun uu___150_1619  ->
               match uu___150_1619 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1621,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1628 -> None)
           in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____1632,uu____1633,uu____1634,quals) -> None
    | uu____1638 -> None
  
let lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1647 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____1651 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____1651 then Some fv else None)
         in
      FStar_All.pipe_right uu____1647 FStar_Util.must
  
let ns_of_lid_equals : FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1665 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____1665 ns)
  
let try_lookup_name :
  Prims.bool ->
    Prims.bool -> env -> FStar_Ident.lident -> foundname Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid  in
          let k_global_def source_lid uu___154_1690 =
            match uu___154_1690 with
            | (uu____1694,true ) when exclude_interf -> None
            | (se,uu____1696) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1698 ->
                     let uu____1709 =
                       let uu____1710 =
                         let uu____1713 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None
                            in
                         (uu____1713, false)  in
                       Term_name uu____1710  in
                     Some uu____1709
                 | FStar_Syntax_Syntax.Sig_datacon uu____1714 ->
                     let uu____1724 =
                       let uu____1725 =
                         let uu____1728 =
                           let uu____1729 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1729
                            in
                         (uu____1728, false)  in
                       Term_name uu____1725  in
                     Some uu____1724
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1731,lbs),uu____1733,uu____1734,uu____1735) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____1748 =
                       let uu____1749 =
                         let uu____1752 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____1752, false)  in
                       Term_name uu____1749  in
                     Some uu____1748
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1754,uu____1755,quals) ->
                     let uu____1759 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___151_1761  ->
                                  match uu___151_1761 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1762 -> false)))
                        in
                     if uu____1759
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid)
                          in
                       let dd =
                         let uu____1766 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___152_1768  ->
                                         match uu___152_1768 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1771 -> false))))
                            in
                         if uu____1766
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let uu____1773 =
                         FStar_Util.find_map quals
                           (fun uu___153_1775  ->
                              match uu___153_1775 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1778 -> None)
                          in
                       (match uu____1773 with
                        | Some refl_monad ->
                            let refl_const =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reflect refl_monad)))
                                None occurrence_range
                               in
                            Some (Term_name (refl_const, false))
                        | uu____1794 ->
                            let uu____1796 =
                              let uu____1797 =
                                let uu____1800 =
                                  let uu____1801 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____1801
                                   in
                                (uu____1800, false)  in
                              Term_name uu____1797  in
                            Some uu____1796)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1805 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1814 -> None)
             in
          let k_local_binding r =
            let uu____1826 =
              let uu____1827 =
                found_local_binding (FStar_Ident.range_of_lid lid) r  in
              Term_name uu____1827  in
            Some uu____1826  in
          let k_rec_binding uu____1837 =
            match uu____1837 with
            | (id,l,dd) ->
                let uu____1845 =
                  let uu____1846 =
                    let uu____1849 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None
                       in
                    (uu____1849, false)  in
                  Term_name uu____1846  in
                Some uu____1845
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____1853 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____1853 with
                 | Some f -> Some (Term_name f)
                 | uu____1863 -> None)
            | uu____1867 -> None  in
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
        let uu____1887 = try_lookup_name true exclude_interf env lid  in
        match uu____1887 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____1896 -> None
  
let try_lookup_effect_name :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1907 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1907 with | Some (o,l1) -> Some l1 | uu____1916 -> None
  
let try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)
        Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____1930 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1930 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____1939;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____1948;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____1956,uu____1957,uu____1958,uu____1959,uu____1960,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____1962;_},l1)
          -> Some (l1, cattributes)
      | uu____1974 -> None
  
let try_lookup_effect_defn :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      let uu____1988 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1988 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____1994;_},uu____1995)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____1999;_},uu____2000)
          -> Some ne
      | uu____2003 -> None
  
let is_effect_name : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2013 = try_lookup_effect_name env lid  in
      match uu____2013 with | None  -> false | Some uu____2015 -> true
  
let try_lookup_root_effect_name :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2023 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____2023 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____2029,uu____2030,uu____2031,uu____2032,uu____2033);
             FStar_Syntax_Syntax.sigrng = uu____2034;_},uu____2035)
          ->
          let rec aux new_name =
            let uu____2047 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____2047 with
            | None  -> None
            | Some (s,uu____2057) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____2062,uu____2063,uu____2064,cmp,uu____2066,uu____2067)
                     ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____2073 -> None)
             in
          aux l'
      | Some (uu____2074,l') -> Some l'
      | uu____2078 -> None
  
let lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___155_2099 =
        match uu___155_2099 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (lid2,uu____2105,uu____2106,quals);
             FStar_Syntax_Syntax.sigrng = uu____2108;_},uu____2109)
            -> Some quals
        | uu____2113 -> None  in
      let uu____2117 =
        resolve_in_open_namespaces' env lid (fun uu____2121  -> None)
          (fun uu____2123  -> None) k_global_def
         in
      match uu____2117 with | Some quals -> quals | uu____2129 -> []
  
let try_lookup_module :
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul Prims.option =
  fun env  ->
    fun path  ->
      let uu____2141 =
        FStar_List.tryFind
          (fun uu____2147  ->
             match uu____2147 with
             | (mlid,modul) ->
                 let uu____2152 = FStar_Ident.path_of_lid mlid  in
                 uu____2152 = path) env.modules
         in
      match uu____2141 with
      | Some (uu____2156,modul) -> Some modul
      | None  -> None
  
let try_lookup_let :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___156_2178 =
        match uu___156_2178 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2182,lbs),uu____2184,uu____2185,uu____2186);
             FStar_Syntax_Syntax.sigrng = uu____2187;_},uu____2188)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____2201 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            Some uu____2201
        | uu____2202 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2205  -> None)
        (fun uu____2206  -> None) k_global_def
  
let try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___157_2225 =
        match uu___157_2225 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2232,uu____2233,uu____2234);
             FStar_Syntax_Syntax.sigrng = uu____2235;_},uu____2236)
            ->
            FStar_Util.find_map (Prims.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2253 -> None)
        | uu____2258 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2265  -> None)
        (fun uu____2268  -> None) k_global_def
  
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
          let uu____2295 = try_lookup_name any_val exclude_interf env lid  in
          match uu____2295 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2304 -> None
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l 
let resolve_to_fully_qualified_name :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2324 = try_lookup_lid env l  in
      match uu____2324 with
      | None  -> None
      | Some (e,uu____2332) ->
          let uu____2335 =
            let uu____2336 = FStar_Syntax_Subst.compress e  in
            uu____2336.FStar_Syntax_Syntax.n  in
          (match uu____2335 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2345 -> None)
  
let try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___168_2356 = env  in
        {
          curmodule = (uu___168_2356.curmodule);
          curmonad = (uu___168_2356.curmonad);
          modules = (uu___168_2356.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___168_2356.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___168_2356.sigaccum);
          sigmap = (uu___168_2356.sigmap);
          iface = (uu___168_2356.iface);
          admitted_iface = (uu___168_2356.admitted_iface);
          expect_typ = (uu___168_2356.expect_typ);
          docs = (uu___168_2356.docs)
        }  in
      try_lookup_lid env' l
  
let try_lookup_doc :
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str 
let try_lookup_datacon :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___159_2380 =
        match uu___159_2380 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2384,uu____2385,uu____2386,quals);
             FStar_Syntax_Syntax.sigrng = uu____2388;_},uu____2389)
            ->
            let uu____2392 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___158_2394  ->
                      match uu___158_2394 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2395 -> false))
               in
            if uu____2392
            then
              let uu____2397 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None
                 in
              Some uu____2397
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2399;
             FStar_Syntax_Syntax.sigrng = uu____2400;_},uu____2401)
            ->
            let uu____2411 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor)
               in
            Some uu____2411
        | uu____2412 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2415  -> None)
        (fun uu____2416  -> None) k_global_def
  
let find_all_datacons :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___160_2435 =
        match uu___160_2435 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2440,uu____2441,uu____2442,uu____2443,uu____2444,datas,uu____2446);
             FStar_Syntax_Syntax.sigrng = uu____2447;_},uu____2448)
            -> Some datas
        | uu____2456 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2461  -> None)
        (fun uu____2463  -> None) k_global_def
  
let record_cache_aux_with_filter :
  (((Prims.unit -> Prims.unit) * (Prims.unit -> Prims.unit) *
    (Prims.unit -> record_or_dc Prims.list) * (record_or_dc -> Prims.unit) *
    (Prims.unit -> Prims.unit)) * (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____2497 =
    let uu____2498 =
      let uu____2501 =
        let uu____2503 = FStar_ST.read record_cache  in
        FStar_List.hd uu____2503  in
      let uu____2511 = FStar_ST.read record_cache  in uu____2501 ::
        uu____2511
       in
    FStar_ST.write record_cache uu____2498  in
  let pop1 uu____2526 =
    let uu____2527 =
      let uu____2530 = FStar_ST.read record_cache  in
      FStar_List.tl uu____2530  in
    FStar_ST.write record_cache uu____2527  in
  let peek uu____2546 =
    let uu____2547 = FStar_ST.read record_cache  in FStar_List.hd uu____2547
     in
  let insert r =
    let uu____2559 =
      let uu____2562 = let uu____2564 = peek ()  in r :: uu____2564  in
      let uu____2566 =
        let uu____2569 = FStar_ST.read record_cache  in
        FStar_List.tl uu____2569  in
      uu____2562 :: uu____2566  in
    FStar_ST.write record_cache uu____2559  in
  let commit1 uu____2585 =
    let uu____2586 = FStar_ST.read record_cache  in
    match uu____2586 with
    | hd1::uu____2594::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2607 -> failwith "Impossible"  in
  let filter1 uu____2613 =
    let rc = peek ()  in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
            in
         let uu____2620 =
           let uu____2623 = FStar_ST.read record_cache  in filtered ::
             uu____2623
            in
         FStar_ST.write record_cache uu____2620)
     in
  let aux = (push1, pop1, peek, insert, commit1)  in (aux, filter1) 
let record_cache_aux :
  ((Prims.unit -> Prims.unit) * (Prims.unit -> Prims.unit) *
    (Prims.unit -> record_or_dc Prims.list) * (record_or_dc -> Prims.unit) *
    (Prims.unit -> Prims.unit))
  =
  let uu____2697 = record_cache_aux_with_filter  in
  match uu____2697 with | (aux,uu____2735) -> aux 
let filter_record_cache : Prims.unit -> Prims.unit =
  let uu____2774 = record_cache_aux_with_filter  in
  match uu____2774 with | (uu____2797,filter1) -> filter1 
let push_record_cache : Prims.unit -> Prims.unit =
  let uu____2837 = record_cache_aux  in
  match uu____2837 with
  | (push1,uu____2857,uu____2858,uu____2859,uu____2860) -> push1 
let pop_record_cache : Prims.unit -> Prims.unit =
  let uu____2885 = record_cache_aux  in
  match uu____2885 with
  | (uu____2904,pop1,uu____2906,uu____2907,uu____2908) -> pop1 
let peek_record_cache : Prims.unit -> record_or_dc Prims.list =
  let uu____2934 = record_cache_aux  in
  match uu____2934 with
  | (uu____2954,uu____2955,peek,uu____2957,uu____2958) -> peek 
let insert_record_cache : record_or_dc -> Prims.unit =
  let uu____2983 = record_cache_aux  in
  match uu____2983 with
  | (uu____3002,uu____3003,uu____3004,insert,uu____3006) -> insert 
let commit_record_cache : Prims.unit -> Prims.unit =
  let uu____3031 = record_cache_aux  in
  match uu____3031 with
  | (uu____3050,uu____3051,uu____3052,uu____3053,commit1) -> commit1 
let extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3093,uu____3094) ->
            let is_rec =
              FStar_Util.for_some
                (fun uu___161_3105  ->
                   match uu___161_3105 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____3108 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___162_3116  ->
                      match uu___162_3116 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3118,uu____3119,uu____3120,uu____3121,uu____3122,uu____3123);
                          FStar_Syntax_Syntax.sigrng = uu____3124;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3129 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___163_3131  ->
                    match uu___163_3131 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____3135,uu____3136,dc::[],tags);
                        FStar_Syntax_Syntax.sigrng = uu____3139;_} ->
                        let uu____3145 =
                          let uu____3146 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____3146  in
                        (match uu____3145 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3150,t,uu____3152,uu____3153,uu____3154,uu____3155);
                             FStar_Syntax_Syntax.sigrng = uu____3156;_} ->
                             let uu____3161 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____3161 with
                              | (formals,uu____3170) ->
                                  let is_rec1 = is_rec tags  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3196  ->
                                            match uu____3196 with
                                            | (x,q) ->
                                                let uu____3204 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec1 &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____3204
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3235  ->
                                            match uu____3235 with
                                            | (x,q) ->
                                                let uu____3244 =
                                                  if is_rec1
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____3244,
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
                                  ((let uu____3256 =
                                      let uu____3258 =
                                        FStar_ST.read new_globs  in
                                      (Record_or_dc record) :: uu____3258  in
                                    FStar_ST.write new_globs uu____3256);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3274 =
                                            match uu____3274 with
                                            | (id,uu____3280) ->
                                                let modul =
                                                  let uu____3286 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____3286.FStar_Ident.str
                                                   in
                                                let uu____3287 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____3287 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____3303 =
                                                         let uu____3304 =
                                                           FStar_ST.read
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3304
                                                          in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3303);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3311 =
                                                               let uu____3312
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id
                                                                  in
                                                               uu____3312.FStar_Ident.ident
                                                                in
                                                             uu____3311.FStar_Ident.idText
                                                              in
                                                           let uu____3314 =
                                                             let uu____3315 =
                                                               FStar_ST.read
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3315
                                                              in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3314))
                                                 | None  -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3328 -> ())
                    | uu____3329 -> ()))
        | uu____3330 -> ()
  
let try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3343 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____3343 with
        | (ns,id) ->
            let uu____3353 = peek_record_cache ()  in
            FStar_Util.find_map uu____3353
              (fun record  ->
                 let uu____3356 =
                   find_in_record ns id record (fun r  -> Cont_ok r)  in
                 option_of_cont (fun uu____3359  -> None) uu____3356)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3360  -> Cont_ignore) (fun uu____3361  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3364 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____3364)
        (fun k  -> fun uu____3367  -> k)
  
let try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let uu____3376 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____3376 with
      | Some r when r.is_record -> Some r
      | uu____3380 -> None
  
let belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3391 = try_lookup_record_by_field_name env lid  in
        match uu____3391 with
        | Some record' when
            let uu____3394 =
              let uu____3395 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____3395  in
            let uu____3397 =
              let uu____3398 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____3398  in
            uu____3394 = uu____3397 ->
            let uu____3400 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3402  -> Cont_ok ())
               in
            (match uu____3400 with
             | Cont_ok uu____3403 -> true
             | uu____3404 -> false)
        | uu____3406 -> false
  
let try_lookup_dc_by_field_name :
  env -> FStar_Ident.lident -> (FStar_Ident.lident * Prims.bool) Prims.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____3417 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____3417 with
      | Some r ->
          let uu____3423 =
            let uu____3426 =
              let uu____3427 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              FStar_Ident.set_lid_range uu____3427
                (FStar_Ident.range_of_lid fieldname)
               in
            (uu____3426, (r.is_record))  in
          Some uu____3423
      | uu____3430 -> None
  
let string_set_ref_new :
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3439  ->
    let uu____3440 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode  in
    FStar_Util.mk_ref uu____3440
  
let exported_id_set_new :
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3451  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___164_3460  ->
      match uu___164_3460 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___165_3480 =
            match uu___165_3480 with
            | Rec_binding uu____3481 -> true
            | uu____3482 -> false  in
          let this_env =
            let uu___169_3484 = env  in
            let uu____3485 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___169_3484.curmodule);
              curmonad = (uu___169_3484.curmonad);
              modules = (uu___169_3484.modules);
              scope_mods = uu____3485;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___169_3484.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___169_3484.sigaccum);
              sigmap = (uu___169_3484.sigmap);
              iface = (uu___169_3484.iface);
              admitted_iface = (uu___169_3484.admitted_iface);
              expect_typ = (uu___169_3484.expect_typ);
              docs = (uu___169_3484.docs)
            }  in
          let uu____3487 = try_lookup_lid' any_val exclude_if this_env lid
             in
          match uu____3487 with | None  -> true | Some uu____3493 -> false
  
let push_scope_mod : env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___170_3504 = env  in
      {
        curmodule = (uu___170_3504.curmodule);
        curmonad = (uu___170_3504.curmonad);
        modules = (uu___170_3504.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___170_3504.exported_ids);
        trans_exported_ids = (uu___170_3504.trans_exported_ids);
        includes = (uu___170_3504.includes);
        sigaccum = (uu___170_3504.sigaccum);
        sigmap = (uu___170_3504.sigmap);
        iface = (uu___170_3504.iface);
        admitted_iface = (uu___170_3504.admitted_iface);
        expect_typ = (uu___170_3504.expect_typ);
        docs = (uu___170_3504.docs)
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
        let uu____3543 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____3543
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
          | Some (se,uu____3563) ->
              let uu____3566 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____3566 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>"  in
        let uu____3571 =
          let uu____3572 =
            let uu____3575 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r
               in
            (uu____3575, (FStar_Ident.range_of_lid l))  in
          FStar_Errors.Error uu____3572  in
        Prims.raise uu____3571  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____3582 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3587 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3595 -> (true, true)
          | uu____3602 -> (false, false)  in
        match uu____3582 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____3607 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3610 =
                     let uu____3611 = unique any_val exclude_if env l  in
                     Prims.op_Negation uu____3611  in
                   if uu____3610 then Some l else None)
               in
            (match uu____3607 with
             | Some l when
                 let uu____3615 = FStar_Options.interactive ()  in
                 Prims.op_Negation uu____3615 -> err l
             | uu____3616 ->
                 (extract_record env globals s;
                  (let uu___171_3621 = env  in
                   {
                     curmodule = (uu___171_3621.curmodule);
                     curmonad = (uu___171_3621.curmonad);
                     modules = (uu___171_3621.modules);
                     scope_mods = (uu___171_3621.scope_mods);
                     exported_ids = (uu___171_3621.exported_ids);
                     trans_exported_ids = (uu___171_3621.trans_exported_ids);
                     includes = (uu___171_3621.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___171_3621.sigmap);
                     iface = (uu___171_3621.iface);
                     admitted_iface = (uu___171_3621.admitted_iface);
                     expect_typ = (uu___171_3621.expect_typ);
                     docs = (uu___171_3621.docs)
                   })))
         in
      let env2 =
        let uu___172_3623 = env1  in
        let uu____3624 = FStar_ST.read globals  in
        {
          curmodule = (uu___172_3623.curmodule);
          curmonad = (uu___172_3623.curmonad);
          modules = (uu___172_3623.modules);
          scope_mods = uu____3624;
          exported_ids = (uu___172_3623.exported_ids);
          trans_exported_ids = (uu___172_3623.trans_exported_ids);
          includes = (uu___172_3623.includes);
          sigaccum = (uu___172_3623.sigaccum);
          sigmap = (uu___172_3623.sigmap);
          iface = (uu___172_3623.iface);
          admitted_iface = (uu___172_3623.admitted_iface);
          expect_typ = (uu___172_3623.expect_typ);
          docs = (uu___172_3623.docs)
        }  in
      let uu____3629 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3643,uu____3644) ->
            let uu____3651 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____3651)
        | uu____3665 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____3629 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3695  ->
                   match uu____3695 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3706 =
                                  let uu____3708 = FStar_ST.read globals  in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3708
                                   in
                                FStar_ST.write globals uu____3706);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3717 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____3717.FStar_Ident.str  in
                                    ((let uu____3719 =
                                        get_exported_id_set env3 modul  in
                                      match uu____3719 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____3734 =
                                            let uu____3735 =
                                              FStar_ST.read my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3735
                                             in
                                          FStar_ST.write my_exported_ids
                                            uu____3734
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
              let uu___173_3747 = env3  in
              let uu____3748 = FStar_ST.read globals  in
              {
                curmodule = (uu___173_3747.curmodule);
                curmonad = (uu___173_3747.curmonad);
                modules = (uu___173_3747.modules);
                scope_mods = uu____3748;
                exported_ids = (uu___173_3747.exported_ids);
                trans_exported_ids = (uu___173_3747.trans_exported_ids);
                includes = (uu___173_3747.includes);
                sigaccum = (uu___173_3747.sigaccum);
                sigmap = (uu___173_3747.sigmap);
                iface = (uu___173_3747.iface);
                admitted_iface = (uu___173_3747.admitted_iface);
                expect_typ = (uu___173_3747.expect_typ);
                docs = (uu___173_3747.docs)
              }  in
            env4))
  
let push_namespace : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3759 =
        let uu____3762 = resolve_module_name env ns false  in
        match uu____3762 with
        | None  ->
            let modules = env.modules  in
            let uu____3770 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3776  ->
                      match uu____3776 with
                      | (m,uu____3780) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) ".")))
               in
            if uu____3770
            then (ns, Open_namespace)
            else
              (let uu____3784 =
                 let uu____3785 =
                   let uu____3788 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns)
                      in
                   (uu____3788, (FStar_Ident.range_of_lid ns))  in
                 FStar_Errors.Error uu____3785  in
               Prims.raise uu____3784)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module))  in
      match uu____3759 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
  
let push_include : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____3802 = resolve_module_name env ns false  in
      match uu____3802 with
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____3808 = current_module env1  in
              uu____3808.FStar_Ident.str  in
            (let uu____3810 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____3810 with
             | None  -> ()
             | Some incl ->
                 let uu____3823 =
                   let uu____3825 = FStar_ST.read incl  in ns1 :: uu____3825
                    in
                 FStar_ST.write incl uu____3823);
            (match () with
             | () ->
                 let uu____3833 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____3833 with
                  | Some ns_trans_exports ->
                      ((let uu____3846 =
                          let uu____3857 = get_exported_id_set env1 curmod
                             in
                          let uu____3862 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____3857, uu____3862)  in
                        match uu____3846 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____3902 = ns_trans_exports k  in
                                FStar_ST.read uu____3902  in
                              let ex = cur_exports k  in
                              (let uu____3911 =
                                 let uu____3912 = FStar_ST.read ex  in
                                 FStar_Util.set_difference uu____3912 ns_ex
                                  in
                               FStar_ST.write ex uu____3911);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____3922 =
                                     let uu____3923 = FStar_ST.read trans_ex
                                        in
                                     FStar_Util.set_union uu____3923 ns_ex
                                      in
                                   FStar_ST.write trans_ex uu____3922)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____3929 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____3943 =
                        let uu____3944 =
                          let uu____3947 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str
                             in
                          (uu____3947, (FStar_Ident.range_of_lid ns1))  in
                        FStar_Errors.Error uu____3944  in
                      Prims.raise uu____3943))))
      | uu____3948 ->
          let uu____3950 =
            let uu____3951 =
              let uu____3954 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str
                 in
              (uu____3954, (FStar_Ident.range_of_lid ns))  in
            FStar_Errors.Error uu____3951  in
          Prims.raise uu____3950
  
let push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____3964 = module_is_defined env l  in
        if uu____3964
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____3967 =
             let uu____3968 =
               let uu____3971 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l)
                  in
               (uu____3971, (FStar_Ident.range_of_lid l))  in
             FStar_Errors.Error uu____3968  in
           Prims.raise uu____3967)
  
let push_doc :
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option -> env =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____3985 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____3985 with
              | None  -> ()
              | Some old_doc ->
                  let uu____3988 =
                    let uu____3989 = FStar_Ident.string_of_lid l  in
                    let uu____3990 = FStar_Parser_AST.string_of_fsdoc old_doc
                       in
                    let uu____3991 = FStar_Parser_AST.string_of_fsdoc doc1
                       in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____3989 uu____3990 uu____3991
                     in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____3988);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
  
let check_admits : env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,quals) ->
                let uu____4003 = try_lookup_lid env l  in
                (match uu____4003 with
                 | None  ->
                     ((let uu____4010 =
                         let uu____4011 = FStar_Options.interactive ()  in
                         Prims.op_Negation uu____4011  in
                       if uu____4010
                       then
                         let uu____4012 =
                           let uu____4013 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l)
                              in
                           let uu____4014 =
                             FStar_Syntax_Print.lid_to_string l  in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____4013 uu____4014
                            in
                         FStar_Util.print_string uu____4012
                       else ());
                      FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                        ((let uu___174_4018 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_declare_typ
                                 (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                                   quals)));
                            FStar_Syntax_Syntax.sigrng =
                              (uu___174_4018.FStar_Syntax_Syntax.sigrng)
                          }), false))
                 | Some uu____4020 -> ())
            | uu____4025 -> ()))
  
let finish : env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4036) ->
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
                                (lid,uu____4046,uu____4047,uu____4048,uu____4049,uu____4050,uu____4051)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4058 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4061,uu____4062,quals) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4069,lbs),uu____4071,quals,uu____4073) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4088 =
                               let uu____4089 =
                                 let uu____4090 =
                                   let uu____4095 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____4095.FStar_Syntax_Syntax.fv_name  in
                                 uu____4090.FStar_Syntax_Syntax.v  in
                               uu____4089.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____4088))
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
                               let uu____4105 =
                                 let uu____4110 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____4110.FStar_Syntax_Syntax.fv_name  in
                               uu____4105.FStar_Syntax_Syntax.v  in
                             let decl =
                               let uu___175_4115 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp),
                                        (FStar_Syntax_Syntax.Assumption ::
                                        quals)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___175_4115.FStar_Syntax_Syntax.sigrng)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4123 -> ()));
      (let curmod =
         let uu____4125 = current_module env  in uu____4125.FStar_Ident.str
          in
       (let uu____4127 =
          let uu____4138 = get_exported_id_set env curmod  in
          let uu____4143 = get_trans_exported_id_set env curmod  in
          (uu____4138, uu____4143)  in
        match uu____4127 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4183 = cur_ex eikind  in FStar_ST.read uu____4183
                 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____4191 =
                let uu____4192 = FStar_ST.read cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____4192  in
              FStar_ST.write cur_trans_ex_set_ref uu____4191  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4198 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___176_4210 = env  in
                  {
                    curmodule = None;
                    curmonad = (uu___176_4210.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___176_4210.exported_ids);
                    trans_exported_ids = (uu___176_4210.trans_exported_ids);
                    includes = (uu___176_4210.includes);
                    sigaccum = [];
                    sigmap = (uu___176_4210.sigmap);
                    iface = (uu___176_4210.iface);
                    admitted_iface = (uu___176_4210.admitted_iface);
                    expect_typ = (uu___176_4210.expect_typ);
                    docs = (uu___176_4210.docs)
                  }))))
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push : env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4223 =
       let uu____4225 = FStar_ST.read stack  in env :: uu____4225  in
     FStar_ST.write stack uu____4223);
    (let uu___177_4233 = env  in
     let uu____4234 = FStar_Util.smap_copy (sigmap env)  in
     let uu____4240 = FStar_Util.smap_copy env.docs  in
     {
       curmodule = (uu___177_4233.curmodule);
       curmonad = (uu___177_4233.curmonad);
       modules = (uu___177_4233.modules);
       scope_mods = (uu___177_4233.scope_mods);
       exported_ids = (uu___177_4233.exported_ids);
       trans_exported_ids = (uu___177_4233.trans_exported_ids);
       includes = (uu___177_4233.includes);
       sigaccum = (uu___177_4233.sigaccum);
       sigmap = uu____4234;
       iface = (uu___177_4233.iface);
       admitted_iface = (uu___177_4233.admitted_iface);
       expect_typ = (uu___177_4233.expect_typ);
       docs = uu____4240
     })
  
let pop : Prims.unit -> env =
  fun uu____4244  ->
    let uu____4245 = FStar_ST.read stack  in
    match uu____4245 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4258 -> failwith "Impossible: Too many pops"
  
let commit_mark : env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4264 = FStar_ST.read stack  in
     match uu____4264 with
     | uu____4269::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4276 -> failwith "Impossible: Too many pops")
  
let mark : env -> env = fun x  -> push x 
let reset_mark : Prims.unit -> env = fun uu____4283  -> pop () 
let export_interface : FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4295 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4297 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4315 = FStar_Util.smap_try_find sm' k  in
              match uu____4315 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,q) ->
                          let uu___178_4334 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_declare_typ
                                 (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                                   q)));
                            FStar_Syntax_Syntax.sigrng =
                              (uu___178_4334.FStar_Syntax_Syntax.sigrng)
                          }
                      | uu____4336 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4339 -> ()));
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
                  FStar_Syntax_Const.fstar_ns_lid]
               in
            let open_ns1 =
              if
                (FStar_List.length mname.FStar_Ident.ns) <>
                  (Prims.parse_int "0")
              then
                let ns = FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in ns
                  :: open_ns
              else open_ns  in
            (let uu____4383 = exported_id_set_new ()  in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4383);
            (match () with
             | () ->
                 ((let uu____4388 = exported_id_set_new ()  in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4388);
                  (match () with
                   | () ->
                       ((let uu____4393 = FStar_Util.mk_ref []  in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4393);
                        (match () with
                         | () ->
                             let uu___179_4402 = env1  in
                             let uu____4403 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1
                                in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___179_4402.curmonad);
                               modules = (uu___179_4402.modules);
                               scope_mods = uu____4403;
                               exported_ids = (uu___179_4402.exported_ids);
                               trans_exported_ids =
                                 (uu___179_4402.trans_exported_ids);
                               includes = (uu___179_4402.includes);
                               sigaccum = (uu___179_4402.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___179_4402.expect_typ);
                               docs = (uu___179_4402.docs)
                             })))))
             in
          let uu____4406 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4418  ->
                    match uu____4418 with
                    | (l,uu____4422) -> FStar_Ident.lid_equals l mname))
             in
          match uu____4406 with
          | None  -> let uu____4427 = prep env  in (uu____4427, false)
          | Some (uu____4428,m) ->
              ((let uu____4433 =
                  (let uu____4434 = FStar_Options.interactive ()  in
                   Prims.op_Negation uu____4434) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf)
                   in
                if uu____4433
                then
                  let uu____4435 =
                    let uu____4436 =
                      let uu____4439 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (uu____4439, (FStar_Ident.range_of_lid mname))  in
                    FStar_Errors.Error uu____4436  in
                  Prims.raise uu____4435
                else ());
               (let uu____4441 =
                  let uu____4442 = push env  in prep uu____4442  in
                (uu____4441, true)))
  
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
          let uu___180_4450 = env  in
          {
            curmodule = (uu___180_4450.curmodule);
            curmonad = (Some mname);
            modules = (uu___180_4450.modules);
            scope_mods = (uu___180_4450.scope_mods);
            exported_ids = (uu___180_4450.exported_ids);
            trans_exported_ids = (uu___180_4450.trans_exported_ids);
            includes = (uu___180_4450.includes);
            sigaccum = (uu___180_4450.sigaccum);
            sigmap = (uu___180_4450.sigmap);
            iface = (uu___180_4450.iface);
            admitted_iface = (uu___180_4450.admitted_iface);
            expect_typ = (uu___180_4450.expect_typ);
            docs = (uu___180_4450.docs)
          }
  
let fail_or env lookup lid =
  let uu____4475 = lookup lid  in
  match uu____4475 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4481  ->
             match uu____4481 with
             | (lid1,uu____4485) -> FStar_Ident.text_of_lid lid1) env.modules
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
             let uu____4492 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
             FStar_Ident.set_lid_range uu____4492
               (FStar_Ident.range_of_lid lid)
              in
           let uu____4493 = resolve_module_name env modul true  in
           match uu____4493 with
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
  let uu____4520 = lookup id  in
  match uu____4520 with
  | None  ->
      Prims.raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r 