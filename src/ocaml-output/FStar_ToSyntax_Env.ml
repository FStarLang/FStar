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
let set_iface : env -> Prims.bool -> env =
  fun env  ->
    fun b  ->
      let uu___166_364 = env  in
      {
        curmodule = (uu___166_364.curmodule);
        curmonad = (uu___166_364.curmonad);
        modules = (uu___166_364.modules);
        scope_mods = (uu___166_364.scope_mods);
        exported_ids = (uu___166_364.exported_ids);
        trans_exported_ids = (uu___166_364.trans_exported_ids);
        includes = (uu___166_364.includes);
        sigaccum = (uu___166_364.sigaccum);
        sigmap = (uu___166_364.sigmap);
        iface = b;
        admitted_iface = (uu___166_364.admitted_iface);
        expect_typ = (uu___166_364.expect_typ);
        docs = (uu___166_364.docs)
      }
  
let all_exported_id_kinds : exported_id_kind Prims.list =
  [Exported_id_field; Exported_id_term_type] 
let transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____374 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____374 with
      | None  -> []
      | Some exported_id_set ->
          let uu____378 =
            let uu____379 = exported_id_set Exported_id_term_type  in
            FStar_ST.read uu____379  in
          FStar_All.pipe_right uu____378 FStar_Util.set_elements
  
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
      | None  -> let uu____405 = current_module env  in qual uu____405 id
      | Some monad ->
          let uu____407 =
            let uu____408 = current_module env  in qual uu____408 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____407 id
  
let new_sigmap uu____416 = FStar_Util.smap_create (Prims.parse_int "100") 
let empty_env : Prims.unit -> env =
  fun uu____419  ->
    let uu____420 = new_sigmap ()  in
    let uu____422 = new_sigmap ()  in
    let uu____424 = new_sigmap ()  in
    let uu____430 = new_sigmap ()  in
    let uu____436 = new_sigmap ()  in
    {
      curmodule = None;
      curmonad = None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____420;
      trans_exported_ids = uu____422;
      includes = uu____424;
      sigaccum = [];
      sigmap = uu____430;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____436
    }
  
let sigmap : env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap
  = fun env  -> env.sigmap 
let has_all_in_scope : env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____451  ->
         match uu____451 with
         | (m,uu____455) ->
             FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid) env.modules
  
let set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___167_463 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___167_463.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___168_464 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___168_464.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___168_464.FStar_Syntax_Syntax.sort)
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
        (fun uu____510  ->
           match uu____510 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____524 =
                   let uu____525 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____525 dd dq  in
                 Some uu____524
               else None)
       in
    match t with | Some v1 -> Some (v1, false) | None  -> None
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____555 -> false 
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____579 -> false 
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____590 -> false 
let option_of_cont k_ignore uu___139_609 =
  match uu___139_609 with
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
        (fun uu____654  ->
           match uu____654 with
           | (f,uu____659) ->
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
  fun uu___140_695  ->
    match uu___140_695 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
  
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText  in
  let rec aux uu___141_744 =
    match uu___141_744 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str  in
        let not_shadowed =
          let uu____752 = get_exported_id_set env mname  in
          match uu____752 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____768 = mex eikind  in FStar_ST.read uu____768  in
              FStar_Util.set_mem idstr mexports
           in
        let mincludes =
          let uu____775 = FStar_Util.smap_try_find env.includes mname  in
          match uu____775 with
          | None  -> []
          | Some minc -> FStar_ST.read minc  in
        let look_into =
          if not_shadowed
          then let uu____795 = qual modul id  in find_in_module uu____795
          else Cont_ignore  in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____798 -> look_into)
     in
  aux [ns] 
let is_exported_id_field : exported_id_kind -> Prims.bool =
  fun uu___142_802  ->
    match uu___142_802 with | Exported_id_field  -> true | uu____803 -> false
  
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___143_892 =
    match uu___143_892 with
    | (id',uu____894,uu____895) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText
     in
  let check_rec_binding_id uu___144_899 =
    match uu___144_899 with
    | (id',uu____901,uu____902) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText
     in
  let curmod_ns =
    let uu____905 = current_module env  in FStar_Ident.ids_of_lid uu____905
     in
  let proc uu___145_910 =
    match uu___145_910 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____915) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____918 = FStar_Ident.lid_of_ids curmod_ns  in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident  in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____918 id
    | uu____921 -> Cont_ignore  in
  let rec aux uu___146_927 =
    match uu___146_927 with
    | a::q ->
        let uu____933 = proc a  in
        option_of_cont (fun uu____935  -> aux q) uu____933
    | [] ->
        let uu____936 = lookup_default_id Cont_fail id  in
        option_of_cont (fun uu____938  -> None) uu____936
     in
  aux env.scope_mods 
let found_local_binding r uu____957 =
  match uu____957 with
  | (id',x,mut) -> let uu____964 = bv_to_name x r  in (uu____964, mut) 
let find_in_module env lid k_global_def k_not_found =
  let uu____1001 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
     in
  match uu____1001 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found 
let try_lookup_id :
  env ->
    FStar_Ident.ident -> (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  =
  fun env  ->
    fun id  ->
      let uu____1023 = unmangleOpName id  in
      match uu____1023 with
      | Some f -> Some f
      | uu____1037 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1044 = found_local_binding id.FStar_Ident.idRange r
                  in
               Cont_ok uu____1044) (fun uu____1049  -> Cont_fail)
            (fun uu____1052  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____1059  -> fun uu____1060  -> Cont_fail)
                 Cont_ignore)
            (fun uu____1067  -> fun uu____1068  -> Cont_fail)
  
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1120 ->
        let lid = qualify env id  in
        let uu____1122 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
        (match uu____1122 with
         | Some r -> let uu____1135 = k_global_def lid r  in Some uu____1135
         | None  -> None)
    | None  -> None  in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1148 = current_module env  in qual uu____1148 id
         in
      find_in_module env lid k_global_def k_not_found
  
let module_is_defined : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (match env.curmodule with
       | None  -> false
       | Some m ->
           let uu____1157 = current_module env  in
           FStar_Ident.lid_equals lid uu____1157)
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
        let rec aux uu___147_1181 =
          match uu___147_1181 with
          | [] ->
              let uu____1184 = module_is_defined env lid  in
              if uu____1184 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1191 =
                  let uu____1193 = FStar_Ident.path_of_lid ns  in
                  let uu____1195 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____1193 uu____1195  in
                FStar_Ident.lid_of_path uu____1191
                  (FStar_Ident.range_of_lid lid)
                 in
              let uu____1197 = module_is_defined env new_lid  in
              if uu____1197 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1202 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1206::q -> aux q  in
        aux env.scope_mods
  
let fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> Prims.unit =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____1218 =
          let uu____1219 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____1219  in
        if uu____1218
        then
          (if FStar_Ident.lid_equals ns_resolved FStar_Syntax_Const.prims_lid
           then ()
           else
             (let uu____1221 =
                let uu____1222 =
                  let uu____1225 =
                    FStar_Util.format1
                      "Reference %s to current module is forbidden (see GitHub issue #451)"
                      ns_original.FStar_Ident.str
                     in
                  (uu____1225, (FStar_Ident.range_of_lid ns_original))  in
                FStar_Errors.Error uu____1222  in
              Prims.raise uu____1221))
        else ()
  
let fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> Prims.unit
  =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____1233 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____1236 = resolve_module_name env modul_orig true  in
          (match uu____1236 with
           | Some modul_res -> fail_if_curmodule env modul_orig modul_res
           | uu____1239 -> ())
  
let namespace_is_open : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      FStar_List.existsb
        (fun uu___148_1247  ->
           match uu___148_1247 with
           | Open_module_or_namespace (ns,Open_namespace ) ->
               FStar_Ident.lid_equals lid ns
           | uu____1249 -> false) env.scope_mods
  
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
                 let uu____1304 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____1304
                   (FStar_Util.map_option
                      (fun uu____1328  ->
                         match uu____1328 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id :: rev_kept_ids)))))
           in
        let uu____1345 =
          is_full_path &&
            (let uu____1346 = FStar_Ident.lid_of_ids ids  in
             module_is_defined env uu____1346)
           in
        if uu____1345
        then (ids, [])
        else
          (match FStar_List.rev ids with
           | [] -> ([], [])
           | ns_last_id::ns_rev_prefix ->
               let uu____1363 = aux ns_rev_prefix ns_last_id  in
               (match uu____1363 with
                | None  -> ([], ids)
                | Some (stripped_ids,rev_kept_ids) ->
                    (stripped_ids, (FStar_List.rev rev_kept_ids))))
  
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1476::uu____1477 ->
      let uu____1479 =
        let uu____1481 =
          let uu____1482 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_Ident.set_lid_range uu____1482 (FStar_Ident.range_of_lid lid)
           in
        resolve_module_name env uu____1481 true  in
      (match uu____1479 with
       | None  -> None
       | Some modul ->
           let uu____1485 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident
              in
           option_of_cont (fun uu____1487  -> None) uu____1485)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
  
let cont_of_option k_none uu___149_1502 =
  match uu___149_1502 with | Some v1 -> Cont_ok v1 | None  -> k_none 
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1581 = k_global_def lid1 def  in cont_of_option k uu____1581
     in
  let f_module lid' =
    let k = Cont_ignore  in find_in_module env lid' (k_global_def' k) k  in
  let l_default k i = lookup_default_id env i (k_global_def' k) k  in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1602 = k_local_binding l  in
       cont_of_option Cont_fail uu____1602)
    (fun r  ->
       let uu____1605 = k_rec_binding r  in
       cont_of_option Cont_fail uu____1605) (fun uu____1607  -> Cont_ignore)
    f_module l_default
  
let fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual Prims.option =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1613,uu____1614,uu____1615,l,uu____1617,quals,uu____1619) ->
        let qopt =
          FStar_Util.find_map quals
            (fun uu___150_1626  ->
               match uu___150_1626 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1628,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1635 -> None)
           in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____1639,uu____1640,uu____1641,quals) -> None
    | uu____1645 -> None
  
let lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1654 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____1658 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____1658 then Some fv else None)
         in
      FStar_All.pipe_right uu____1654 FStar_Util.must
  
let ns_of_lid_equals : FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1672 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____1672 ns)
  
let try_lookup_name :
  Prims.bool ->
    Prims.bool -> env -> FStar_Ident.lident -> foundname Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid  in
          let k_global_def source_lid uu___154_1697 =
            match uu___154_1697 with
            | (uu____1701,true ) when exclude_interf -> None
            | (se,uu____1703) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1705 ->
                     let uu____1716 =
                       let uu____1717 =
                         let uu____1720 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None
                            in
                         (uu____1720, false)  in
                       Term_name uu____1717  in
                     Some uu____1716
                 | FStar_Syntax_Syntax.Sig_datacon uu____1721 ->
                     let uu____1731 =
                       let uu____1732 =
                         let uu____1735 =
                           let uu____1736 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1736
                            in
                         (uu____1735, false)  in
                       Term_name uu____1732  in
                     Some uu____1731
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1738,lbs),uu____1740,uu____1741,uu____1742) ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____1755 =
                       let uu____1756 =
                         let uu____1759 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____1759, false)  in
                       Term_name uu____1756  in
                     Some uu____1755
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1761,uu____1762,quals) ->
                     let uu____1766 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___151_1768  ->
                                  match uu___151_1768 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1769 -> false)))
                        in
                     if uu____1766
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid)
                          in
                       let dd =
                         let uu____1773 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___152_1775  ->
                                         match uu___152_1775 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1778 -> false))))
                            in
                         if uu____1773
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let uu____1780 =
                         FStar_Util.find_map quals
                           (fun uu___153_1782  ->
                              match uu___153_1782 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1785 -> None)
                          in
                       (match uu____1780 with
                        | Some refl_monad ->
                            let refl_const =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reflect refl_monad)))
                                None occurrence_range
                               in
                            Some (Term_name (refl_const, false))
                        | uu____1801 ->
                            let uu____1803 =
                              let uu____1804 =
                                let uu____1807 =
                                  let uu____1808 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____1808
                                   in
                                (uu____1807, false)  in
                              Term_name uu____1804  in
                            Some uu____1803)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1812 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1821 -> None)
             in
          let k_local_binding r =
            let uu____1833 =
              let uu____1834 =
                found_local_binding (FStar_Ident.range_of_lid lid) r  in
              Term_name uu____1834  in
            Some uu____1833  in
          let k_rec_binding uu____1844 =
            match uu____1844 with
            | (id,l,dd) ->
                let uu____1852 =
                  let uu____1853 =
                    let uu____1856 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None
                       in
                    (uu____1856, false)  in
                  Term_name uu____1853  in
                Some uu____1852
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____1860 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____1860 with
                 | Some f -> Some (Term_name f)
                 | uu____1870 -> None)
            | uu____1874 -> None  in
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
        let uu____1894 = try_lookup_name true exclude_interf env lid  in
        match uu____1894 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____1903 -> None
  
let try_lookup_effect_name :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1914 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1914 with | Some (o,l1) -> Some l1 | uu____1923 -> None
  
let try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)
        Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____1937 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1937 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____1946;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____1955;_},l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____1963,uu____1964,uu____1965,uu____1966,uu____1967,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____1969;_},l1)
          -> Some (l1, cattributes)
      | uu____1981 -> None
  
let try_lookup_effect_defn :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      let uu____1995 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1995 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____2001;_},uu____2002)
          -> Some ne
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_new_effect_for_free ne;
             FStar_Syntax_Syntax.sigrng = uu____2006;_},uu____2007)
          -> Some ne
      | uu____2010 -> None
  
let is_effect_name : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____2020 = try_lookup_effect_name env lid  in
      match uu____2020 with | None  -> false | Some uu____2022 -> true
  
let try_lookup_root_effect_name :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2030 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____2030 with
      | Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____2036,uu____2037,uu____2038,uu____2039,uu____2040);
             FStar_Syntax_Syntax.sigrng = uu____2041;_},uu____2042)
          ->
          let rec aux new_name =
            let uu____2054 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____2054 with
            | None  -> None
            | Some (s,uu____2064) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free ne
                   |FStar_Syntax_Syntax.Sig_new_effect ne ->
                     Some
                       (FStar_Ident.set_lid_range
                          ne.FStar_Syntax_Syntax.mname
                          (FStar_Ident.range_of_lid l))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____2069,uu____2070,uu____2071,cmp,uu____2073,uu____2074)
                     ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____2080 -> None)
             in
          aux l'
      | Some (uu____2081,l') -> Some l'
      | uu____2085 -> None
  
let lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___155_2106 =
        match uu___155_2106 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (lid2,uu____2112,uu____2113,quals);
             FStar_Syntax_Syntax.sigrng = uu____2115;_},uu____2116)
            -> Some quals
        | uu____2120 -> None  in
      let uu____2124 =
        resolve_in_open_namespaces' env lid (fun uu____2128  -> None)
          (fun uu____2130  -> None) k_global_def
         in
      match uu____2124 with | Some quals -> quals | uu____2136 -> []
  
let try_lookup_module :
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul Prims.option =
  fun env  ->
    fun path  ->
      let uu____2148 =
        FStar_List.tryFind
          (fun uu____2154  ->
             match uu____2154 with
             | (mlid,modul) ->
                 let uu____2159 = FStar_Ident.path_of_lid mlid  in
                 uu____2159 = path) env.modules
         in
      match uu____2148 with
      | Some (uu____2163,modul) -> Some modul
      | None  -> None
  
let try_lookup_let :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___156_2185 =
        match uu___156_2185 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____2189,lbs),uu____2191,uu____2192,uu____2193);
             FStar_Syntax_Syntax.sigrng = uu____2194;_},uu____2195)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____2208 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            Some uu____2208
        | uu____2209 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2212  -> None)
        (fun uu____2213  -> None) k_global_def
  
let try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___157_2232 =
        match uu___157_2232 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____2239,uu____2240,uu____2241);
             FStar_Syntax_Syntax.sigrng = uu____2242;_},uu____2243)
            ->
            FStar_Util.find_map (Prims.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____2260 -> None)
        | uu____2265 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2272  -> None)
        (fun uu____2275  -> None) k_global_def
  
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
          let uu____2302 = try_lookup_name any_val exclude_interf env lid  in
          match uu____2302 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2311 -> None
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l 
let resolve_to_fully_qualified_name :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____2331 = try_lookup_lid env l  in
      match uu____2331 with
      | None  -> None
      | Some (e,uu____2339) ->
          let uu____2342 =
            let uu____2343 = FStar_Syntax_Subst.compress e  in
            uu____2343.FStar_Syntax_Syntax.n  in
          (match uu____2342 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               Some ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____2352 -> None)
  
let try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___169_2363 = env  in
        {
          curmodule = (uu___169_2363.curmodule);
          curmonad = (uu___169_2363.curmonad);
          modules = (uu___169_2363.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___169_2363.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___169_2363.sigaccum);
          sigmap = (uu___169_2363.sigmap);
          iface = (uu___169_2363.iface);
          admitted_iface = (uu___169_2363.admitted_iface);
          expect_typ = (uu___169_2363.expect_typ);
          docs = (uu___169_2363.docs)
        }  in
      try_lookup_lid env' l
  
let try_lookup_doc :
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option =
  fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str 
let try_lookup_datacon :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___159_2387 =
        match uu___159_2387 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____2391,uu____2392,uu____2393,quals);
             FStar_Syntax_Syntax.sigrng = uu____2395;_},uu____2396)
            ->
            let uu____2399 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___158_2401  ->
                      match uu___158_2401 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2402 -> false))
               in
            if uu____2399
            then
              let uu____2404 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None
                 in
              Some uu____2404
            else None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____2406;
             FStar_Syntax_Syntax.sigrng = uu____2407;_},uu____2408)
            ->
            let uu____2418 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor)
               in
            Some uu____2418
        | uu____2419 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2422  -> None)
        (fun uu____2423  -> None) k_global_def
  
let find_all_datacons :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___160_2442 =
        match uu___160_2442 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____2447,uu____2448,uu____2449,uu____2450,uu____2451,datas,uu____2453);
             FStar_Syntax_Syntax.sigrng = uu____2454;_},uu____2455)
            -> Some datas
        | uu____2463 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2468  -> None)
        (fun uu____2470  -> None) k_global_def
  
let record_cache_aux_with_filter :
  (((Prims.unit -> Prims.unit) * (Prims.unit -> Prims.unit) *
    (Prims.unit -> record_or_dc Prims.list) * (record_or_dc -> Prims.unit) *
    (Prims.unit -> Prims.unit)) * (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____2504 =
    let uu____2505 =
      let uu____2508 =
        let uu____2510 = FStar_ST.read record_cache  in
        FStar_List.hd uu____2510  in
      let uu____2518 = FStar_ST.read record_cache  in uu____2508 ::
        uu____2518
       in
    FStar_ST.write record_cache uu____2505  in
  let pop1 uu____2533 =
    let uu____2534 =
      let uu____2537 = FStar_ST.read record_cache  in
      FStar_List.tl uu____2537  in
    FStar_ST.write record_cache uu____2534  in
  let peek uu____2553 =
    let uu____2554 = FStar_ST.read record_cache  in FStar_List.hd uu____2554
     in
  let insert r =
    let uu____2566 =
      let uu____2569 = let uu____2571 = peek ()  in r :: uu____2571  in
      let uu____2573 =
        let uu____2576 = FStar_ST.read record_cache  in
        FStar_List.tl uu____2576  in
      uu____2569 :: uu____2573  in
    FStar_ST.write record_cache uu____2566  in
  let commit1 uu____2592 =
    let uu____2593 = FStar_ST.read record_cache  in
    match uu____2593 with
    | hd1::uu____2601::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2614 -> failwith "Impossible"  in
  let filter1 uu____2620 =
    let rc = peek ()  in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
            in
         let uu____2627 =
           let uu____2630 = FStar_ST.read record_cache  in filtered ::
             uu____2630
            in
         FStar_ST.write record_cache uu____2627)
     in
  let aux = (push1, pop1, peek, insert, commit1)  in (aux, filter1) 
let record_cache_aux :
  ((Prims.unit -> Prims.unit) * (Prims.unit -> Prims.unit) *
    (Prims.unit -> record_or_dc Prims.list) * (record_or_dc -> Prims.unit) *
    (Prims.unit -> Prims.unit))
  =
  let uu____2704 = record_cache_aux_with_filter  in
  match uu____2704 with | (aux,uu____2742) -> aux 
let filter_record_cache : Prims.unit -> Prims.unit =
  let uu____2781 = record_cache_aux_with_filter  in
  match uu____2781 with | (uu____2804,filter1) -> filter1 
let push_record_cache : Prims.unit -> Prims.unit =
  let uu____2844 = record_cache_aux  in
  match uu____2844 with
  | (push1,uu____2864,uu____2865,uu____2866,uu____2867) -> push1 
let pop_record_cache : Prims.unit -> Prims.unit =
  let uu____2892 = record_cache_aux  in
  match uu____2892 with
  | (uu____2911,pop1,uu____2913,uu____2914,uu____2915) -> pop1 
let peek_record_cache : Prims.unit -> record_or_dc Prims.list =
  let uu____2941 = record_cache_aux  in
  match uu____2941 with
  | (uu____2961,uu____2962,peek,uu____2964,uu____2965) -> peek 
let insert_record_cache : record_or_dc -> Prims.unit =
  let uu____2990 = record_cache_aux  in
  match uu____2990 with
  | (uu____3009,uu____3010,uu____3011,insert,uu____3013) -> insert 
let commit_record_cache : Prims.unit -> Prims.unit =
  let uu____3038 = record_cache_aux  in
  match uu____3038 with
  | (uu____3057,uu____3058,uu____3059,uu____3060,commit1) -> commit1 
let extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____3100,uu____3101) ->
            let is_rec =
              FStar_Util.for_some
                (fun uu___161_3112  ->
                   match uu___161_3112 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____3115 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___162_3123  ->
                      match uu___162_3123 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____3125,uu____3126,uu____3127,uu____3128,uu____3129,uu____3130);
                          FStar_Syntax_Syntax.sigrng = uu____3131;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____3136 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___163_3138  ->
                    match uu___163_3138 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs,parms,uu____3142,uu____3143,dc::[],tags);
                        FStar_Syntax_Syntax.sigrng = uu____3146;_} ->
                        let uu____3152 =
                          let uu____3153 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____3153  in
                        (match uu____3152 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____3157,t,uu____3159,uu____3160,uu____3161,uu____3162);
                             FStar_Syntax_Syntax.sigrng = uu____3163;_} ->
                             let uu____3168 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____3168 with
                              | (formals,uu____3177) ->
                                  let is_rec1 = is_rec tags  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____3203  ->
                                            match uu____3203 with
                                            | (x,q) ->
                                                let uu____3211 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec1 &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____3211
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____3242  ->
                                            match uu____3242 with
                                            | (x,q) ->
                                                let uu____3251 =
                                                  if is_rec1
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____3251,
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
                                  ((let uu____3263 =
                                      let uu____3265 =
                                        FStar_ST.read new_globs  in
                                      (Record_or_dc record) :: uu____3265  in
                                    FStar_ST.write new_globs uu____3263);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____3281 =
                                            match uu____3281 with
                                            | (id,uu____3287) ->
                                                let modul =
                                                  let uu____3293 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____3293.FStar_Ident.str
                                                   in
                                                let uu____3294 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____3294 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____3310 =
                                                         let uu____3311 =
                                                           FStar_ST.read
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____3311
                                                          in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____3310);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____3318 =
                                                               let uu____3319
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id
                                                                  in
                                                               uu____3319.FStar_Ident.ident
                                                                in
                                                             uu____3318.FStar_Ident.idText
                                                              in
                                                           let uu____3321 =
                                                             let uu____3322 =
                                                               FStar_ST.read
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____3322
                                                              in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____3321))
                                                 | None  -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____3335 -> ())
                    | uu____3336 -> ()))
        | uu____3337 -> ()
  
let try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3350 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____3350 with
        | (ns,id) ->
            let uu____3360 = peek_record_cache ()  in
            FStar_Util.find_map uu____3360
              (fun record  ->
                 let uu____3363 =
                   find_in_record ns id record (fun r  -> Cont_ok r)  in
                 option_of_cont (fun uu____3366  -> None) uu____3363)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3367  -> Cont_ignore) (fun uu____3368  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3371 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____3371)
        (fun k  -> fun uu____3374  -> k)
  
let try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let uu____3383 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____3383 with
      | Some r when r.is_record -> Some r
      | uu____3387 -> None
  
let belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3398 = try_lookup_record_by_field_name env lid  in
        match uu____3398 with
        | Some record' when
            let uu____3401 =
              let uu____3402 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____3402  in
            let uu____3404 =
              let uu____3405 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____3405  in
            uu____3401 = uu____3404 ->
            let uu____3407 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3409  -> Cont_ok ())
               in
            (match uu____3407 with
             | Cont_ok uu____3410 -> true
             | uu____3411 -> false)
        | uu____3413 -> false
  
let try_lookup_dc_by_field_name :
  env -> FStar_Ident.lident -> (FStar_Ident.lident * Prims.bool) Prims.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____3424 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____3424 with
      | Some r ->
          let uu____3430 =
            let uu____3433 =
              let uu____3434 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              FStar_Ident.set_lid_range uu____3434
                (FStar_Ident.range_of_lid fieldname)
               in
            (uu____3433, (r.is_record))  in
          Some uu____3430
      | uu____3437 -> None
  
let string_set_ref_new :
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3446  ->
    let uu____3447 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode  in
    FStar_Util.mk_ref uu____3447
  
let exported_id_set_new :
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3458  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___164_3467  ->
      match uu___164_3467 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___165_3487 =
            match uu___165_3487 with
            | Rec_binding uu____3488 -> true
            | uu____3489 -> false  in
          let this_env =
            let uu___170_3491 = env  in
            let uu____3492 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___170_3491.curmodule);
              curmonad = (uu___170_3491.curmonad);
              modules = (uu___170_3491.modules);
              scope_mods = uu____3492;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___170_3491.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___170_3491.sigaccum);
              sigmap = (uu___170_3491.sigmap);
              iface = (uu___170_3491.iface);
              admitted_iface = (uu___170_3491.admitted_iface);
              expect_typ = (uu___170_3491.expect_typ);
              docs = (uu___170_3491.docs)
            }  in
          let uu____3494 = try_lookup_lid' any_val exclude_if this_env lid
             in
          match uu____3494 with | None  -> true | Some uu____3500 -> false
  
let push_scope_mod : env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___171_3511 = env  in
      {
        curmodule = (uu___171_3511.curmodule);
        curmonad = (uu___171_3511.curmonad);
        modules = (uu___171_3511.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___171_3511.exported_ids);
        trans_exported_ids = (uu___171_3511.trans_exported_ids);
        includes = (uu___171_3511.includes);
        sigaccum = (uu___171_3511.sigaccum);
        sigmap = (uu___171_3511.sigmap);
        iface = (uu___171_3511.iface);
        admitted_iface = (uu___171_3511.admitted_iface);
        expect_typ = (uu___171_3511.expect_typ);
        docs = (uu___171_3511.docs)
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
        let uu____3550 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____3550
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
          | Some (se,uu____3570) ->
              let uu____3573 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____3573 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>"  in
        let uu____3578 =
          let uu____3579 =
            let uu____3582 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r
               in
            (uu____3582, (FStar_Ident.range_of_lid l))  in
          FStar_Errors.Error uu____3579  in
        Prims.raise uu____3578  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____3589 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let uu____3594 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3602 -> (true, true)
          | uu____3609 -> (false, false)  in
        match uu____3589 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____3614 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3617 =
                     let uu____3618 = unique any_val exclude_if env l  in
                     Prims.op_Negation uu____3618  in
                   if uu____3617 then Some l else None)
               in
            (match uu____3614 with
             | Some l when
                 let uu____3622 = FStar_Options.interactive ()  in
                 Prims.op_Negation uu____3622 -> err l
             | uu____3623 ->
                 (extract_record env globals s;
                  (let uu___172_3628 = env  in
                   {
                     curmodule = (uu___172_3628.curmodule);
                     curmonad = (uu___172_3628.curmonad);
                     modules = (uu___172_3628.modules);
                     scope_mods = (uu___172_3628.scope_mods);
                     exported_ids = (uu___172_3628.exported_ids);
                     trans_exported_ids = (uu___172_3628.trans_exported_ids);
                     includes = (uu___172_3628.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___172_3628.sigmap);
                     iface = (uu___172_3628.iface);
                     admitted_iface = (uu___172_3628.admitted_iface);
                     expect_typ = (uu___172_3628.expect_typ);
                     docs = (uu___172_3628.docs)
                   })))
         in
      let env2 =
        let uu___173_3630 = env1  in
        let uu____3631 = FStar_ST.read globals  in
        {
          curmodule = (uu___173_3630.curmodule);
          curmonad = (uu___173_3630.curmonad);
          modules = (uu___173_3630.modules);
          scope_mods = uu____3631;
          exported_ids = (uu___173_3630.exported_ids);
          trans_exported_ids = (uu___173_3630.trans_exported_ids);
          includes = (uu___173_3630.includes);
          sigaccum = (uu___173_3630.sigaccum);
          sigmap = (uu___173_3630.sigmap);
          iface = (uu___173_3630.iface);
          admitted_iface = (uu___173_3630.admitted_iface);
          expect_typ = (uu___173_3630.expect_typ);
          docs = (uu___173_3630.docs)
        }  in
      let uu____3636 =
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____3650,uu____3651) ->
            let uu____3658 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____3658)
        | uu____3672 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____3636 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3702  ->
                   match uu____3702 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3713 =
                                  let uu____3715 = FStar_ST.read globals  in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3715
                                   in
                                FStar_ST.write globals uu____3713);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3724 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____3724.FStar_Ident.str  in
                                    ((let uu____3726 =
                                        get_exported_id_set env3 modul  in
                                      match uu____3726 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____3741 =
                                            let uu____3742 =
                                              FStar_ST.read my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3742
                                             in
                                          FStar_ST.write my_exported_ids
                                            uu____3741
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
              let uu___174_3754 = env3  in
              let uu____3755 = FStar_ST.read globals  in
              {
                curmodule = (uu___174_3754.curmodule);
                curmonad = (uu___174_3754.curmonad);
                modules = (uu___174_3754.modules);
                scope_mods = uu____3755;
                exported_ids = (uu___174_3754.exported_ids);
                trans_exported_ids = (uu___174_3754.trans_exported_ids);
                includes = (uu___174_3754.includes);
                sigaccum = (uu___174_3754.sigaccum);
                sigmap = (uu___174_3754.sigmap);
                iface = (uu___174_3754.iface);
                admitted_iface = (uu___174_3754.admitted_iface);
                expect_typ = (uu___174_3754.expect_typ);
                docs = (uu___174_3754.docs)
              }  in
            env4))
  
let push_namespace : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3766 =
        let uu____3769 = resolve_module_name env ns false  in
        match uu____3769 with
        | None  ->
            let modules = env.modules  in
            let uu____3777 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3783  ->
                      match uu____3783 with
                      | (m,uu____3787) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) ".")))
               in
            if uu____3777
            then (ns, Open_namespace)
            else
              (let uu____3791 =
                 let uu____3792 =
                   let uu____3795 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns)
                      in
                   (uu____3795, (FStar_Ident.range_of_lid ns))  in
                 FStar_Errors.Error uu____3792  in
               Prims.raise uu____3791)
        | Some ns' -> (fail_if_curmodule env ns ns'; (ns', Open_module))  in
      match uu____3766 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
  
let push_include : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____3809 = resolve_module_name env ns false  in
      match uu____3809 with
      | Some ns1 ->
          (fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____3815 = current_module env1  in
              uu____3815.FStar_Ident.str  in
            (let uu____3817 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____3817 with
             | None  -> ()
             | Some incl ->
                 let uu____3830 =
                   let uu____3832 = FStar_ST.read incl  in ns1 :: uu____3832
                    in
                 FStar_ST.write incl uu____3830);
            (match () with
             | () ->
                 let uu____3840 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____3840 with
                  | Some ns_trans_exports ->
                      ((let uu____3853 =
                          let uu____3864 = get_exported_id_set env1 curmod
                             in
                          let uu____3869 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____3864, uu____3869)  in
                        match uu____3853 with
                        | (Some cur_exports,Some cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____3909 = ns_trans_exports k  in
                                FStar_ST.read uu____3909  in
                              let ex = cur_exports k  in
                              (let uu____3918 =
                                 let uu____3919 = FStar_ST.read ex  in
                                 FStar_Util.set_difference uu____3919 ns_ex
                                  in
                               FStar_ST.write ex uu____3918);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____3929 =
                                     let uu____3930 = FStar_ST.read trans_ex
                                        in
                                     FStar_Util.set_union uu____3930 ns_ex
                                      in
                                   FStar_ST.write trans_ex uu____3929)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____3936 -> ());
                       (match () with | () -> env1))
                  | None  ->
                      let uu____3950 =
                        let uu____3951 =
                          let uu____3954 =
                            FStar_Util.format1
                              "include: Module %s was not prepared"
                              ns1.FStar_Ident.str
                             in
                          (uu____3954, (FStar_Ident.range_of_lid ns1))  in
                        FStar_Errors.Error uu____3951  in
                      Prims.raise uu____3950))))
      | uu____3955 ->
          let uu____3957 =
            let uu____3958 =
              let uu____3961 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str
                 in
              (uu____3961, (FStar_Ident.range_of_lid ns))  in
            FStar_Errors.Error uu____3958  in
          Prims.raise uu____3957
  
let push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____3971 = module_is_defined env l  in
        if uu____3971
        then
          (fail_if_curmodule env l l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____3974 =
             let uu____3975 =
               let uu____3978 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l)
                  in
               (uu____3978, (FStar_Ident.range_of_lid l))  in
             FStar_Errors.Error uu____3975  in
           Prims.raise uu____3974)
  
let push_doc :
  env -> FStar_Ident.lid -> FStar_Parser_AST.fsdoc Prims.option -> env =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | None  -> env
        | Some doc1 ->
            ((let uu____3992 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____3992 with
              | None  -> ()
              | Some old_doc ->
                  let uu____3995 =
                    let uu____3996 = FStar_Ident.string_of_lid l  in
                    let uu____3997 = FStar_Parser_AST.string_of_fsdoc old_doc
                       in
                    let uu____3998 = FStar_Parser_AST.string_of_fsdoc doc1
                       in
                    FStar_Util.format3
                      "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                      uu____3996 uu____3997 uu____3998
                     in
                  FStar_Errors.warn (FStar_Ident.range_of_lid l) uu____3995);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
  
let check_admits : env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,quals) ->
                let uu____4010 = try_lookup_lid env l  in
                (match uu____4010 with
                 | None  ->
                     ((let uu____4017 =
                         let uu____4018 = FStar_Options.interactive ()  in
                         Prims.op_Negation uu____4018  in
                       if uu____4017
                       then
                         let uu____4019 =
                           let uu____4020 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l)
                              in
                           let uu____4021 =
                             FStar_Syntax_Print.lid_to_string l  in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____4020 uu____4021
                            in
                         FStar_Util.print_string uu____4019
                       else ());
                      FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                        ((let uu___175_4025 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_declare_typ
                                 (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                                   quals)));
                            FStar_Syntax_Syntax.sigrng =
                              (uu___175_4025.FStar_Syntax_Syntax.sigrng)
                          }), false))
                 | Some uu____4027 -> ())
            | uu____4032 -> ()))
  
let finish : env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4043) ->
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
                                (lid,uu____4053,uu____4054,uu____4055,uu____4056,uu____4057,uu____4058)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____4065 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____4068,uu____4069,quals) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____4076,lbs),uu____4078,quals,uu____4080) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____4095 =
                               let uu____4096 =
                                 let uu____4097 =
                                   let uu____4102 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____4102.FStar_Syntax_Syntax.fv_name  in
                                 uu____4097.FStar_Syntax_Syntax.v  in
                               uu____4096.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____4095))
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
                               let uu____4112 =
                                 let uu____4117 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____4117.FStar_Syntax_Syntax.fv_name  in
                               uu____4112.FStar_Syntax_Syntax.v  in
                             let decl =
                               let uu___176_4122 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp),
                                        (FStar_Syntax_Syntax.Assumption ::
                                        quals)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___176_4122.FStar_Syntax_Syntax.sigrng)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____4130 -> ()));
      (let curmod =
         let uu____4132 = current_module env  in uu____4132.FStar_Ident.str
          in
       (let uu____4134 =
          let uu____4145 = get_exported_id_set env curmod  in
          let uu____4150 = get_trans_exported_id_set env curmod  in
          (uu____4145, uu____4150)  in
        match uu____4134 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____4190 = cur_ex eikind  in FStar_ST.read uu____4190
                 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____4198 =
                let uu____4199 = FStar_ST.read cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____4199  in
              FStar_ST.write cur_trans_ex_set_ref uu____4198  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____4205 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___177_4217 = env  in
                  {
                    curmodule = None;
                    curmonad = (uu___177_4217.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___177_4217.exported_ids);
                    trans_exported_ids = (uu___177_4217.trans_exported_ids);
                    includes = (uu___177_4217.includes);
                    sigaccum = [];
                    sigmap = (uu___177_4217.sigmap);
                    iface = (uu___177_4217.iface);
                    admitted_iface = (uu___177_4217.admitted_iface);
                    expect_typ = (uu___177_4217.expect_typ);
                    docs = (uu___177_4217.docs)
                  }))))
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push : env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____4230 =
       let uu____4232 = FStar_ST.read stack  in env :: uu____4232  in
     FStar_ST.write stack uu____4230);
    (let uu___178_4240 = env  in
     let uu____4241 = FStar_Util.smap_copy (sigmap env)  in
     let uu____4247 = FStar_Util.smap_copy env.docs  in
     {
       curmodule = (uu___178_4240.curmodule);
       curmonad = (uu___178_4240.curmonad);
       modules = (uu___178_4240.modules);
       scope_mods = (uu___178_4240.scope_mods);
       exported_ids = (uu___178_4240.exported_ids);
       trans_exported_ids = (uu___178_4240.trans_exported_ids);
       includes = (uu___178_4240.includes);
       sigaccum = (uu___178_4240.sigaccum);
       sigmap = uu____4241;
       iface = (uu___178_4240.iface);
       admitted_iface = (uu___178_4240.admitted_iface);
       expect_typ = (uu___178_4240.expect_typ);
       docs = uu____4247
     })
  
let pop : Prims.unit -> env =
  fun uu____4251  ->
    let uu____4252 = FStar_ST.read stack  in
    match uu____4252 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____4265 -> failwith "Impossible: Too many pops"
  
let commit_mark : env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____4271 = FStar_ST.read stack  in
     match uu____4271 with
     | uu____4276::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____4283 -> failwith "Impossible: Too many pops")
  
let mark : env -> env = fun x  -> push x 
let reset_mark : Prims.unit -> env = fun uu____4290  -> pop () 
let export_interface : FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____4302 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____4304 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____4322 = FStar_Util.smap_try_find sm' k  in
              match uu____4322 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,q) ->
                          let uu___179_4341 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_declare_typ
                                 (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                                   q)));
                            FStar_Syntax_Syntax.sigrng =
                              (uu___179_4341.FStar_Syntax_Syntax.sigrng)
                          }
                      | uu____4343 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____4346 -> ()));
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
            (let uu____4390 = exported_id_set_new ()  in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4390);
            (match () with
             | () ->
                 ((let uu____4395 = exported_id_set_new ()  in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4395);
                  (match () with
                   | () ->
                       ((let uu____4400 = FStar_Util.mk_ref []  in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4400);
                        (match () with
                         | () ->
                             let uu___180_4409 = env1  in
                             let uu____4410 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1
                                in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___180_4409.curmonad);
                               modules = (uu___180_4409.modules);
                               scope_mods = uu____4410;
                               exported_ids = (uu___180_4409.exported_ids);
                               trans_exported_ids =
                                 (uu___180_4409.trans_exported_ids);
                               includes = (uu___180_4409.includes);
                               sigaccum = (uu___180_4409.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___180_4409.expect_typ);
                               docs = (uu___180_4409.docs)
                             })))))
             in
          let uu____4413 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4425  ->
                    match uu____4425 with
                    | (l,uu____4429) -> FStar_Ident.lid_equals l mname))
             in
          match uu____4413 with
          | None  -> let uu____4434 = prep env  in (uu____4434, false)
          | Some (uu____4435,m) ->
              ((let uu____4440 =
                  (let uu____4441 = FStar_Options.interactive ()  in
                   Prims.op_Negation uu____4441) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf)
                   in
                if uu____4440
                then
                  let uu____4442 =
                    let uu____4443 =
                      let uu____4446 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (uu____4446, (FStar_Ident.range_of_lid mname))  in
                    FStar_Errors.Error uu____4443  in
                  Prims.raise uu____4442
                else ());
               (let uu____4448 =
                  let uu____4449 = push env  in prep uu____4449  in
                (uu____4448, true)))
  
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
          let uu___181_4457 = env  in
          {
            curmodule = (uu___181_4457.curmodule);
            curmonad = (Some mname);
            modules = (uu___181_4457.modules);
            scope_mods = (uu___181_4457.scope_mods);
            exported_ids = (uu___181_4457.exported_ids);
            trans_exported_ids = (uu___181_4457.trans_exported_ids);
            includes = (uu___181_4457.includes);
            sigaccum = (uu___181_4457.sigaccum);
            sigmap = (uu___181_4457.sigmap);
            iface = (uu___181_4457.iface);
            admitted_iface = (uu___181_4457.admitted_iface);
            expect_typ = (uu___181_4457.expect_typ);
            docs = (uu___181_4457.docs)
          }
  
let fail_or env lookup lid =
  let uu____4482 = lookup lid  in
  match uu____4482 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4488  ->
             match uu____4488 with
             | (lid1,uu____4492) -> FStar_Ident.text_of_lid lid1) env.modules
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
             let uu____4499 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
             FStar_Ident.set_lid_range uu____4499
               (FStar_Ident.range_of_lid lid)
              in
           let uu____4500 = resolve_module_name env modul true  in
           match uu____4500 with
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
  let uu____4527 = lookup id  in
  match uu____4527 with
  | None  ->
      Prims.raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r 