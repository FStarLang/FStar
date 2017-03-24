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
      | None  -> let uu____369 = current_module env  in qual uu____369 id
      | Some monad ->
          let uu____371 =
            let uu____372 = current_module env  in qual uu____372 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____371 id
  
let new_sigmap uu____380 = FStar_Util.smap_create (Prims.parse_int "100") 
let empty_env : Prims.unit -> env =
  fun uu____383  ->
    let uu____384 = new_sigmap ()  in
    let uu____386 = new_sigmap ()  in
    let uu____388 = new_sigmap ()  in
    let uu____394 = new_sigmap ()  in
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
  
let sigmap : env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap
  = fun env  -> env.sigmap 
let has_all_in_scope : env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____413  ->
         match uu____413 with
         | (m,uu____417) ->
             FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid) env.modules
  
let set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___171_425 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___171_425.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___172_426 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___172_426.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___172_426.FStar_Syntax_Syntax.sort)
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
        (fun uu____472  ->
           match uu____472 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 let uu____486 =
                   let uu____487 =
                     FStar_Ident.lid_of_path ["Prims"; y]
                       id.FStar_Ident.idRange
                      in
                   FStar_Syntax_Syntax.fvar uu____487 dd dq  in
                 Some uu____486
               else None)
       in
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
let option_of_cont k_ignore uu___141_571 =
  match uu___141_571 with
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
        (fun uu____616  ->
           match uu____616 with
           | (f,uu____621) ->
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
  fun uu___142_657  ->
    match uu___142_657 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
  
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText  in
  let rec aux uu___143_706 =
    match uu___143_706 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str  in
        let not_shadowed =
          let uu____714 = get_exported_id_set env mname  in
          match uu____714 with
          | None  -> true
          | Some mex ->
              let mexports =
                let uu____730 = mex eikind  in FStar_ST.read uu____730  in
              FStar_Util.set_mem idstr mexports
           in
        let mincludes =
          let uu____737 = FStar_Util.smap_try_find env.includes mname  in
          match uu____737 with
          | None  -> []
          | Some minc -> FStar_ST.read minc  in
        let look_into =
          if not_shadowed
          then let uu____757 = qual modul id  in find_in_module uu____757
          else Cont_ignore  in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____760 -> look_into)
     in
  aux [ns] 
let is_exported_id_field : exported_id_kind -> Prims.bool =
  fun uu___144_764  ->
    match uu___144_764 with | Exported_id_field  -> true | uu____765 -> false
  
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___145_854 =
    match uu___145_854 with
    | (id',uu____856,uu____857) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText
     in
  let check_rec_binding_id uu___146_861 =
    match uu___146_861 with
    | (id',uu____863,uu____864) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText
     in
  let curmod_ns =
    let uu____867 = current_module env  in FStar_Ident.ids_of_lid uu____867
     in
  let proc uu___147_872 =
    match uu___147_872 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____877) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let uu____880 = FStar_Ident.lid_of_ids curmod_ns  in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id1 = lid.FStar_Ident.ident  in
             find_in_record lid.FStar_Ident.ns id1 r k_record) Cont_ignore
          env uu____880 id
    | uu____883 -> Cont_ignore  in
  let rec aux uu___148_889 =
    match uu___148_889 with
    | a::q ->
        let uu____895 = proc a  in
        option_of_cont (fun uu____897  -> aux q) uu____895
    | [] ->
        let uu____898 = lookup_default_id Cont_fail id  in
        option_of_cont (fun uu____900  -> None) uu____898
     in
  aux env.scope_mods 
let found_local_binding r uu____919 =
  match uu____919 with
  | (id',x,mut) -> let uu____926 = bv_to_name x r  in (uu____926, mut) 
let find_in_module env lid k_global_def k_not_found =
  let uu____963 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
     in
  match uu____963 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found 
let try_lookup_id :
  env ->
    FStar_Ident.ident -> (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  =
  fun env  ->
    fun id  ->
      let uu____985 = unmangleOpName id  in
      match uu____985 with
      | Some f -> Some f
      | uu____999 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  ->
               let uu____1006 = found_local_binding id.FStar_Ident.idRange r
                  in
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
        let lid = qualify env id  in
        let uu____1084 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
        (match uu____1084 with
         | Some r -> let uu____1097 = k_global_def lid r  in Some uu____1097
         | None  -> None)
    | None  -> None  in
  match find_in_monad with
  | Some v1 -> v1
  | None  ->
      let lid = let uu____1110 = current_module env  in qual uu____1110 id
         in
      find_in_module env lid k_global_def k_not_found
  
let module_is_defined : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (let uu____1118 = current_module env  in
       FStar_Ident.lid_equals lid uu____1118) ||
        (FStar_List.existsb
           (fun x  -> FStar_Ident.lid_equals lid (Prims.fst x)) env.modules)
  
let resolve_module_name :
  env -> FStar_Ident.lident -> Prims.bool -> FStar_Ident.lident Prims.option
  =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns  in
        let rec aux uu___149_1142 =
          match uu___149_1142 with
          | [] ->
              let uu____1145 = module_is_defined env lid  in
              if uu____1145 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____1152 =
                  let uu____1154 = FStar_Ident.path_of_lid ns  in
                  let uu____1156 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____1154 uu____1156  in
                FStar_Ident.lid_of_path uu____1152
                  (FStar_Ident.range_of_lid lid)
                 in
              let uu____1158 = module_is_defined env new_lid  in
              if uu____1158 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1163 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1167::q -> aux q  in
        aux env.scope_mods
  
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1255::uu____1256 ->
      let uu____1258 =
        let uu____1260 =
          let uu____1261 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_Ident.set_lid_range uu____1261 (FStar_Ident.range_of_lid lid)
           in
        resolve_module_name env uu____1260 true  in
      (match uu____1258 with
       | None  -> None
       | Some modul ->
           let uu____1264 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident
              in
           option_of_cont (fun uu____1266  -> None) uu____1264)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
  
let cont_of_option k_none uu___150_1281 =
  match uu___150_1281 with | Some v1 -> Cont_ok v1 | None  -> k_none 
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid1 def =
    let uu____1360 = k_global_def lid1 def  in cont_of_option k uu____1360
     in
  let f_module lid' =
    let k = Cont_ignore  in find_in_module env lid' (k_global_def' k) k  in
  let l_default k i = lookup_default_id env i (k_global_def' k) k  in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let uu____1381 = k_local_binding l  in
       cont_of_option Cont_fail uu____1381)
    (fun r  ->
       let uu____1384 = k_rec_binding r  in
       cont_of_option Cont_fail uu____1384) (fun uu____1386  -> Cont_ignore)
    f_module l_default
  
let fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual Prims.option =
  fun uu___152_1390  ->
    match uu___152_1390 with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1392,uu____1393,uu____1394,l,uu____1396,quals,uu____1398,uu____1399)
        ->
        let qopt =
          FStar_Util.find_map quals
            (fun uu___151_1406  ->
               match uu___151_1406 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1408,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1415 -> None)
           in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____1419,uu____1420,uu____1421,quals,uu____1423) -> None
    | uu____1426 -> None
  
let lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let uu____1435 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____1439 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____1439 then Some fv else None)
         in
      FStar_All.pipe_right uu____1435 FStar_Util.must
  
let ns_of_lid_equals : FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let uu____1453 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____1453 ns)
  
let try_lookup_name :
  Prims.bool ->
    Prims.bool -> env -> FStar_Ident.lident -> foundname Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid  in
          let k_global_def source_lid uu___156_1478 =
            match uu___156_1478 with
            | (uu____1482,true ) when exclude_interf -> None
            | (se,uu____1484) ->
                (match se with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1486 ->
                     let uu____1498 =
                       let uu____1499 =
                         let uu____1502 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant None
                            in
                         (uu____1502, false)  in
                       Term_name uu____1499  in
                     Some uu____1498
                 | FStar_Syntax_Syntax.Sig_datacon uu____1503 ->
                     let uu____1514 =
                       let uu____1515 =
                         let uu____1518 =
                           let uu____1519 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.Delta_constant uu____1519
                            in
                         (uu____1518, false)  in
                       Term_name uu____1515  in
                     Some uu____1514
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1521,lbs),uu____1523,uu____1524,uu____1525,uu____1526)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____1539 =
                       let uu____1540 =
                         let uu____1543 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____1543, false)  in
                       Term_name uu____1540  in
                     Some uu____1539
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____1545,uu____1546,quals,uu____1548) ->
                     let uu____1551 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___153_1553  ->
                                  match uu___153_1553 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1554 -> false)))
                        in
                     if uu____1551
                     then
                       let lid2 =
                         FStar_Ident.set_lid_range lid1
                           (FStar_Ident.range_of_lid source_lid)
                          in
                       let dd =
                         let uu____1558 =
                           (FStar_Syntax_Util.is_primop_lid lid2) ||
                             ((ns_of_lid_equals lid2
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___154_1560  ->
                                         match uu___154_1560 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1563 -> false))))
                            in
                         if uu____1558
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let uu____1565 =
                         FStar_Util.find_map quals
                           (fun uu___155_1567  ->
                              match uu___155_1567 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1570 -> None)
                          in
                       (match uu____1565 with
                        | Some refl_monad ->
                            let refl_const =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reflect refl_monad)))
                                None occurrence_range
                               in
                            Some (Term_name (refl_const, false))
                        | uu____1586 ->
                            let uu____1588 =
                              let uu____1589 =
                                let uu____1592 =
                                  let uu____1593 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____1593
                                   in
                                (uu____1592, false)  in
                              Term_name uu____1589  in
                            Some uu____1588)
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,_)
                   |FStar_Syntax_Syntax.Sig_new_effect (ne,_) ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1599 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1609 -> None)
             in
          let k_local_binding r =
            let uu____1621 =
              let uu____1622 =
                found_local_binding (FStar_Ident.range_of_lid lid) r  in
              Term_name uu____1622  in
            Some uu____1621  in
          let k_rec_binding uu____1632 =
            match uu____1632 with
            | (id,l,dd) ->
                let uu____1640 =
                  let uu____1641 =
                    let uu____1644 =
                      FStar_Syntax_Syntax.fvar
                        (FStar_Ident.set_lid_range l
                           (FStar_Ident.range_of_lid lid)) dd None
                       in
                    (uu____1644, false)  in
                  Term_name uu____1641  in
                Some uu____1640
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____1648 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____1648 with
                 | Some f -> Some (Term_name f)
                 | uu____1658 -> None)
            | uu____1662 -> None  in
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
        let uu____1682 = try_lookup_name true exclude_interf env lid  in
        match uu____1682 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____1691 -> None
  
let try_lookup_effect_name :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1702 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1702 with | Some (o,l1) -> Some l1 | uu____1711 -> None
  
let try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)
        Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____1725 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1725 with
      | Some (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1734),l1) ->
          Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,uu____1743),l1)
          -> Some (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          (FStar_Syntax_Syntax.Sig_effect_abbrev
           (uu____1751,uu____1752,uu____1753,uu____1754,uu____1755,cattributes,uu____1757),l1)
          -> Some (l1, cattributes)
      | uu____1769 -> None
  
let try_lookup_effect_defn :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      let uu____1783 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1783 with
      | Some (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1789),uu____1790)
          -> Some ne
      | Some
          (FStar_Syntax_Syntax.Sig_new_effect_for_free
           (ne,uu____1794),uu____1795)
          -> Some ne
      | uu____1798 -> None
  
let is_effect_name : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____1808 = try_lookup_effect_name env lid  in
      match uu____1808 with | None  -> false | Some uu____1810 -> true
  
let lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___157_1828 =
        match uu___157_1828 with
        | (FStar_Syntax_Syntax.Sig_declare_typ
           (lid2,uu____1834,uu____1835,quals,uu____1837),uu____1838) ->
            Some quals
        | uu____1842 -> None  in
      let uu____1846 =
        resolve_in_open_namespaces' env lid (fun uu____1850  -> None)
          (fun uu____1852  -> None) k_global_def
         in
      match uu____1846 with | Some quals -> quals | uu____1858 -> []
  
let try_lookup_module :
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul Prims.option =
  fun env  ->
    fun path  ->
      let uu____1870 =
        FStar_List.tryFind
          (fun uu____1876  ->
             match uu____1876 with
             | (mlid,modul) ->
                 let uu____1881 = FStar_Ident.path_of_lid mlid  in
                 uu____1881 = path) env.modules
         in
      match uu____1870 with
      | Some (uu____1885,modul) -> Some modul
      | None  -> None
  
let try_lookup_let :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___158_1907 =
        match uu___158_1907 with
        | (FStar_Syntax_Syntax.Sig_let
           ((uu____1911,lbs),uu____1913,uu____1914,uu____1915,uu____1916),uu____1917)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____1930 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            Some uu____1930
        | uu____1931 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____1934  -> None)
        (fun uu____1935  -> None) k_global_def
  
let try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___159_1954 =
        match uu___159_1954 with
        | (FStar_Syntax_Syntax.Sig_let
           (lbs,uu____1961,uu____1962,uu____1963,uu____1964),uu____1965) ->
            FStar_Util.find_map (Prims.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____1982 -> None)
        | uu____1987 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____1994  -> None)
        (fun uu____1997  -> None) k_global_def
  
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
          let uu____2018 = try_lookup_name any_val exclude_interf env lid  in
          match uu____2018 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____2027 -> None
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l 
let try_lookup_datacon :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___161_2056 =
        match uu___161_2056 with
        | (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2060,uu____2061,uu____2062,quals,uu____2064),uu____2065) ->
            let uu____2068 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___160_2070  ->
                      match uu___160_2070 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____2071 -> false))
               in
            if uu____2068
            then
              let uu____2073 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.Delta_constant None
                 in
              Some uu____2073
            else None
        | (FStar_Syntax_Syntax.Sig_datacon uu____2075,uu____2076) ->
            let uu____2087 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor)
               in
            Some uu____2087
        | uu____2088 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2091  -> None)
        (fun uu____2092  -> None) k_global_def
  
let find_all_datacons :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___162_2111 =
        match uu___162_2111 with
        | (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____2116,uu____2117,uu____2118,uu____2119,uu____2120,datas,uu____2122,uu____2123),uu____2124)
            -> Some datas
        | uu____2132 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2137  -> None)
        (fun uu____2139  -> None) k_global_def
  
let record_cache_aux_with_filter :
  (((Prims.unit -> Prims.unit) * (Prims.unit -> Prims.unit) *
    (Prims.unit -> record_or_dc Prims.list) * (record_or_dc -> Prims.unit) *
    (Prims.unit -> Prims.unit)) * (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____2173 =
    let uu____2174 =
      let uu____2177 =
        let uu____2179 = FStar_ST.read record_cache  in
        FStar_List.hd uu____2179  in
      let uu____2187 = FStar_ST.read record_cache  in uu____2177 ::
        uu____2187
       in
    FStar_ST.write record_cache uu____2174  in
  let pop1 uu____2202 =
    let uu____2203 =
      let uu____2206 = FStar_ST.read record_cache  in
      FStar_List.tl uu____2206  in
    FStar_ST.write record_cache uu____2203  in
  let peek uu____2222 =
    let uu____2223 = FStar_ST.read record_cache  in FStar_List.hd uu____2223
     in
  let insert r =
    let uu____2235 =
      let uu____2238 = let uu____2240 = peek ()  in r :: uu____2240  in
      let uu____2242 =
        let uu____2245 = FStar_ST.read record_cache  in
        FStar_List.tl uu____2245  in
      uu____2238 :: uu____2242  in
    FStar_ST.write record_cache uu____2235  in
  let commit1 uu____2261 =
    let uu____2262 = FStar_ST.read record_cache  in
    match uu____2262 with
    | hd1::uu____2270::tl1 -> FStar_ST.write record_cache (hd1 :: tl1)
    | uu____2283 -> failwith "Impossible"  in
  let filter1 uu____2289 =
    let rc = peek ()  in
    pop1 ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
            in
         let uu____2296 =
           let uu____2299 = FStar_ST.read record_cache  in filtered ::
             uu____2299
            in
         FStar_ST.write record_cache uu____2296)
     in
  let aux = (push1, pop1, peek, insert, commit1)  in (aux, filter1) 
let record_cache_aux :
  ((Prims.unit -> Prims.unit) * (Prims.unit -> Prims.unit) *
    (Prims.unit -> record_or_dc Prims.list) * (record_or_dc -> Prims.unit) *
    (Prims.unit -> Prims.unit))
  =
  let uu____2373 = record_cache_aux_with_filter  in
  match uu____2373 with | (aux,uu____2411) -> aux 
let filter_record_cache : Prims.unit -> Prims.unit =
  let uu____2450 = record_cache_aux_with_filter  in
  match uu____2450 with | (uu____2473,filter1) -> filter1 
let push_record_cache : Prims.unit -> Prims.unit =
  let uu____2513 = record_cache_aux  in
  match uu____2513 with
  | (push1,uu____2533,uu____2534,uu____2535,uu____2536) -> push1 
let pop_record_cache : Prims.unit -> Prims.unit =
  let uu____2561 = record_cache_aux  in
  match uu____2561 with
  | (uu____2580,pop1,uu____2582,uu____2583,uu____2584) -> pop1 
let peek_record_cache : Prims.unit -> record_or_dc Prims.list =
  let uu____2610 = record_cache_aux  in
  match uu____2610 with
  | (uu____2630,uu____2631,peek,uu____2633,uu____2634) -> peek 
let insert_record_cache : record_or_dc -> Prims.unit =
  let uu____2659 = record_cache_aux  in
  match uu____2659 with
  | (uu____2678,uu____2679,uu____2680,insert,uu____2682) -> insert 
let commit_record_cache : Prims.unit -> Prims.unit =
  let uu____2707 = record_cache_aux  in
  match uu____2707 with
  | (uu____2726,uu____2727,uu____2728,uu____2729,commit1) -> commit1 
let extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun uu___166_2764  ->
        match uu___166_2764 with
        | FStar_Syntax_Syntax.Sig_bundle
            (sigs,uu____2769,uu____2770,uu____2771) ->
            let is_rec =
              FStar_Util.for_some
                (fun uu___163_2782  ->
                   match uu___163_2782 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____2785 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___164_2793  ->
                      match uu___164_2793 with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2795,uu____2796,uu____2797,uu____2798,uu____2799,uu____2800,uu____2801)
                          -> FStar_Ident.lid_equals dc lid
                      | uu____2806 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___165_2808  ->
                    match uu___165_2808 with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (typename,univs,parms,uu____2812,uu____2813,dc::[],tags,uu____2816)
                        ->
                        let uu____2822 =
                          let uu____2823 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____2823  in
                        (match uu____2822 with
                         | FStar_Syntax_Syntax.Sig_datacon
                             (constrname,uu____2827,t,uu____2829,uu____2830,uu____2831,uu____2832,uu____2833)
                             ->
                             let uu____2838 =
                               FStar_Syntax_Util.arrow_formals_comp t  in
                             (match uu____2838 with
                              | (formals,uu____2845) ->
                                  let is_rec1 = is_rec tags  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____2867  ->
                                            match uu____2867 with
                                            | (x,q) ->
                                                let uu____2875 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec1 &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____2875
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____2906  ->
                                            match uu____2906 with
                                            | (x,q) ->
                                                let uu____2915 =
                                                  if is_rec1
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (uu____2915,
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
                                  ((let uu____2927 =
                                      let uu____2929 =
                                        FStar_ST.read new_globs  in
                                      (Record_or_dc record) :: uu____2929  in
                                    FStar_ST.write new_globs uu____2927);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____2945 =
                                            match uu____2945 with
                                            | (id,uu____2951) ->
                                                let modul =
                                                  let uu____2957 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____2957.FStar_Ident.str
                                                   in
                                                let uu____2958 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____2958 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____2974 =
                                                         let uu____2975 =
                                                           FStar_ST.read
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           uu____2975
                                                          in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         uu____2974);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____2982 =
                                                               let uu____2983
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id
                                                                  in
                                                               uu____2983.FStar_Ident.ident
                                                                in
                                                             uu____2982.FStar_Ident.idText
                                                              in
                                                           let uu____2985 =
                                                             let uu____2986 =
                                                               FStar_ST.read
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____2986
                                                              in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             uu____2985))
                                                 | None  -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____2999 -> ())
                    | uu____3000 -> ()))
        | uu____3001 -> ()
  
let try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____3014 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____3014 with
        | (ns,id) ->
            let uu____3024 = peek_record_cache ()  in
            FStar_Util.find_map uu____3024
              (fun record  ->
                 let uu____3027 =
                   find_in_record ns id record (fun r  -> Cont_ok r)  in
                 option_of_cont (fun uu____3030  -> None) uu____3027)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____3031  -> Cont_ignore) (fun uu____3032  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____3035 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____3035)
        (fun k  -> fun uu____3038  -> k)
  
let try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let uu____3047 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____3047 with
      | Some r when r.is_record -> Some r
      | uu____3051 -> None
  
let belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____3062 = try_lookup_record_by_field_name env lid  in
        match uu____3062 with
        | Some record' when
            let uu____3065 =
              let uu____3066 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____3066  in
            let uu____3068 =
              let uu____3069 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____3069  in
            uu____3065 = uu____3068 ->
            let uu____3071 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____3073  -> Cont_ok ())
               in
            (match uu____3071 with
             | Cont_ok uu____3074 -> true
             | uu____3075 -> false)
        | uu____3077 -> false
  
let try_lookup_dc_by_field_name :
  env -> FStar_Ident.lident -> (FStar_Ident.lident * Prims.bool) Prims.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____3088 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____3088 with
      | Some r ->
          let uu____3094 =
            let uu____3097 =
              let uu____3098 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              FStar_Ident.set_lid_range uu____3098
                (FStar_Ident.range_of_lid fieldname)
               in
            (uu____3097, (r.is_record))  in
          Some uu____3094
      | uu____3101 -> None
  
let string_set_ref_new :
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____3110  ->
    let uu____3111 =
      FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode  in
    FStar_Util.mk_ref uu____3111
  
let exported_id_set_new :
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____3122  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___167_3131  ->
      match uu___167_3131 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let empty_include_smap :
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap = new_sigmap () 
let empty_exported_id_smap : exported_id_set FStar_Util.smap = new_sigmap () 
let unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool =
  fun any_val  ->
    fun exclude_if  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___168_3157 =
            match uu___168_3157 with
            | Rec_binding uu____3158 -> true
            | uu____3159 -> false  in
          let this_env =
            let uu___173_3161 = env  in
            let uu____3162 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___173_3161.curmodule);
              curmonad = (uu___173_3161.curmonad);
              modules = (uu___173_3161.modules);
              scope_mods = uu____3162;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___173_3161.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___173_3161.sigaccum);
              sigmap = (uu___173_3161.sigmap);
              iface = (uu___173_3161.iface);
              admitted_iface = (uu___173_3161.admitted_iface);
              expect_typ = (uu___173_3161.expect_typ)
            }  in
          let uu____3164 = try_lookup_lid' any_val exclude_if this_env lid
             in
          match uu____3164 with | None  -> true | Some uu____3170 -> false
  
let push_scope_mod : env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___174_3181 = env  in
      {
        curmodule = (uu___174_3181.curmodule);
        curmonad = (uu___174_3181.curmonad);
        modules = (uu___174_3181.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___174_3181.exported_ids);
        trans_exported_ids = (uu___174_3181.trans_exported_ids);
        includes = (uu___174_3181.includes);
        sigaccum = (uu___174_3181.sigaccum);
        sigmap = (uu___174_3181.sigmap);
        iface = (uu___174_3181.iface);
        admitted_iface = (uu___174_3181.admitted_iface);
        expect_typ = (uu___174_3181.expect_typ)
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
        let uu____3220 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____3220
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
          | Some (se,uu____3240) ->
              let uu____3243 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____3243 with
               | Some l1 ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l1)
               | None  -> "<unknown>")
          | None  -> "<unknown>"  in
        let uu____3248 =
          let uu____3249 =
            let uu____3252 =
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                (FStar_Ident.text_of_lid l) r
               in
            (uu____3252, (FStar_Ident.range_of_lid l))  in
          FStar_Errors.Error uu____3249  in
        Prims.raise uu____3248  in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env1 =
        let uu____3259 =
          match s with
          | FStar_Syntax_Syntax.Sig_let uu____3264 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3273 -> (true, true)
          | uu____3281 -> (false, false)  in
        match uu____3259 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____3286 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3289 =
                     let uu____3290 = unique any_val exclude_if env l  in
                     Prims.op_Negation uu____3290  in
                   if uu____3289 then Some l else None)
               in
            (match uu____3286 with
             | Some l when
                 let uu____3294 = FStar_Options.interactive ()  in
                 Prims.op_Negation uu____3294 -> err l
             | uu____3295 ->
                 (extract_record env globals s;
                  (let uu___175_3300 = env  in
                   {
                     curmodule = (uu___175_3300.curmodule);
                     curmonad = (uu___175_3300.curmonad);
                     modules = (uu___175_3300.modules);
                     scope_mods = (uu___175_3300.scope_mods);
                     exported_ids = (uu___175_3300.exported_ids);
                     trans_exported_ids = (uu___175_3300.trans_exported_ids);
                     includes = (uu___175_3300.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___175_3300.sigmap);
                     iface = (uu___175_3300.iface);
                     admitted_iface = (uu___175_3300.admitted_iface);
                     expect_typ = (uu___175_3300.expect_typ)
                   })))
         in
      let env2 =
        let uu___176_3302 = env1  in
        let uu____3303 = FStar_ST.read globals  in
        {
          curmodule = (uu___176_3302.curmodule);
          curmonad = (uu___176_3302.curmonad);
          modules = (uu___176_3302.modules);
          scope_mods = uu____3303;
          exported_ids = (uu___176_3302.exported_ids);
          trans_exported_ids = (uu___176_3302.trans_exported_ids);
          includes = (uu___176_3302.includes);
          sigaccum = (uu___176_3302.sigaccum);
          sigmap = (uu___176_3302.sigmap);
          iface = (uu___176_3302.iface);
          admitted_iface = (uu___176_3302.admitted_iface);
          expect_typ = (uu___176_3302.expect_typ)
        }  in
      let uu____3308 =
        match s with
        | FStar_Syntax_Syntax.Sig_bundle
            (ses,uu____3322,uu____3323,uu____3324) ->
            let uu____3331 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env2, uu____3331)
        | uu____3345 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____3308 with
      | (env3,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3375  ->
                   match uu____3375 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let uu____3386 =
                                  let uu____3388 = FStar_ST.read globals  in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    uu____3388
                                   in
                                FStar_ST.write globals uu____3386);
                               (match () with
                                | () ->
                                    let modul =
                                      let uu____3397 =
                                        FStar_Ident.lid_of_ids
                                          lid.FStar_Ident.ns
                                         in
                                      uu____3397.FStar_Ident.str  in
                                    ((let uu____3399 =
                                        get_exported_id_set env3 modul  in
                                      match uu____3399 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let uu____3414 =
                                            let uu____3415 =
                                              FStar_ST.read my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              uu____3415
                                             in
                                          FStar_ST.write my_exported_ids
                                            uu____3414
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
              let uu___177_3427 = env3  in
              let uu____3428 = FStar_ST.read globals  in
              {
                curmodule = (uu___177_3427.curmodule);
                curmonad = (uu___177_3427.curmonad);
                modules = (uu___177_3427.modules);
                scope_mods = uu____3428;
                exported_ids = (uu___177_3427.exported_ids);
                trans_exported_ids = (uu___177_3427.trans_exported_ids);
                includes = (uu___177_3427.includes);
                sigaccum = (uu___177_3427.sigaccum);
                sigmap = (uu___177_3427.sigmap);
                iface = (uu___177_3427.iface);
                admitted_iface = (uu___177_3427.admitted_iface);
                expect_typ = (uu___177_3427.expect_typ)
              }  in
            env4))
  
let push_namespace : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3439 =
        let uu____3442 = resolve_module_name env ns false  in
        match uu____3442 with
        | None  ->
            let modules = env.modules  in
            let uu____3450 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3456  ->
                      match uu____3456 with
                      | (m,uu____3460) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) ".")))
               in
            if uu____3450
            then (ns, Open_namespace)
            else
              (let uu____3464 =
                 let uu____3465 =
                   let uu____3468 =
                     FStar_Util.format1 "Namespace %s cannot be found"
                       (FStar_Ident.text_of_lid ns)
                      in
                   (uu____3468, (FStar_Ident.range_of_lid ns))  in
                 FStar_Errors.Error uu____3465  in
               Prims.raise uu____3464)
        | Some ns' -> (ns', Open_module)  in
      match uu____3439 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
  
let push_include : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3480 = resolve_module_name env ns false  in
      match uu____3480 with
      | Some ns1 ->
          let env1 =
            push_scope_mod env (Open_module_or_namespace (ns1, Open_module))
             in
          let curmod =
            let uu____3485 = current_module env1  in
            uu____3485.FStar_Ident.str  in
          ((let uu____3487 = FStar_Util.smap_try_find env1.includes curmod
               in
            match uu____3487 with
            | None  -> ()
            | Some incl ->
                let uu____3500 =
                  let uu____3502 = FStar_ST.read incl  in ns1 :: uu____3502
                   in
                FStar_ST.write incl uu____3500);
           (match () with
            | () ->
                let uu____3510 =
                  get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                (match uu____3510 with
                 | Some ns_trans_exports ->
                     ((let uu____3523 =
                         let uu____3534 = get_exported_id_set env1 curmod  in
                         let uu____3539 =
                           get_trans_exported_id_set env1 curmod  in
                         (uu____3534, uu____3539)  in
                       match uu____3523 with
                       | (Some cur_exports,Some cur_trans_exports) ->
                           let update_exports k =
                             let ns_ex =
                               let uu____3579 = ns_trans_exports k  in
                               FStar_ST.read uu____3579  in
                             let ex = cur_exports k  in
                             (let uu____3588 =
                                let uu____3589 = FStar_ST.read ex  in
                                FStar_Util.set_difference uu____3589 ns_ex
                                 in
                              FStar_ST.write ex uu____3588);
                             (match () with
                              | () ->
                                  let trans_ex = cur_trans_exports k  in
                                  let uu____3599 =
                                    let uu____3600 = FStar_ST.read ex  in
                                    FStar_Util.set_union uu____3600 ns_ex  in
                                  FStar_ST.write trans_ex uu____3599)
                              in
                           FStar_List.iter update_exports
                             all_exported_id_kinds
                       | uu____3606 -> ());
                      (match () with | () -> env1))
                 | None  ->
                     let uu____3620 =
                       let uu____3621 =
                         let uu____3624 =
                           FStar_Util.format1
                             "include: Module %s was not prepared"
                             ns1.FStar_Ident.str
                            in
                         (uu____3624, (FStar_Ident.range_of_lid ns1))  in
                       FStar_Errors.Error uu____3621  in
                     Prims.raise uu____3620)))
      | uu____3625 ->
          let uu____3627 =
            let uu____3628 =
              let uu____3631 =
                FStar_Util.format1 "include: Module %s cannot be found"
                  ns.FStar_Ident.str
                 in
              (uu____3631, (FStar_Ident.range_of_lid ns))  in
            FStar_Errors.Error uu____3628  in
          Prims.raise uu____3627
  
let push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____3641 = module_is_defined env l  in
        if uu____3641
        then push_scope_mod env (Module_abbrev (x, l))
        else
          (let uu____3643 =
             let uu____3644 =
               let uu____3647 =
                 FStar_Util.format1 "Module %s cannot be found"
                   (FStar_Ident.text_of_lid l)
                  in
               (uu____3647, (FStar_Ident.range_of_lid l))  in
             FStar_Errors.Error uu____3644  in
           Prims.raise uu____3643)
  
let check_admits : env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,quals,r) ->
                let uu____3659 = try_lookup_lid env l  in
                (match uu____3659 with
                 | None  ->
                     ((let uu____3666 =
                         let uu____3667 = FStar_Options.interactive ()  in
                         Prims.op_Negation uu____3667  in
                       if uu____3666
                       then
                         let uu____3668 =
                           let uu____3669 =
                             FStar_Range.string_of_range
                               (FStar_Ident.range_of_lid l)
                              in
                           let uu____3670 =
                             FStar_Syntax_Print.lid_to_string l  in
                           FStar_Util.format2
                             "%s: Warning: Admitting %s without a definition\n"
                             uu____3669 uu____3670
                            in
                         FStar_Util.print_string uu____3668
                       else ());
                      FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                        ((FStar_Syntax_Syntax.Sig_declare_typ
                            (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                              quals), r)), false))
                 | Some uu____3675 -> ())
            | uu____3680 -> ()))
  
let finish : env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun uu___170_3688  ->
              match uu___170_3688 with
              | FStar_Syntax_Syntax.Sig_bundle
                  (ses,quals,uu____3691,uu____3692) ->
                  if
                    (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                      ||
                      (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun uu___169_3700  ->
                            match uu___169_3700 with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid,uu____3702,uu____3703,uu____3704,uu____3705,uu____3706,uu____3707,uu____3708)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____3715 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____3718,uu____3719,quals,uu____3721) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____3727,lbs),r,uu____3730,quals,uu____3732) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____3747 =
                               let uu____3748 =
                                 let uu____3749 =
                                   let uu____3754 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____3754.FStar_Syntax_Syntax.fv_name  in
                                 uu____3749.FStar_Syntax_Syntax.v  in
                               uu____3748.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____3747))
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
                               let uu____3764 =
                                 let uu____3769 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____3769.FStar_Syntax_Syntax.fv_name  in
                               uu____3764.FStar_Syntax_Syntax.v  in
                             let decl =
                               FStar_Syntax_Syntax.Sig_declare_typ
                                 (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                   (lb.FStar_Syntax_Syntax.lbtyp),
                                   (FStar_Syntax_Syntax.Assumption :: quals),
                                   r)
                                in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____3781 -> ()));
      (let curmod =
         let uu____3783 = current_module env  in uu____3783.FStar_Ident.str
          in
       (let uu____3785 =
          let uu____3796 = get_exported_id_set env curmod  in
          let uu____3801 = get_trans_exported_id_set env curmod  in
          (uu____3796, uu____3801)  in
        match uu____3785 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____3841 = cur_ex eikind  in FStar_ST.read uu____3841
                 in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____3849 =
                let uu____3850 = FStar_ST.read cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____3850  in
              FStar_ST.write cur_trans_ex_set_ref uu____3849  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____3856 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___178_3868 = env  in
                  {
                    curmodule = None;
                    curmonad = (uu___178_3868.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___178_3868.exported_ids);
                    trans_exported_ids = (uu___178_3868.trans_exported_ids);
                    includes = (uu___178_3868.includes);
                    sigaccum = [];
                    sigmap = (uu___178_3868.sigmap);
                    iface = (uu___178_3868.iface);
                    admitted_iface = (uu___178_3868.admitted_iface);
                    expect_typ = (uu___178_3868.expect_typ)
                  }))))
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push : env -> env =
  fun env  ->
    push_record_cache ();
    (let uu____3881 =
       let uu____3883 = FStar_ST.read stack  in env :: uu____3883  in
     FStar_ST.write stack uu____3881);
    (let uu___179_3891 = env  in
     let uu____3892 = FStar_Util.smap_copy (sigmap env)  in
     {
       curmodule = (uu___179_3891.curmodule);
       curmonad = (uu___179_3891.curmonad);
       modules = (uu___179_3891.modules);
       scope_mods = (uu___179_3891.scope_mods);
       exported_ids = (uu___179_3891.exported_ids);
       trans_exported_ids = (uu___179_3891.trans_exported_ids);
       includes = (uu___179_3891.includes);
       sigaccum = (uu___179_3891.sigaccum);
       sigmap = uu____3892;
       iface = (uu___179_3891.iface);
       admitted_iface = (uu___179_3891.admitted_iface);
       expect_typ = (uu___179_3891.expect_typ)
     })
  
let pop : Prims.unit -> env =
  fun uu____3900  ->
    let uu____3901 = FStar_ST.read stack  in
    match uu____3901 with
    | env::tl1 -> (pop_record_cache (); FStar_ST.write stack tl1; env)
    | uu____3914 -> failwith "Impossible: Too many pops"
  
let commit_mark : env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____3920 = FStar_ST.read stack  in
     match uu____3920 with
     | uu____3925::tl1 -> (FStar_ST.write stack tl1; env)
     | uu____3932 -> failwith "Impossible: Too many pops")
  
let mark : env -> env = fun x  -> push x 
let reset_mark : Prims.unit -> env = fun uu____3939  -> pop () 
let export_interface : FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____3951 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____3953 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____3971 = FStar_Util.smap_try_find sm' k  in
              match uu____3971 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,q,r) ->
                          FStar_Syntax_Syntax.Sig_declare_typ
                            (l, u, t, (FStar_Syntax_Syntax.Assumption :: q),
                              r)
                      | uu____3992 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____3995 -> ()));
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
            (let uu____4039 = exported_id_set_new ()  in
             FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
               uu____4039);
            (match () with
             | () ->
                 ((let uu____4044 = exported_id_set_new ()  in
                   FStar_Util.smap_add env1.trans_exported_ids
                     mname.FStar_Ident.str uu____4044);
                  (match () with
                   | () ->
                       ((let uu____4049 = FStar_Util.mk_ref []  in
                         FStar_Util.smap_add env1.includes
                           mname.FStar_Ident.str uu____4049);
                        (match () with
                         | () ->
                             let uu___180_4058 = env1  in
                             let uu____4059 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns1
                                in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___180_4058.curmonad);
                               modules = (uu___180_4058.modules);
                               scope_mods = uu____4059;
                               exported_ids = (uu___180_4058.exported_ids);
                               trans_exported_ids =
                                 (uu___180_4058.trans_exported_ids);
                               includes = (uu___180_4058.includes);
                               sigaccum = (uu___180_4058.sigaccum);
                               sigmap = (env1.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___180_4058.expect_typ)
                             })))))
             in
          let uu____4062 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____4074  ->
                    match uu____4074 with
                    | (l,uu____4078) -> FStar_Ident.lid_equals l mname))
             in
          match uu____4062 with
          | None  -> let uu____4083 = prep env  in (uu____4083, false)
          | Some (uu____4084,m) ->
              ((let uu____4089 =
                  (let uu____4090 = FStar_Options.interactive ()  in
                   Prims.op_Negation uu____4090) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf)
                   in
                if uu____4089
                then
                  let uu____4091 =
                    let uu____4092 =
                      let uu____4095 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (uu____4095, (FStar_Ident.range_of_lid mname))  in
                    FStar_Errors.Error uu____4092  in
                  Prims.raise uu____4091
                else ());
               (let uu____4097 =
                  let uu____4098 = push env  in prep uu____4098  in
                (uu____4097, true)))
  
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
          let uu___181_4106 = env  in
          {
            curmodule = (uu___181_4106.curmodule);
            curmonad = (Some mname);
            modules = (uu___181_4106.modules);
            scope_mods = (uu___181_4106.scope_mods);
            exported_ids = (uu___181_4106.exported_ids);
            trans_exported_ids = (uu___181_4106.trans_exported_ids);
            includes = (uu___181_4106.includes);
            sigaccum = (uu___181_4106.sigaccum);
            sigmap = (uu___181_4106.sigmap);
            iface = (uu___181_4106.iface);
            admitted_iface = (uu___181_4106.admitted_iface);
            expect_typ = (uu___181_4106.expect_typ)
          }
  
let fail_or env lookup lid =
  let uu____4131 = lookup lid  in
  match uu____4131 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____4137  ->
             match uu____4137 with
             | (lid1,uu____4141) -> FStar_Ident.text_of_lid lid1) env.modules
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
             let uu____4148 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
             FStar_Ident.set_lid_range uu____4148
               (FStar_Ident.range_of_lid lid)
              in
           let uu____4149 = resolve_module_name env modul true  in
           match uu____4149 with
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
  let uu____4176 = lookup id  in
  match uu____4176 with
  | None  ->
      Prims.raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r 