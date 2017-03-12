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
      | None  -> let _0_292 = current_module env  in qual _0_292 id
      | Some monad ->
          let _0_294 = let _0_293 = current_module env  in qual _0_293 monad
             in
          FStar_Syntax_Util.mk_field_projector_name_from_ident _0_294 id
  
let new_sigmap uu____377 = FStar_Util.smap_create (Prims.parse_int "100") 
let empty_env : Prims.unit -> env =
  fun uu____380  ->
    let _0_298 = new_sigmap ()  in
    let _0_297 = new_sigmap ()  in
    let _0_296 = new_sigmap ()  in
    let _0_295 = new_sigmap ()  in
    {
      curmodule = None;
      curmonad = None;
      modules = [];
      scope_mods = [];
      exported_ids = _0_298;
      trans_exported_ids = _0_297;
      includes = _0_296;
      sigaccum = [];
      sigmap = _0_295;
      iface = false;
      admitted_iface = false;
      expect_typ = false
    }
  
let sigmap : env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap
  = fun env  -> env.sigmap 
let has_all_in_scope : env -> Prims.bool =
  fun env  ->
    FStar_List.existsb
      (fun uu____398  ->
         match uu____398 with
         | (m,uu____402) ->
             FStar_Ident.lid_equals m FStar_Syntax_Const.all_lid) env.modules
  
let set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv =
  fun bv  ->
    fun r  ->
      let id =
        let uu___172_410 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___172_410.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___173_411 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id;
        FStar_Syntax_Syntax.index = (uu___173_411.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___173_411.FStar_Syntax_Syntax.sort)
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
        (fun uu____457  ->
           match uu____457 with
           | (x,y,dd,dq) ->
               if id.FStar_Ident.idText = x
               then
                 Some
                   (let _0_299 =
                      FStar_Ident.lid_of_path ["Prims"; y]
                        id.FStar_Ident.idRange
                       in
                    FStar_Syntax_Syntax.fvar _0_299 dd dq)
               else None)
       in
    match t with | Some v -> Some (v, false) | None  -> None
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok projectee =
  match projectee with | Cont_ok _0 -> true | uu____500 -> false 
let __proj__Cont_ok__item___0 projectee =
  match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail projectee =
  match projectee with | Cont_fail  -> true | uu____524 -> false 
let uu___is_Cont_ignore projectee =
  match projectee with | Cont_ignore  -> true | uu____535 -> false 
let option_of_cont k_ignore uu___142_554 =
  match uu___142_554 with
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
    let find =
      FStar_Util.find_map record.fields
        (fun uu____599  ->
           match uu____599 with
           | (f,uu____604) ->
               if id.FStar_Ident.idText = f.FStar_Ident.idText
               then Some record
               else None)
       in
    match find with | Some r -> cont r | None  -> Cont_ignore
  else Cont_ignore 
let get_exported_id_set : env -> Prims.string -> exported_id_set Prims.option
  = fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname 
let get_trans_exported_id_set :
  env -> Prims.string -> exported_id_set Prims.option =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname 
let string_of_exported_id_kind : exported_id_kind -> Prims.string =
  fun uu___143_640  ->
    match uu___143_640 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
  
let find_in_module_with_includes eikind find_in_module find_in_module_default
  env ns id =
  let idstr = id.FStar_Ident.idText  in
  let rec aux uu___144_689 =
    match uu___144_689 with
    | [] -> find_in_module_default
    | modul::q ->
        let mname = modul.FStar_Ident.str  in
        let not_shadowed =
          let uu____697 = get_exported_id_set env mname  in
          match uu____697 with
          | None  -> true
          | Some mex ->
              let mexports = FStar_ST.read (mex eikind)  in
              FStar_Util.set_mem idstr mexports
           in
        let mincludes =
          let uu____717 = FStar_Util.smap_try_find env.includes mname  in
          match uu____717 with
          | None  -> []
          | Some minc -> FStar_ST.read minc  in
        let look_into =
          if not_shadowed
          then find_in_module (qual modul id)
          else Cont_ignore  in
        (match look_into with
         | Cont_ignore  -> aux (FStar_List.append mincludes q)
         | uu____739 -> look_into)
     in
  aux [ns] 
let is_exported_id_field : exported_id_kind -> Prims.bool =
  fun uu___145_743  ->
    match uu___145_743 with | Exported_id_field  -> true | uu____744 -> false
  
let try_lookup_id'' env id eikind k_local_binding k_rec_binding k_record
  find_in_module lookup_default_id =
  let check_local_binding_id uu___146_833 =
    match uu___146_833 with
    | (id',uu____835,uu____836) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText
     in
  let check_rec_binding_id uu___147_840 =
    match uu___147_840 with
    | (id',uu____842,uu____843) ->
        id'.FStar_Ident.idText = id.FStar_Ident.idText
     in
  let curmod_ns = FStar_Ident.ids_of_lid (current_module env)  in
  let proc uu___148_850 =
    match uu___148_850 with
    | Local_binding l when check_local_binding_id l -> k_local_binding l
    | Rec_binding r when check_rec_binding_id r -> k_rec_binding r
    | Open_module_or_namespace (ns,uu____855) ->
        find_in_module_with_includes eikind find_in_module Cont_ignore env ns
          id
    | Top_level_def id' when id'.FStar_Ident.idText = id.FStar_Ident.idText
        -> lookup_default_id Cont_ignore id
    | Record_or_dc r when is_exported_id_field eikind ->
        let _0_300 = FStar_Ident.lid_of_ids curmod_ns  in
        find_in_module_with_includes Exported_id_field
          (fun lid  ->
             let id = lid.FStar_Ident.ident  in
             find_in_record lid.FStar_Ident.ns id r k_record) Cont_ignore env
          _0_300 id
    | uu____860 -> Cont_ignore  in
  let rec aux uu___149_866 =
    match uu___149_866 with
    | a::q ->
        let _0_301 = proc a  in
        option_of_cont (fun uu____872  -> aux q) _0_301
    | [] ->
        let _0_302 = lookup_default_id Cont_fail id  in
        option_of_cont (fun uu____873  -> None) _0_302
     in
  aux env.scope_mods 
let found_local_binding r uu____892 =
  match uu____892 with
  | (id',x,mut) -> let _0_303 = bv_to_name x r  in (_0_303, mut) 
let find_in_module env lid k_global_def k_not_found =
  let uu____935 = FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
     in
  match uu____935 with
  | Some sb -> k_global_def lid sb
  | None  -> k_not_found 
let try_lookup_id :
  env ->
    FStar_Ident.ident -> (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  =
  fun env  ->
    fun id  ->
      let uu____957 = unmangleOpName id  in
      match uu____957 with
      | Some f -> Some f
      | uu____971 ->
          try_lookup_id'' env id Exported_id_term_type
            (fun r  -> Cont_ok (found_local_binding id.FStar_Ident.idRange r))
            (fun uu____980  -> Cont_fail) (fun uu____983  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____990  -> fun uu____991  -> Cont_fail) Cont_ignore)
            (fun uu____998  -> fun uu____999  -> Cont_fail)
  
let lookup_default_id env id k_global_def k_not_found =
  let find_in_monad =
    match env.curmonad with
    | Some uu____1051 ->
        let lid = qualify env id  in
        let uu____1053 =
          FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
        (match uu____1053 with
         | Some r -> Some (k_global_def lid r)
         | None  -> None)
    | None  -> None  in
  match find_in_monad with
  | Some v -> v
  | None  ->
      let lid = let _0_304 = current_module env  in qual _0_304 id  in
      find_in_module env lid k_global_def k_not_found
  
let module_is_defined : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      (let _0_305 = current_module env  in FStar_Ident.lid_equals lid _0_305)
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
        let rec aux uu___150_1107 =
          match uu___150_1107 with
          | [] ->
              let uu____1110 = module_is_defined env lid  in
              if uu____1110 then Some lid else None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let _0_308 =
                  let _0_307 = FStar_Ident.path_of_lid ns  in
                  let _0_306 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append _0_307 _0_306  in
                FStar_Ident.lid_of_path _0_308 (FStar_Ident.range_of_lid lid)
                 in
              let uu____1117 = module_is_defined env new_lid  in
              if uu____1117 then Some new_lid else aux q
          | (Module_abbrev (name,modul))::uu____1122 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> Some modul
          | uu____1126::q -> aux q  in
        aux env.scope_mods
  
let resolve_in_open_namespaces'' env lid eikind k_local_binding k_rec_binding
  k_record f_module l_default =
  match lid.FStar_Ident.ns with
  | uu____1214::uu____1215 ->
      let uu____1217 =
        let _0_310 =
          let _0_309 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_Ident.set_lid_range _0_309 (FStar_Ident.range_of_lid lid)  in
        resolve_module_name env _0_310 true  in
      (match uu____1217 with
       | None  -> None
       | Some modul ->
           let _0_311 =
             find_in_module_with_includes eikind f_module Cont_fail env modul
               lid.FStar_Ident.ident
              in
           option_of_cont (fun uu____1221  -> None) _0_311)
  | [] ->
      try_lookup_id'' env lid.FStar_Ident.ident eikind k_local_binding
        k_rec_binding k_record f_module l_default
  
let cont_of_option k_none uu___151_1236 =
  match uu___151_1236 with | Some v -> Cont_ok v | None  -> k_none 
let resolve_in_open_namespaces' env lid k_local_binding k_rec_binding
  k_global_def =
  let k_global_def' k lid def =
    let _0_312 = k_global_def lid def  in cont_of_option k _0_312  in
  let f_module lid' =
    let k = Cont_ignore  in find_in_module env lid' (k_global_def' k) k  in
  let l_default k i = lookup_default_id env i (k_global_def' k) k  in
  resolve_in_open_namespaces'' env lid Exported_id_term_type
    (fun l  ->
       let _0_313 = k_local_binding l  in cont_of_option Cont_fail _0_313)
    (fun r  ->
       let _0_314 = k_rec_binding r  in cont_of_option Cont_fail _0_314)
    (fun uu____1335  -> Cont_ignore) f_module l_default
  
let fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.fv_qual Prims.option =
  fun uu___153_1339  ->
    match uu___153_1339 with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____1341,uu____1342,uu____1343,l,uu____1345,quals,uu____1347,uu____1348)
        ->
        let qopt =
          FStar_Util.find_map quals
            (fun uu___152_1355  ->
               match uu___152_1355 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____1357,fs) ->
                   Some (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____1364 -> None)
           in
        (match qopt with
         | None  -> Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ
        (uu____1368,uu____1369,uu____1370,quals,uu____1372) -> None
    | uu____1375 -> None
  
let lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv
  =
  fun lbs  ->
    fun lid  ->
      let _0_315 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____1387 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____1387 then Some fv else None)
         in
      FStar_All.pipe_right _0_315 FStar_Util.must
  
let ns_of_lid_equals : FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
  =
  fun lid  ->
    fun ns  ->
      ((FStar_List.length lid.FStar_Ident.ns) =
         (FStar_List.length (FStar_Ident.ids_of_lid ns)))
        &&
        (let _0_316 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals _0_316 ns)
  
let try_lookup_name :
  Prims.bool ->
    Prims.bool -> env -> FStar_Ident.lident -> foundname Prims.option
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid  in
          let k_global_def source_lid uu___157_1424 =
            match uu___157_1424 with
            | (uu____1428,true ) when exclude_interf -> None
            | (se,uu____1430) ->
                (match se with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____1432 ->
                     Some
                       (Term_name
                          (let _0_317 =
                             FStar_Syntax_Syntax.fvar source_lid
                               FStar_Syntax_Syntax.Delta_constant None
                              in
                           (_0_317, false)))
                 | FStar_Syntax_Syntax.Sig_datacon uu____1444 ->
                     Some
                       (Term_name
                          (let _0_319 =
                             let _0_318 = fv_qual_of_se se  in
                             FStar_Syntax_Syntax.fvar source_lid
                               FStar_Syntax_Syntax.Delta_constant _0_318
                              in
                           (_0_319, false)))
                 | FStar_Syntax_Syntax.Sig_let
                     ((uu____1455,lbs),uu____1457,uu____1458,uu____1459,uu____1460)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     Some
                       (Term_name
                          (let _0_320 =
                             FStar_Syntax_Syntax.fvar source_lid
                               fv.FStar_Syntax_Syntax.fv_delta
                               fv.FStar_Syntax_Syntax.fv_qual
                              in
                           (_0_320, false)))
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid,uu____1474,uu____1475,quals,uu____1477) ->
                     let uu____1480 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___154_1482  ->
                                  match uu___154_1482 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____1483 -> false)))
                        in
                     if uu____1480
                     then
                       let lid =
                         FStar_Ident.set_lid_range lid
                           (FStar_Ident.range_of_lid source_lid)
                          in
                       let dd =
                         let uu____1487 =
                           (FStar_Syntax_Util.is_primop_lid lid) ||
                             ((ns_of_lid_equals lid
                                 FStar_Syntax_Const.prims_lid)
                                &&
                                (FStar_All.pipe_right quals
                                   (FStar_Util.for_some
                                      (fun uu___155_1489  ->
                                         match uu___155_1489 with
                                         | FStar_Syntax_Syntax.Projector _
                                           |FStar_Syntax_Syntax.Discriminator
                                           _ -> true
                                         | uu____1492 -> false))))
                            in
                         if uu____1487
                         then FStar_Syntax_Syntax.Delta_equational
                         else FStar_Syntax_Syntax.Delta_constant  in
                       let uu____1494 =
                         FStar_Util.find_map quals
                           (fun uu___156_1496  ->
                              match uu___156_1496 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  Some refl_monad
                              | uu____1499 -> None)
                          in
                       (match uu____1494 with
                        | Some refl_monad ->
                            let refl_const =
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_constant
                                    (FStar_Const.Const_reflect refl_monad)))
                                None occurrence_range
                               in
                            Some (Term_name (refl_const, false))
                        | uu____1515 ->
                            Some
                              (Term_name
                                 (let _0_322 =
                                    let _0_321 = fv_qual_of_se se  in
                                    FStar_Syntax_Syntax.fvar lid dd _0_321
                                     in
                                  (_0_322, false))))
                     else None
                 | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,_)
                   |FStar_Syntax_Syntax.Sig_new_effect (ne,_) ->
                     Some
                       (Eff_name
                          (se,
                            (FStar_Ident.set_lid_range
                               ne.FStar_Syntax_Syntax.mname
                               (FStar_Ident.range_of_lid source_lid))))
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____1521 ->
                     Some (Eff_name (se, source_lid))
                 | uu____1531 -> None)
             in
          let k_local_binding r =
            Some
              (Term_name
                 (found_local_binding (FStar_Ident.range_of_lid lid) r))
             in
          let k_rec_binding uu____1550 =
            match uu____1550 with
            | (id,l,dd) ->
                Some
                  (Term_name
                     (let _0_323 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range l
                             (FStar_Ident.range_of_lid lid)) dd None
                         in
                      (_0_323, false)))
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____1561 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____1561 with
                 | Some f -> Some (Term_name f)
                 | uu____1571 -> None)
            | uu____1575 -> None  in
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
        let uu____1595 = try_lookup_name true exclude_interf env lid  in
        match uu____1595 with
        | Some (Eff_name (o,l)) -> Some (o, l)
        | uu____1604 -> None
  
let try_lookup_effect_name :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.option =
  fun env  ->
    fun l  ->
      let uu____1615 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1615 with | Some (o,l) -> Some l | uu____1624 -> None
  
let try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)
        Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____1638 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1638 with
      | Some (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1647),l) ->
          Some (l, (ne.FStar_Syntax_Syntax.cattributes))
      | Some (FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,uu____1656),l)
          -> Some (l, (ne.FStar_Syntax_Syntax.cattributes))
      | Some
          (FStar_Syntax_Syntax.Sig_effect_abbrev
           (uu____1664,uu____1665,uu____1666,uu____1667,uu____1668,cattributes,uu____1670),l)
          -> Some (l, cattributes)
      | uu____1682 -> None
  
let try_lookup_effect_defn :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      let uu____1696 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____1696 with
      | Some (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1702),uu____1703)
          -> Some ne
      | Some
          (FStar_Syntax_Syntax.Sig_new_effect_for_free
           (ne,uu____1707),uu____1708)
          -> Some ne
      | uu____1711 -> None
  
let is_effect_name : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____1721 = try_lookup_effect_name env lid  in
      match uu____1721 with | None  -> false | Some uu____1723 -> true
  
let lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun lid  ->
      let k_global_def lid uu___158_1741 =
        match uu___158_1741 with
        | (FStar_Syntax_Syntax.Sig_declare_typ
           (lid,uu____1747,uu____1748,quals,uu____1750),uu____1751) ->
            Some quals
        | uu____1755 -> None  in
      let uu____1759 =
        resolve_in_open_namespaces' env lid (fun uu____1763  -> None)
          (fun uu____1765  -> None) k_global_def
         in
      match uu____1759 with | Some quals -> quals | uu____1771 -> []
  
let try_lookup_module :
  env -> Prims.string Prims.list -> FStar_Syntax_Syntax.modul Prims.option =
  fun env  ->
    fun path  ->
      let uu____1783 =
        FStar_List.tryFind
          (fun uu____1789  ->
             match uu____1789 with
             | (mlid,modul) ->
                 let _0_324 = FStar_Ident.path_of_lid mlid  in _0_324 = path)
          env.modules
         in
      match uu____1783 with
      | Some (uu____1796,modul) -> Some modul
      | None  -> None
  
let try_lookup_let :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid uu___159_1818 =
        match uu___159_1818 with
        | (FStar_Syntax_Syntax.Sig_let
           ((uu____1822,lbs),uu____1824,uu____1825,uu____1826,uu____1827),uu____1828)
            ->
            let fv = lb_fv lbs lid  in
            Some
              (FStar_Syntax_Syntax.fvar lid fv.FStar_Syntax_Syntax.fv_delta
                 fv.FStar_Syntax_Syntax.fv_qual)
        | uu____1841 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____1844  -> None)
        (fun uu____1845  -> None) k_global_def
  
let try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid uu___160_1864 =
        match uu___160_1864 with
        | (FStar_Syntax_Syntax.Sig_let
           (lbs,uu____1871,uu____1872,uu____1873,uu____1874),uu____1875) ->
            FStar_Util.find_map (Prims.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid ->
                     Some (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____1892 -> None)
        | uu____1897 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____1904  -> None)
        (fun uu____1907  -> None) k_global_def
  
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
          let uu____1928 = try_lookup_name any_val exclude_interf env lid  in
          match uu____1928 with
          | Some (Term_name (e,mut)) -> Some (e, mut)
          | uu____1937 -> None
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * Prims.bool) Prims.option
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l 
let try_lookup_datacon :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.fv Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid uu___162_1966 =
        match uu___162_1966 with
        | (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____1970,uu____1971,uu____1972,quals,uu____1974),uu____1975) ->
            let uu____1978 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___161_1980  ->
                      match uu___161_1980 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____1981 -> false))
               in
            if uu____1978
            then
              Some
                (FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_constant None)
            else None
        | (FStar_Syntax_Syntax.Sig_datacon uu____1984,uu____1985) ->
            Some
              (FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 (Some FStar_Syntax_Syntax.Data_ctor))
        | uu____1996 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____1999  -> None)
        (fun uu____2000  -> None) k_global_def
  
let find_all_datacons :
  env -> FStar_Ident.lident -> FStar_Ident.lident Prims.list Prims.option =
  fun env  ->
    fun lid  ->
      let k_global_def lid uu___163_2019 =
        match uu___163_2019 with
        | (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____2024,uu____2025,uu____2026,uu____2027,uu____2028,datas,uu____2030,uu____2031),uu____2032)
            -> Some datas
        | uu____2040 -> None  in
      resolve_in_open_namespaces' env lid (fun uu____2045  -> None)
        (fun uu____2047  -> None) k_global_def
  
let record_cache_aux_with_filter :
  (((Prims.unit -> Prims.unit) * (Prims.unit -> Prims.unit) *
    (Prims.unit -> record_or_dc Prims.list) * (record_or_dc -> Prims.unit) *
    (Prims.unit -> Prims.unit)) * (Prims.unit -> Prims.unit))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push uu____2081 =
    let _0_327 =
      let _0_326 = FStar_List.hd (FStar_ST.read record_cache)  in
      let _0_325 = FStar_ST.read record_cache  in _0_326 :: _0_325  in
    FStar_ST.write record_cache _0_327  in
  let pop uu____2099 =
    let _0_328 = FStar_List.tl (FStar_ST.read record_cache)  in
    FStar_ST.write record_cache _0_328  in
  let peek uu____2113 = FStar_List.hd (FStar_ST.read record_cache)  in
  let insert r =
    let _0_332 =
      let _0_331 = let _0_329 = peek ()  in r :: _0_329  in
      let _0_330 = FStar_List.tl (FStar_ST.read record_cache)  in _0_331 ::
        _0_330
       in
    FStar_ST.write record_cache _0_332  in
  let commit uu____2136 =
    let uu____2137 = FStar_ST.read record_cache  in
    match uu____2137 with
    | hd::uu____2145::tl -> FStar_ST.write record_cache (hd :: tl)
    | uu____2158 -> failwith "Impossible"  in
  let filter uu____2164 =
    let rc = peek ()  in
    pop ();
    (match () with
     | () ->
         let filtered =
           FStar_List.filter
             (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
            in
         let _0_334 =
           let _0_333 = FStar_ST.read record_cache  in filtered :: _0_333  in
         FStar_ST.write record_cache _0_334)
     in
  let aux = (push, pop, peek, insert, commit)  in (aux, filter) 
let record_cache_aux :
  ((Prims.unit -> Prims.unit) * (Prims.unit -> Prims.unit) *
    (Prims.unit -> record_or_dc Prims.list) * (record_or_dc -> Prims.unit) *
    (Prims.unit -> Prims.unit))
  =
  let uu____2242 = record_cache_aux_with_filter  in
  match uu____2242 with | (aux,uu____2280) -> aux 
let filter_record_cache : Prims.unit -> Prims.unit =
  let uu____2319 = record_cache_aux_with_filter  in
  match uu____2319 with | (uu____2342,filter) -> filter 
let push_record_cache : Prims.unit -> Prims.unit =
  let uu____2382 = record_cache_aux  in
  match uu____2382 with
  | (push,uu____2402,uu____2403,uu____2404,uu____2405) -> push 
let pop_record_cache : Prims.unit -> Prims.unit =
  let uu____2430 = record_cache_aux  in
  match uu____2430 with
  | (uu____2449,pop,uu____2451,uu____2452,uu____2453) -> pop 
let peek_record_cache : Prims.unit -> record_or_dc Prims.list =
  let uu____2479 = record_cache_aux  in
  match uu____2479 with
  | (uu____2499,uu____2500,peek,uu____2502,uu____2503) -> peek 
let insert_record_cache : record_or_dc -> Prims.unit =
  let uu____2528 = record_cache_aux  in
  match uu____2528 with
  | (uu____2547,uu____2548,uu____2549,insert,uu____2551) -> insert 
let commit_record_cache : Prims.unit -> Prims.unit =
  let uu____2576 = record_cache_aux  in
  match uu____2576 with
  | (uu____2595,uu____2596,uu____2597,uu____2598,commit) -> commit 
let extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref ->
      FStar_Syntax_Syntax.sigelt -> Prims.unit
  =
  fun e  ->
    fun new_globs  ->
      fun uu___167_2633  ->
        match uu___167_2633 with
        | FStar_Syntax_Syntax.Sig_bundle
            (sigs,uu____2638,uu____2639,uu____2640) ->
            let is_rec =
              FStar_Util.for_some
                (fun uu___164_2651  ->
                   match uu___164_2651 with
                   | FStar_Syntax_Syntax.RecordType _
                     |FStar_Syntax_Syntax.RecordConstructor _ -> true
                   | uu____2654 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___165_2662  ->
                      match uu___165_2662 with
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2664,uu____2665,uu____2666,uu____2667,uu____2668,uu____2669,uu____2670)
                          -> FStar_Ident.lid_equals dc lid
                      | uu____2675 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___166_2677  ->
                    match uu___166_2677 with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (typename,univs,parms,uu____2681,uu____2682,dc::[],tags,uu____2685)
                        ->
                        let uu____2691 =
                          let _0_335 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must _0_335  in
                        (match uu____2691 with
                         | FStar_Syntax_Syntax.Sig_datacon
                             (constrname,uu____2694,t,uu____2696,uu____2697,uu____2698,uu____2699,uu____2700)
                             ->
                             let uu____2705 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____2705 with
                              | (formals,uu____2714) ->
                                  let is_rec = is_rec tags  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____2740  ->
                                            match uu____2740 with
                                            | (x,q) ->
                                                let uu____2748 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____2748
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____2779  ->
                                            match uu____2779 with
                                            | (x,q) ->
                                                let _0_336 =
                                                  if is_rec
                                                  then
                                                    FStar_Syntax_Util.unmangle_field_name
                                                      x.FStar_Syntax_Syntax.ppname
                                                  else
                                                    x.FStar_Syntax_Syntax.ppname
                                                   in
                                                (_0_336,
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
                                      is_record = is_rec
                                    }  in
                                  ((let _0_338 =
                                      let _0_337 = FStar_ST.read new_globs
                                         in
                                      (Record_or_dc record) :: _0_337  in
                                    FStar_ST.write new_globs _0_338);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____2813 =
                                            match uu____2813 with
                                            | (id,uu____2819) ->
                                                let modul =
                                                  (FStar_Ident.lid_of_ids
                                                     constrname.FStar_Ident.ns).FStar_Ident.str
                                                   in
                                                let uu____2825 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____2825 with
                                                 | Some my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let _0_340 =
                                                         let _0_339 =
                                                           FStar_ST.read
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id.FStar_Ident.idText
                                                           _0_339
                                                          in
                                                       FStar_ST.write
                                                         my_exported_ids
                                                         _0_340);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             ((FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                 constrname
                                                                 id).FStar_Ident.ident).FStar_Ident.idText
                                                              in
                                                           let _0_342 =
                                                             let _0_341 =
                                                               FStar_ST.read
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               _0_341
                                                              in
                                                           FStar_ST.write
                                                             my_exported_ids
                                                             _0_342))
                                                 | None  -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____2858 -> ())
                    | uu____2859 -> ()))
        | uu____2860 -> ()
  
let try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname =
        let uu____2873 =
          ((fieldname.FStar_Ident.ns), (fieldname.FStar_Ident.ident))  in
        match uu____2873 with
        | (ns,id) ->
            let _0_344 = peek_record_cache ()  in
            FStar_Util.find_map _0_344
              (fun record  ->
                 let _0_343 =
                   find_in_record ns id record (fun r  -> Cont_ok r)  in
                 option_of_cont (fun uu____2884  -> None) _0_343)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____2886  -> Cont_ignore) (fun uu____2887  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let _0_345 = find_in_cache fn  in
           cont_of_option Cont_ignore _0_345)
        (fun k  -> fun uu____2891  -> k)
  
let try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc Prims.option =
  fun env  ->
    fun fieldname  ->
      let uu____2900 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____2900 with
      | Some r when r.is_record -> Some r
      | uu____2904 -> None
  
let belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____2915 = try_lookup_record_by_field_name env lid  in
        match uu____2915 with
        | Some record' when
            let _0_347 =
              FStar_Ident.text_of_path
                (FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns)
               in
            let _0_346 =
              FStar_Ident.text_of_path
                (FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns)
               in
            _0_347 = _0_346 ->
            let uu____2918 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____2920  -> Cont_ok ())
               in
            (match uu____2918 with
             | Cont_ok uu____2921 -> true
             | uu____2922 -> false)
        | uu____2924 -> false
  
let try_lookup_dc_by_field_name :
  env -> FStar_Ident.lident -> (FStar_Ident.lident * Prims.bool) Prims.option
  =
  fun env  ->
    fun fieldname  ->
      let uu____2935 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____2935 with
      | Some r ->
          Some
            (let _0_349 =
               let _0_348 =
                 FStar_Ident.lid_of_ids
                   (FStar_List.append (r.typename).FStar_Ident.ns
                      [r.constrname])
                  in
               FStar_Ident.set_lid_range _0_348
                 (FStar_Ident.range_of_lid fieldname)
                in
             (_0_349, (r.is_record)))
      | uu____2943 -> None
  
let string_set_ref_new :
  Prims.unit -> Prims.string FStar_Util.set FStar_ST.ref =
  fun uu____2952  ->
    FStar_Util.mk_ref
      (FStar_Util.new_set FStar_Util.compare FStar_Util.hashcode)
  
let exported_id_set_new :
  Prims.unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref
  =
  fun uu____2962  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___168_2971  ->
      match uu___168_2971 with
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
          let filter_scope_mods uu___169_2997 =
            match uu___169_2997 with
            | Rec_binding uu____2998 -> true
            | uu____2999 -> false  in
          let this_env =
            let uu___174_3001 = env  in
            let _0_350 = FStar_List.filter filter_scope_mods env.scope_mods
               in
            {
              curmodule = (uu___174_3001.curmodule);
              curmonad = (uu___174_3001.curmonad);
              modules = (uu___174_3001.modules);
              scope_mods = _0_350;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___174_3001.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___174_3001.sigaccum);
              sigmap = (uu___174_3001.sigmap);
              iface = (uu___174_3001.iface);
              admitted_iface = (uu___174_3001.admitted_iface);
              expect_typ = (uu___174_3001.expect_typ)
            }  in
          let uu____3002 = try_lookup_lid' any_val exclude_if this_env lid
             in
          match uu____3002 with | None  -> true | Some uu____3008 -> false
  
let push_scope_mod : env -> scope_mod -> env =
  fun env  ->
    fun scope_mod  ->
      let uu___175_3019 = env  in
      {
        curmodule = (uu___175_3019.curmodule);
        curmonad = (uu___175_3019.curmonad);
        modules = (uu___175_3019.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___175_3019.exported_ids);
        trans_exported_ids = (uu___175_3019.trans_exported_ids);
        includes = (uu___175_3019.includes);
        sigaccum = (uu___175_3019.sigaccum);
        sigmap = (uu___175_3019.sigmap);
        iface = (uu___175_3019.iface);
        admitted_iface = (uu___175_3019.admitted_iface);
        expect_typ = (uu___175_3019.expect_typ)
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
        let uu____3058 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____3058
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
          | Some (se,uu____3078) ->
              let uu____3081 =
                FStar_Util.find_opt (FStar_Ident.lid_equals l)
                  (FStar_Syntax_Util.lids_of_sigelt se)
                 in
              (match uu____3081 with
               | Some l ->
                   FStar_All.pipe_left FStar_Range.string_of_range
                     (FStar_Ident.range_of_lid l)
               | None  -> "<unknown>")
          | None  -> "<unknown>"  in
        Prims.raise
          (FStar_Errors.Error
             (let _0_351 =
                FStar_Util.format2
                  "Duplicate top-level names [%s]; previously declared at %s"
                  (FStar_Ident.text_of_lid l) r
                 in
              (_0_351, (FStar_Ident.range_of_lid l))))
         in
      let globals = FStar_Util.mk_ref env.scope_mods  in
      let env =
        let uu____3092 =
          match s with
          | FStar_Syntax_Syntax.Sig_let uu____3097 -> (false, true)
          | FStar_Syntax_Syntax.Sig_bundle uu____3106 -> (true, true)
          | uu____3114 -> (false, false)  in
        match uu____3092 with
        | (any_val,exclude_if) ->
            let lids = FStar_Syntax_Util.lids_of_sigelt s  in
            let uu____3119 =
              FStar_Util.find_map lids
                (fun l  ->
                   let uu____3122 =
                     Prims.op_Negation (unique any_val exclude_if env l)  in
                   if uu____3122 then Some l else None)
               in
            (match uu____3119 with
             | Some l when Prims.op_Negation (FStar_Options.interactive ())
                 -> err l
             | uu____3126 ->
                 (extract_record env globals s;
                  (let uu___176_3131 = env  in
                   {
                     curmodule = (uu___176_3131.curmodule);
                     curmonad = (uu___176_3131.curmonad);
                     modules = (uu___176_3131.modules);
                     scope_mods = (uu___176_3131.scope_mods);
                     exported_ids = (uu___176_3131.exported_ids);
                     trans_exported_ids = (uu___176_3131.trans_exported_ids);
                     includes = (uu___176_3131.includes);
                     sigaccum = (s :: (env.sigaccum));
                     sigmap = (uu___176_3131.sigmap);
                     iface = (uu___176_3131.iface);
                     admitted_iface = (uu___176_3131.admitted_iface);
                     expect_typ = (uu___176_3131.expect_typ)
                   })))
         in
      let env =
        let uu___177_3133 = env  in
        let _0_352 = FStar_ST.read globals  in
        {
          curmodule = (uu___177_3133.curmodule);
          curmonad = (uu___177_3133.curmonad);
          modules = (uu___177_3133.modules);
          scope_mods = _0_352;
          exported_ids = (uu___177_3133.exported_ids);
          trans_exported_ids = (uu___177_3133.trans_exported_ids);
          includes = (uu___177_3133.includes);
          sigaccum = (uu___177_3133.sigaccum);
          sigmap = (uu___177_3133.sigmap);
          iface = (uu___177_3133.iface);
          admitted_iface = (uu___177_3133.admitted_iface);
          expect_typ = (uu___177_3133.expect_typ)
        }  in
      let uu____3137 =
        match s with
        | FStar_Syntax_Syntax.Sig_bundle
            (ses,uu____3151,uu____3152,uu____3153) ->
            let _0_353 =
              FStar_List.map
                (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se)) ses
               in
            (env, _0_353)
        | uu____3169 -> (env, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
         in
      match uu____3137 with
      | (env,lss) ->
          (FStar_All.pipe_right lss
             (FStar_List.iter
                (fun uu____3199  ->
                   match uu____3199 with
                   | (lids,se) ->
                       FStar_All.pipe_right lids
                         (FStar_List.iter
                            (fun lid  ->
                               (let _0_355 =
                                  let _0_354 = FStar_ST.read globals  in
                                  (Top_level_def (lid.FStar_Ident.ident)) ::
                                    _0_354
                                   in
                                FStar_ST.write globals _0_355);
                               (match () with
                                | () ->
                                    let modul =
                                      (FStar_Ident.lid_of_ids
                                         lid.FStar_Ident.ns).FStar_Ident.str
                                       in
                                    ((let uu____3218 =
                                        get_exported_id_set env modul  in
                                      match uu____3218 with
                                      | Some f ->
                                          let my_exported_ids =
                                            f Exported_id_term_type  in
                                          let _0_357 =
                                            let _0_356 =
                                              FStar_ST.read my_exported_ids
                                               in
                                            FStar_Util.set_add
                                              (lid.FStar_Ident.ident).FStar_Ident.idText
                                              _0_356
                                             in
                                          FStar_ST.write my_exported_ids
                                            _0_357
                                      | None  -> ());
                                     (match () with
                                      | () ->
                                          FStar_Util.smap_add (sigmap env)
                                            lid.FStar_Ident.str
                                            (se,
                                              (env.iface &&
                                                 (Prims.op_Negation
                                                    env.admitted_iface))))))))));
           (let env =
              let uu___178_3243 = env  in
              let _0_358 = FStar_ST.read globals  in
              {
                curmodule = (uu___178_3243.curmodule);
                curmonad = (uu___178_3243.curmonad);
                modules = (uu___178_3243.modules);
                scope_mods = _0_358;
                exported_ids = (uu___178_3243.exported_ids);
                trans_exported_ids = (uu___178_3243.trans_exported_ids);
                includes = (uu___178_3243.includes);
                sigaccum = (uu___178_3243.sigaccum);
                sigmap = (uu___178_3243.sigmap);
                iface = (uu___178_3243.iface);
                admitted_iface = (uu___178_3243.admitted_iface);
                expect_typ = (uu___178_3243.expect_typ)
              }  in
            env))
  
let push_namespace : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3253 =
        let uu____3256 = resolve_module_name env ns false  in
        match uu____3256 with
        | None  ->
            let modules = env.modules  in
            let uu____3264 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____3270  ->
                      match uu____3270 with
                      | (m,uu____3274) ->
                          FStar_Util.starts_with
                            (Prims.strcat (FStar_Ident.text_of_lid m) ".")
                            (Prims.strcat (FStar_Ident.text_of_lid ns) ".")))
               in
            if uu____3264
            then (ns, Open_namespace)
            else
              Prims.raise
                (FStar_Errors.Error
                   (let _0_359 =
                      FStar_Util.format1 "Namespace %s cannot be found"
                        (FStar_Ident.text_of_lid ns)
                       in
                    (_0_359, (FStar_Ident.range_of_lid ns))))
        | Some ns' -> (ns', Open_module)  in
      match uu____3253 with
      | (ns',kd) -> push_scope_mod env (Open_module_or_namespace (ns', kd))
  
let push_include : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun ns  ->
      let uu____3289 = resolve_module_name env ns false  in
      match uu____3289 with
      | Some ns ->
          let env =
            push_scope_mod env (Open_module_or_namespace (ns, Open_module))
             in
          let curmod = (current_module env).FStar_Ident.str  in
          ((let uu____3295 = FStar_Util.smap_try_find env.includes curmod  in
            match uu____3295 with
            | None  -> ()
            | Some incl ->
                let _0_361 = let _0_360 = FStar_ST.read incl  in ns :: _0_360
                   in
                FStar_ST.write incl _0_361);
           (match () with
            | () ->
                let uu____3314 =
                  get_trans_exported_id_set env ns.FStar_Ident.str  in
                (match uu____3314 with
                 | Some ns_trans_exports ->
                     ((let uu____3327 =
                         let _0_363 = get_exported_id_set env curmod  in
                         let _0_362 = get_trans_exported_id_set env curmod
                            in
                         (_0_363, _0_362)  in
                       match uu____3327 with
                       | (Some cur_exports,Some cur_trans_exports) ->
                           let update_exports k =
                             let ns_ex = FStar_ST.read (ns_trans_exports k)
                                in
                             let ex = cur_exports k  in
                             (let _0_365 =
                                let _0_364 = FStar_ST.read ex  in
                                FStar_Util.set_difference _0_364 ns_ex  in
                              FStar_ST.write ex _0_365);
                             (match () with
                              | () ->
                                  let trans_ex = cur_trans_exports k  in
                                  let _0_367 =
                                    let _0_366 = FStar_ST.read ex  in
                                    FStar_Util.set_union _0_366 ns_ex  in
                                  FStar_ST.write trans_ex _0_367)
                              in
                           FStar_List.iter update_exports
                             all_exported_id_kinds
                       | uu____3391 -> ());
                      (match () with | () -> env))
                 | None  ->
                     Prims.raise
                       (FStar_Errors.Error
                          (let _0_368 =
                             FStar_Util.format1
                               "include: Module %s was not prepared"
                               ns.FStar_Ident.str
                              in
                           (_0_368, (FStar_Ident.range_of_lid ns)))))))
      | uu____3405 ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_369 =
                  FStar_Util.format1 "include: Module %s cannot be found"
                    ns.FStar_Ident.str
                   in
                (_0_369, (FStar_Ident.range_of_lid ns))))
  
let push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____3416 = module_is_defined env l  in
        if uu____3416
        then push_scope_mod env (Module_abbrev (x, l))
        else
          Prims.raise
            (FStar_Errors.Error
               (let _0_370 =
                  FStar_Util.format1 "Module %s cannot be found"
                    (FStar_Ident.text_of_lid l)
                   in
                (_0_370, (FStar_Ident.range_of_lid l))))
  
let check_admits : env -> Prims.unit =
  fun env  ->
    FStar_All.pipe_right env.sigaccum
      (FStar_List.iter
         (fun se  ->
            match se with
            | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,quals,r) ->
                let uu____3429 = try_lookup_lid env l  in
                (match uu____3429 with
                 | None  ->
                     ((let uu____3436 =
                         Prims.op_Negation (FStar_Options.interactive ())  in
                       if uu____3436
                       then
                         FStar_Util.print_string
                           (let _0_372 =
                              FStar_Range.string_of_range
                                (FStar_Ident.range_of_lid l)
                               in
                            let _0_371 = FStar_Syntax_Print.lid_to_string l
                               in
                            FStar_Util.format2
                              "%s: Warning: Admitting %s without a definition\n"
                              _0_372 _0_371)
                       else ());
                      FStar_Util.smap_add (sigmap env) l.FStar_Ident.str
                        ((FStar_Syntax_Syntax.Sig_declare_typ
                            (l, u, t, (FStar_Syntax_Syntax.Assumption ::
                              quals), r)), false))
                 | Some uu____3441 -> ())
            | uu____3446 -> ()))
  
let finish : env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun uu___171_3454  ->
              match uu___171_3454 with
              | FStar_Syntax_Syntax.Sig_bundle
                  (ses,quals,uu____3457,uu____3458) ->
                  if
                    (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                      ||
                      (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun uu___170_3466  ->
                            match uu___170_3466 with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid,uu____3468,uu____3469,uu____3470,uu____3471,uu____3472,uu____3473,uu____3474)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | uu____3481 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____3484,uu____3485,quals,uu____3487) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let
                  ((uu____3493,lbs),r,uu____3496,quals,uu____3498) ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let _0_373 =
                               (((FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                                in
                             FStar_Util.smap_remove (sigmap env) _0_373))
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
                               ((FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
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
              | uu____3535 -> ()));
      (let curmod = (current_module env).FStar_Ident.str  in
       (let uu____3538 =
          let _0_375 = get_exported_id_set env curmod  in
          let _0_374 = get_trans_exported_id_set env curmod  in
          (_0_375, _0_374)  in
        match uu____3538 with
        | (Some cur_ex,Some cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set = FStar_ST.read (cur_ex eikind)  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let _0_377 =
                let _0_376 = FStar_ST.read cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set _0_376  in
              FStar_ST.write cur_trans_ex_set_ref _0_377  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____3593 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___179_3605 = env  in
                  {
                    curmodule = None;
                    curmonad = (uu___179_3605.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___179_3605.exported_ids);
                    trans_exported_ids = (uu___179_3605.trans_exported_ids);
                    includes = (uu___179_3605.includes);
                    sigaccum = [];
                    sigmap = (uu___179_3605.sigmap);
                    iface = (uu___179_3605.iface);
                    admitted_iface = (uu___179_3605.admitted_iface);
                    expect_typ = (uu___179_3605.expect_typ)
                  }))))
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push : env -> env =
  fun env  ->
    push_record_cache ();
    (let _0_379 = let _0_378 = FStar_ST.read stack  in env :: _0_378  in
     FStar_ST.write stack _0_379);
    (let uu___180_3624 = env  in
     let _0_380 = FStar_Util.smap_copy (sigmap env)  in
     {
       curmodule = (uu___180_3624.curmodule);
       curmonad = (uu___180_3624.curmonad);
       modules = (uu___180_3624.modules);
       scope_mods = (uu___180_3624.scope_mods);
       exported_ids = (uu___180_3624.exported_ids);
       trans_exported_ids = (uu___180_3624.trans_exported_ids);
       includes = (uu___180_3624.includes);
       sigaccum = (uu___180_3624.sigaccum);
       sigmap = _0_380;
       iface = (uu___180_3624.iface);
       admitted_iface = (uu___180_3624.admitted_iface);
       expect_typ = (uu___180_3624.expect_typ)
     })
  
let pop : Prims.unit -> env =
  fun uu____3629  ->
    let uu____3630 = FStar_ST.read stack  in
    match uu____3630 with
    | env::tl -> (pop_record_cache (); FStar_ST.write stack tl; env)
    | uu____3643 -> failwith "Impossible: Too many pops"
  
let commit_mark : env -> env =
  fun env  ->
    commit_record_cache ();
    (let uu____3649 = FStar_ST.read stack  in
     match uu____3649 with
     | uu____3654::tl -> (FStar_ST.write stack tl; env)
     | uu____3661 -> failwith "Impossible: Too many pops")
  
let mark : env -> env = fun x  -> push x 
let reset_mark : Prims.unit -> env = fun uu____3668  -> pop () 
let export_interface : FStar_Ident.lident -> env -> env =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____3680 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____3682 -> false  in
      let sm = sigmap env  in
      let env = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____3700 = FStar_Util.smap_try_find sm' k  in
              match uu____3700 with
              | Some (se,true ) when sigelt_in_m se ->
                  (FStar_Util.smap_remove sm' k;
                   (let se =
                      match se with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t,q,r) ->
                          FStar_Syntax_Syntax.Sig_declare_typ
                            (l, u, t, (FStar_Syntax_Syntax.Assumption :: q),
                              r)
                      | uu____3721 -> se  in
                    FStar_Util.smap_add sm' k (se, false)))
              | uu____3724 -> ()));
      env
  
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
          let prep env =
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
            let open_ns =
              if
                (FStar_List.length mname.FStar_Ident.ns) <>
                  (Prims.parse_int "0")
              then
                let ns = FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in ns
                  :: open_ns
              else open_ns  in
            (let _0_381 = exported_id_set_new ()  in
             FStar_Util.smap_add env.exported_ids mname.FStar_Ident.str
               _0_381);
            (match () with
             | () ->
                 ((let _0_382 = exported_id_set_new ()  in
                   FStar_Util.smap_add env.trans_exported_ids
                     mname.FStar_Ident.str _0_382);
                  (match () with
                   | () ->
                       ((let _0_383 = FStar_Util.mk_ref []  in
                         FStar_Util.smap_add env.includes
                           mname.FStar_Ident.str _0_383);
                        (match () with
                         | () ->
                             let uu___181_3779 = env  in
                             let _0_384 =
                               FStar_List.map
                                 (fun lid  ->
                                    Open_module_or_namespace
                                      (lid, Open_namespace)) open_ns
                                in
                             {
                               curmodule = (Some mname);
                               curmonad = (uu___181_3779.curmonad);
                               modules = (uu___181_3779.modules);
                               scope_mods = _0_384;
                               exported_ids = (uu___181_3779.exported_ids);
                               trans_exported_ids =
                                 (uu___181_3779.trans_exported_ids);
                               includes = (uu___181_3779.includes);
                               sigaccum = (uu___181_3779.sigaccum);
                               sigmap = (env.sigmap);
                               iface = intf;
                               admitted_iface = admitted;
                               expect_typ = (uu___181_3779.expect_typ)
                             })))))
             in
          let uu____3781 =
            FStar_All.pipe_right env.modules
              (FStar_Util.find_opt
                 (fun uu____3793  ->
                    match uu____3793 with
                    | (l,uu____3797) -> FStar_Ident.lid_equals l mname))
             in
          match uu____3781 with
          | None  -> let _0_385 = prep env  in (_0_385, false)
          | Some (uu____3802,m) ->
              ((let uu____3807 =
                  (Prims.op_Negation (FStar_Options.interactive ())) &&
                    ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                       || intf)
                   in
                if uu____3807
                then
                  Prims.raise
                    (FStar_Errors.Error
                       (let _0_386 =
                          FStar_Util.format1
                            "Duplicate module or interface name: %s"
                            mname.FStar_Ident.str
                           in
                        (_0_386, (FStar_Ident.range_of_lid mname))))
                else ());
               (let _0_387 = prep (push env)  in (_0_387, true)))
  
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
          let uu___182_3816 = env  in
          {
            curmodule = (uu___182_3816.curmodule);
            curmonad = (Some mname);
            modules = (uu___182_3816.modules);
            scope_mods = (uu___182_3816.scope_mods);
            exported_ids = (uu___182_3816.exported_ids);
            trans_exported_ids = (uu___182_3816.trans_exported_ids);
            includes = (uu___182_3816.includes);
            sigaccum = (uu___182_3816.sigaccum);
            sigmap = (uu___182_3816.sigmap);
            iface = (uu___182_3816.iface);
            admitted_iface = (uu___182_3816.admitted_iface);
            expect_typ = (uu___182_3816.expect_typ)
          }
  
let fail_or env lookup lid =
  let uu____3841 = lookup lid  in
  match uu____3841 with
  | None  ->
      let opened_modules =
        FStar_List.map
          (fun uu____3847  ->
             match uu____3847 with
             | (lid,uu____3851) -> FStar_Ident.text_of_lid lid) env.modules
         in
      let msg =
        FStar_Util.format1 "Identifier not found: [%s]"
          (FStar_Ident.text_of_lid lid)
         in
      let msg =
        if (FStar_List.length lid.FStar_Ident.ns) = (Prims.parse_int "0")
        then msg
        else
          (let modul =
             let _0_388 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
             FStar_Ident.set_lid_range _0_388 (FStar_Ident.range_of_lid lid)
              in
           let uu____3858 = resolve_module_name env modul true  in
           match uu____3858 with
           | None  ->
               let opened_modules = FStar_String.concat ", " opened_modules
                  in
               FStar_Util.format3
                 "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str opened_modules
           | Some modul' when
               Prims.op_Negation
                 (FStar_List.existsb (fun m  -> m = modul'.FStar_Ident.str)
                    opened_modules)
               ->
               let opened_modules = FStar_String.concat ", " opened_modules
                  in
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 opened_modules
           | Some modul' ->
               FStar_Util.format4
                 "%s\nModule %s resolved into %s, definition %s not found"
                 msg modul.FStar_Ident.str modul'.FStar_Ident.str
                 (lid.FStar_Ident.ident).FStar_Ident.idText)
         in
      Prims.raise (FStar_Errors.Error (msg, (FStar_Ident.range_of_lid lid)))
  | Some r -> r 
let fail_or2 lookup id =
  let uu____3885 = lookup id  in
  match uu____3885 with
  | None  ->
      Prims.raise
        (FStar_Errors.Error
           ((Prims.strcat "Identifier not found ["
               (Prims.strcat id.FStar_Ident.idText "]")),
             (id.FStar_Ident.idRange)))
  | Some r -> r 