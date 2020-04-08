open Prims
type ty_binding =
  {
  ty_b_name: FStar_Extraction_ML_Syntax.mlident ;
  ty_b_ty: FStar_Extraction_ML_Syntax.mlty }
let (__proj__Mkty_binding__item__ty_b_name :
  ty_binding -> FStar_Extraction_ML_Syntax.mlident) =
  fun projectee  ->
    match projectee with | { ty_b_name; ty_b_ty;_} -> ty_b_name
  
let (__proj__Mkty_binding__item__ty_b_ty :
  ty_binding -> FStar_Extraction_ML_Syntax.mlty) =
  fun projectee  -> match projectee with | { ty_b_name; ty_b_ty;_} -> ty_b_ty 
type exp_binding =
  {
  exp_b_name: FStar_Extraction_ML_Syntax.mlident ;
  exp_b_expr: FStar_Extraction_ML_Syntax.mlexpr ;
  exp_b_tscheme: FStar_Extraction_ML_Syntax.mltyscheme ;
  exp_b_inst_ok: Prims.bool }
let (__proj__Mkexp_binding__item__exp_b_name :
  exp_binding -> FStar_Extraction_ML_Syntax.mlident) =
  fun projectee  ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} -> exp_b_name
  
let (__proj__Mkexp_binding__item__exp_b_expr :
  exp_binding -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun projectee  ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} -> exp_b_expr
  
let (__proj__Mkexp_binding__item__exp_b_tscheme :
  exp_binding -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun projectee  ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} ->
        exp_b_tscheme
  
let (__proj__Mkexp_binding__item__exp_b_inst_ok : exp_binding -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} ->
        exp_b_inst_ok
  
type ty_or_exp_b = (ty_binding,exp_binding) FStar_Util.either
type binding =
  | Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b) 
  | Fv of (FStar_Syntax_Syntax.fv * exp_binding) 
let (uu___is_Bv : binding -> Prims.bool) =
  fun projectee  -> match projectee with | Bv _0 -> true | uu____159 -> false 
let (__proj__Bv__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)) =
  fun projectee  -> match projectee with | Bv _0 -> _0 
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee  -> match projectee with | Fv _0 -> true | uu____194 -> false 
let (__proj__Fv__item___0 :
  binding -> (FStar_Syntax_Syntax.fv * exp_binding)) =
  fun projectee  -> match projectee with | Fv _0 -> _0 
type tydef =
  {
  tydef_fv: FStar_Syntax_Syntax.fv ;
  tydef_mlmodule_name: FStar_Extraction_ML_Syntax.mlsymbol Prims.list ;
  tydef_name: FStar_Extraction_ML_Syntax.mlsymbol ;
  tydef_def: FStar_Extraction_ML_Syntax.mltyscheme }
let (__proj__Mktydef__item__tydef_fv : tydef -> FStar_Syntax_Syntax.fv) =
  fun projectee  ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_def;_} -> tydef_fv
  
let (__proj__Mktydef__item__tydef_mlmodule_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol Prims.list) =
  fun projectee  ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_def;_} ->
        tydef_mlmodule_name
  
let (__proj__Mktydef__item__tydef_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun projectee  ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_def;_} -> tydef_name
  
let (__proj__Mktydef__item__tydef_def :
  tydef -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun projectee  ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_def;_} -> tydef_def
  
let (tydef_fv : tydef -> FStar_Syntax_Syntax.fv) = fun td  -> td.tydef_fv 
let (tydef_def : tydef -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun td  -> td.tydef_def 
let (tydef_mlpath : tydef -> FStar_Extraction_ML_Syntax.mlpath) =
  fun td  -> ((td.tydef_mlmodule_name), (td.tydef_name)) 
type uenv =
  {
  env_tcenv: FStar_TypeChecker_Env.env ;
  env_bindings: binding Prims.list ;
  env_mlident_map: FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap ;
  mlpath_of_lid: FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap ;
  env_fieldname_map: FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap ;
  mlpath_of_fieldname: FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap ;
  tydefs: tydef Prims.list ;
  type_names:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list ;
  currentModule: FStar_Extraction_ML_Syntax.mlpath }
let (__proj__Mkuenv__item__env_tcenv : uenv -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_tcenv
  
let (__proj__Mkuenv__item__env_bindings : uenv -> binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_bindings
  
let (__proj__Mkuenv__item__env_mlident_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_mlident_map
  
let (__proj__Mkuenv__item__mlpath_of_lid :
  uenv -> FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> mlpath_of_lid
  
let (__proj__Mkuenv__item__env_fieldname_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_fieldname_map
  
let (__proj__Mkuenv__item__mlpath_of_fieldname :
  uenv -> FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> mlpath_of_fieldname
  
let (__proj__Mkuenv__item__tydefs : uenv -> tydef Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> tydefs
  
let (__proj__Mkuenv__item__type_names :
  uenv ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> type_names
  
let (__proj__Mkuenv__item__currentModule :
  uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> currentModule
  
let (tcenv_of_uenv : uenv -> FStar_TypeChecker_Env.env) =
  fun u  -> u.env_tcenv 
let (set_tcenv : uenv -> FStar_TypeChecker_Env.env -> uenv) =
  fun u  ->
    fun t  ->
      let uu___70_762 = u  in
      {
        env_tcenv = t;
        env_bindings = (uu___70_762.env_bindings);
        env_mlident_map = (uu___70_762.env_mlident_map);
        mlpath_of_lid = (uu___70_762.mlpath_of_lid);
        env_fieldname_map = (uu___70_762.env_fieldname_map);
        mlpath_of_fieldname = (uu___70_762.mlpath_of_fieldname);
        tydefs = (uu___70_762.tydefs);
        type_names = (uu___70_762.type_names);
        currentModule = (uu___70_762.currentModule)
      }
  
let (current_module_of_uenv : uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun u  -> u.currentModule 
let (set_current_module : uenv -> FStar_Extraction_ML_Syntax.mlpath -> uenv)
  =
  fun u  ->
    fun m  ->
      let uu___78_780 = u  in
      {
        env_tcenv = (uu___78_780.env_tcenv);
        env_bindings = (uu___78_780.env_bindings);
        env_mlident_map = (uu___78_780.env_mlident_map);
        mlpath_of_lid = (uu___78_780.mlpath_of_lid);
        env_fieldname_map = (uu___78_780.env_fieldname_map);
        mlpath_of_fieldname = (uu___78_780.mlpath_of_fieldname);
        tydefs = (uu___78_780.tydefs);
        type_names = (uu___78_780.type_names);
        currentModule = m
      }
  
let (bindings_of_uenv : uenv -> binding Prims.list) =
  fun u  -> u.env_bindings 
let (debug : uenv -> (unit -> unit) -> unit) =
  fun g  ->
    fun f  ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule  in
      let uu____807 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction")  in
      if uu____807 then f () else ()
  
let (print_mlpath_map : uenv -> Prims.string) =
  fun g  ->
    let string_of_mlpath mlp =
      Prims.op_Hat
        (FStar_String.concat "." (FStar_Pervasives_Native.fst mlp))
        (Prims.op_Hat "." (FStar_Pervasives_Native.snd mlp))
       in
    let entries =
      FStar_Util.psmap_fold g.mlpath_of_lid
        (fun key  ->
           fun value  ->
             fun entries  ->
               let uu____871 =
                 FStar_Util.format2 "%s -> %s" key (string_of_mlpath value)
                  in
               uu____871 :: entries) []
       in
    FStar_String.concat "\n" entries
  
let (try_lookup_fv :
  uenv ->
    FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun g  ->
    fun fv  ->
      FStar_Util.find_map g.env_bindings
        (fun uu___0_895  ->
           match uu___0_895 with
           | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____900 -> FStar_Pervasives_Native.None)
  
let (lookup_fv : uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun g  ->
    fun fv  ->
      let uu____912 = try_lookup_fv g fv  in
      match uu____912 with
      | FStar_Pervasives_Native.None  ->
          let uu____915 =
            let uu____917 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
               in
            let uu____919 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____917
              uu____919
             in
          failwith uu____915
      | FStar_Pervasives_Native.Some y -> y
  
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___1_940  ->
             match uu___1_940 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____945 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____946 =
            let uu____948 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange
               in
            let uu____950 = FStar_Syntax_Print.bv_to_string bv  in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____948
              uu____950
             in
          failwith uu____946
      | FStar_Pervasives_Native.Some y -> y
  
let (lookup_term :
  uenv ->
    FStar_Syntax_Syntax.term ->
      (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual
        FStar_Pervasives_Native.option))
  =
  fun g  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____978 = lookup_bv g x  in
          (uu____978, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar x ->
          let uu____982 =
            let uu____983 = lookup_fv g x  in FStar_Util.Inr uu____983  in
          (uu____982, (x.FStar_Syntax_Syntax.fv_qual))
      | uu____986 -> failwith "Impossible: lookup_term for a non-name"
  
let (lookup_ty : uenv -> FStar_Syntax_Syntax.bv -> ty_binding) =
  fun g  ->
    fun x  ->
      let uu____1005 = lookup_bv g x  in
      match uu____1005 with
      | FStar_Util.Inl ty -> ty
      | uu____1007 -> failwith "Expected a type name"
  
let (lookup_ty_const :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun uu____1021  ->
      match uu____1021 with
      | (module_name,ty_name) ->
          FStar_Util.find_map env.tydefs
            (fun tydef1  ->
               if
                 (ty_name = tydef1.tydef_name) &&
                   (module_name = tydef1.tydef_mlmodule_name)
               then FStar_Pervasives_Native.Some (tydef1.tydef_def)
               else FStar_Pervasives_Native.None)
  
let (mlpath_of_lident :
  uenv -> FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlpath) =
  fun g  ->
    fun x  ->
      let uu____1058 =
        FStar_Util.psmap_try_find g.mlpath_of_lid x.FStar_Ident.str  in
      match uu____1058 with
      | FStar_Pervasives_Native.None  ->
          (debug g
             (fun uu____1065  ->
                FStar_Util.print1 "Identifier not found: %s"
                  x.FStar_Ident.str;
                (let uu____1068 = print_mlpath_map g  in
                 FStar_Util.print1 "Env is \n%s\n" uu____1068));
           failwith (Prims.op_Hat "Identifier not found: " x.FStar_Ident.str))
      | FStar_Pervasives_Native.Some mlp -> mlp
  
let (is_type_name : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g  ->
    fun fv  ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some
           (fun uu____1099  ->
              match uu____1099 with
              | (x,uu____1106) -> FStar_Syntax_Syntax.fv_eq fv x))
  
let (is_fv_type : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g  ->
    fun fv  ->
      (is_type_name g fv) ||
        (FStar_All.pipe_right g.tydefs
           (FStar_Util.for_some
              (fun tydef1  -> FStar_Syntax_Syntax.fv_eq fv tydef1.tydef_fv)))
  
let (lookup_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      FStar_Extraction_ML_Syntax.mlpath)
  =
  fun g  ->
    fun uu____1138  ->
      match uu____1138 with
      | (type_name,fn) ->
          let key =
            FStar_Ident.lid_of_ids
              (FStar_List.append type_name.FStar_Ident.ns [fn])
             in
          let uu____1146 =
            FStar_Util.psmap_try_find g.mlpath_of_fieldname
              key.FStar_Ident.str
             in
          (match uu____1146 with
           | FStar_Pervasives_Native.None  ->
               failwith
                 (Prims.op_Hat "Field name not found: " key.FStar_Ident.str)
           | FStar_Pervasives_Native.Some mlp -> mlp)
  
let (initial_mlident_map : unit -> Prims.string FStar_Util.psmap) =
  let map = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  fun uu____1175  ->
    let uu____1176 = FStar_ST.op_Bang map  in
    match uu____1176 with
    | FStar_Pervasives_Native.Some m -> m
    | FStar_Pervasives_Native.None  ->
        let m =
          let uu____1228 =
            let uu____1232 = FStar_Options.codegen ()  in
            match uu____1232 with
            | FStar_Pervasives_Native.Some (FStar_Options.FSharp ) ->
                FStar_Extraction_ML_Syntax.fsharpkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.OCaml ) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Plugin ) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Kremlin ) ->
                FStar_Extraction_ML_Syntax.kremlin_keywords ()
            | FStar_Pervasives_Native.None  -> []  in
          let uu____1240 = FStar_Util.psmap_empty ()  in
          FStar_List.fold_right
            (fun x  -> fun m  -> FStar_Util.psmap_add m x "") uu____1228
            uu____1240
           in
        (FStar_ST.op_Colon_Equals map (FStar_Pervasives_Native.Some m); m)
  
let (rename_conventional : Prims.string -> Prims.bool -> Prims.string) =
  fun s  ->
    fun is_local_type_variable  ->
      let cs = FStar_String.list_of_string s  in
      let sanitize_typ uu____1321 =
        let valid_rest c = FStar_Util.is_letter_or_digit c  in
        let aux cs1 =
          FStar_List.map
            (fun x  ->
               let uu____1352 = valid_rest x  in
               if uu____1352 then x else 117) cs1
           in
        let uu____1359 =
          let uu____1361 = FStar_List.hd cs  in uu____1361 = 39  in
        if uu____1359
        then
          let uu____1370 = FStar_List.hd cs  in
          let uu____1373 =
            let uu____1377 = FStar_List.tail cs  in aux uu____1377  in
          uu____1370 :: uu____1373
        else (let uu____1385 = aux cs  in 39 :: uu____1385)  in
      let sanitize_term uu____1399 =
        let valid c =
          ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39)  in
        let cs' =
          FStar_List.fold_right
            (fun c  ->
               fun cs1  ->
                 let uu____1430 =
                   let uu____1434 = valid c  in
                   if uu____1434 then [c] else [95; 95]  in
                 FStar_List.append uu____1430 cs1) cs []
           in
        match cs' with
        | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
        | uu____1466 -> cs  in
      let uu____1470 =
        if is_local_type_variable then sanitize_typ () else sanitize_term ()
         in
      FStar_String.string_of_list uu____1470
  
let (root_name_of_bv :
  FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlident) =
  fun x  ->
    let uu____1488 =
      (FStar_Util.starts_with
         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        || (FStar_Syntax_Syntax.is_null_bv x)
       in
    if uu____1488
    then
      let uu____1492 =
        let uu____1494 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.op_Hat "_" uu____1494  in
      Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        uu____1492
    else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (find_uniq :
  Prims.string FStar_Util.psmap ->
    Prims.string ->
      Prims.bool -> (Prims.string * Prims.string FStar_Util.psmap))
  =
  fun ml_ident_map  ->
    fun root_name  ->
      fun is_local_type_variable  ->
        let rec aux i root_name1 =
          let target_mlident =
            if i = Prims.int_zero
            then root_name1
            else
              (let uu____1564 = FStar_Util.string_of_int i  in
               Prims.op_Hat root_name1 uu____1564)
             in
          let uu____1566 =
            FStar_Util.psmap_try_find ml_ident_map target_mlident  in
          match uu____1566 with
          | FStar_Pervasives_Native.Some x ->
              aux (i + Prims.int_one) root_name1
          | FStar_Pervasives_Native.None  ->
              let map = FStar_Util.psmap_add ml_ident_map target_mlident ""
                 in
              (target_mlident, map)
           in
        let mlident = rename_conventional root_name is_local_type_variable
           in
        if is_local_type_variable
        then
          let uu____1605 =
            let uu____1614 = FStar_Util.substring_from mlident Prims.int_one
               in
            aux Prims.int_zero uu____1614  in
          match uu____1605 with | (nm,map) -> ((Prims.op_Hat "'" nm), map)
        else aux Prims.int_zero mlident
  
let (mlns_of_lid : FStar_Ident.lident -> Prims.string Prims.list) =
  fun x  ->
    FStar_List.map (fun x1  -> x1.FStar_Ident.idText) x.FStar_Ident.ns
  
let (new_mlpath_of_lident :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g  ->
    fun x  ->
      let uu____1675 =
        let uu____1680 =
          FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid  in
        if uu____1680
        then (([], ((x.FStar_Ident.ident).FStar_Ident.idText)), g)
        else
          (let uu____1694 =
             find_uniq g.env_mlident_map
               (x.FStar_Ident.ident).FStar_Ident.idText false
              in
           match uu____1694 with
           | (name,map) ->
               let g1 =
                 let uu___243_1719 = g  in
                 {
                   env_tcenv = (uu___243_1719.env_tcenv);
                   env_bindings = (uu___243_1719.env_bindings);
                   env_mlident_map = map;
                   mlpath_of_lid = (uu___243_1719.mlpath_of_lid);
                   env_fieldname_map = (uu___243_1719.env_fieldname_map);
                   mlpath_of_fieldname = (uu___243_1719.mlpath_of_fieldname);
                   tydefs = (uu___243_1719.tydefs);
                   type_names = (uu___243_1719.type_names);
                   currentModule = (uu___243_1719.currentModule)
                 }  in
               let uu____1720 =
                 let uu____1721 = mlns_of_lid x  in (uu____1721, name)  in
               (uu____1720, g1))
         in
      match uu____1675 with
      | (mlp,g1) ->
          let g2 =
            let uu___249_1736 = g1  in
            let uu____1737 =
              FStar_Util.psmap_add g1.mlpath_of_lid x.FStar_Ident.str mlp  in
            {
              env_tcenv = (uu___249_1736.env_tcenv);
              env_bindings = (uu___249_1736.env_bindings);
              env_mlident_map = (uu___249_1736.env_mlident_map);
              mlpath_of_lid = uu____1737;
              env_fieldname_map = (uu___249_1736.env_fieldname_map);
              mlpath_of_fieldname = (uu___249_1736.mlpath_of_fieldname);
              tydefs = (uu___249_1736.tydefs);
              type_names = (uu___249_1736.type_names);
              currentModule = (uu___249_1736.currentModule)
            }  in
          (mlp, g2)
  
let (extend_ty : uenv -> FStar_Syntax_Syntax.bv -> Prims.bool -> uenv) =
  fun g  ->
    fun a  ->
      fun map_to_top  ->
        let is_local_type_variable = Prims.op_Negation map_to_top  in
        let uu____1760 =
          let uu____1769 = root_name_of_bv a  in
          find_uniq g.env_mlident_map uu____1769 is_local_type_variable  in
        match uu____1760 with
        | (ml_a,mlident_map) ->
            let mapped_to =
              if map_to_top
              then FStar_Extraction_ML_Syntax.MLTY_Top
              else FStar_Extraction_ML_Syntax.MLTY_Var ml_a  in
            let gamma =
              (Bv
                 (a,
                   (FStar_Util.Inl { ty_b_name = ml_a; ty_b_ty = mapped_to })))
              :: (g.env_bindings)  in
            let tcenv = FStar_TypeChecker_Env.push_bv g.env_tcenv a  in
            let uu___266_1789 = g  in
            {
              env_tcenv = tcenv;
              env_bindings = gamma;
              env_mlident_map = mlident_map;
              mlpath_of_lid = (uu___266_1789.mlpath_of_lid);
              env_fieldname_map = (uu___266_1789.env_fieldname_map);
              mlpath_of_fieldname = (uu___266_1789.mlpath_of_fieldname);
              tydefs = (uu___266_1789.tydefs);
              type_names = (uu___266_1789.type_names);
              currentModule = (uu___266_1789.currentModule)
            }
  
let (extend_bv :
  uenv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool ->
          Prims.bool ->
            Prims.bool ->
              (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g  ->
    fun x  ->
      fun t_x  ->
        fun add_unit  ->
          fun is_rec  ->
            fun mk_unit  ->
              let ml_ty =
                match t_x with
                | ([],t) -> t
                | uu____1844 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let uu____1845 =
                let uu____1854 = root_name_of_bv x  in
                find_uniq g.env_mlident_map uu____1854 false  in
              match uu____1845 with
              | (mlident,mlident_map) ->
                  let mlx = FStar_Extraction_ML_Syntax.MLE_Var mlident  in
                  let mlx1 =
                    if mk_unit
                    then FStar_Extraction_ML_Syntax.ml_unit
                    else
                      if add_unit
                      then
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top)
                          (FStar_Extraction_ML_Syntax.MLE_App
                             ((FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top mlx),
                               [FStar_Extraction_ML_Syntax.ml_unit]))
                      else FStar_Extraction_ML_Syntax.with_ty ml_ty mlx
                     in
                  let t_x1 =
                    if add_unit
                    then FStar_Extraction_ML_Syntax.pop_unit t_x
                    else t_x  in
                  let exp_binding1 =
                    {
                      exp_b_name = mlident;
                      exp_b_expr = mlx1;
                      exp_b_tscheme = t_x1;
                      exp_b_inst_ok = false
                    }  in
                  let gamma = (Bv (x, (FStar_Util.Inr exp_binding1))) ::
                    (g.env_bindings)  in
                  let tcenv =
                    let uu____1894 = FStar_Syntax_Syntax.binders_of_list [x]
                       in
                    FStar_TypeChecker_Env.push_binders g.env_tcenv uu____1894
                     in
                  ((let uu___294_1897 = g  in
                    {
                      env_tcenv = tcenv;
                      env_bindings = gamma;
                      env_mlident_map = mlident_map;
                      mlpath_of_lid = (uu___294_1897.mlpath_of_lid);
                      env_fieldname_map = (uu___294_1897.env_fieldname_map);
                      mlpath_of_fieldname =
                        (uu___294_1897.mlpath_of_fieldname);
                      tydefs = (uu___294_1897.tydefs);
                      type_names = (uu___294_1897.type_names);
                      currentModule = (uu___294_1897.currentModule)
                    }), mlident, exp_binding1)
  
let (new_mlident : uenv -> (uenv * FStar_Extraction_ML_Syntax.mlident)) =
  fun g  ->
    let ml_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
    let x =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.tun
       in
    let uu____1916 =
      extend_bv g x ([], FStar_Extraction_ML_Syntax.MLTY_Top) false false
        false
       in
    match uu____1916 with | (g1,id,uu____1935) -> (g1, id)
  
let (extend_fv :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool ->
          Prims.bool ->
            (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g  ->
    fun x  ->
      fun t_x  ->
        fun add_unit  ->
          fun is_rec  ->
            let rec mltyFvars t =
              match t with
              | FStar_Extraction_ML_Syntax.MLTY_Var x1 -> [x1]
              | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
                  let uu____2002 = mltyFvars t1  in
                  let uu____2006 = mltyFvars t2  in
                  FStar_List.append uu____2002 uu____2006
              | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
                  FStar_List.collect mltyFvars args
              | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
                  FStar_List.collect mltyFvars ts
              | FStar_Extraction_ML_Syntax.MLTY_Top  -> []
              | FStar_Extraction_ML_Syntax.MLTY_Erased  -> []  in
            let rec subsetMlidents la lb =
              match la with
              | h::tla ->
                  (FStar_List.contains h lb) && (subsetMlidents tla lb)
              | [] -> true  in
            let tySchemeIsClosed tys =
              let uu____2067 = mltyFvars (FStar_Pervasives_Native.snd tys)
                 in
              subsetMlidents uu____2067 (FStar_Pervasives_Native.fst tys)  in
            let uu____2071 = tySchemeIsClosed t_x  in
            if uu____2071
            then
              let ml_ty =
                match t_x with
                | ([],t) -> t
                | uu____2084 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let uu____2085 =
                new_mlpath_of_lident g
                  (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              match uu____2085 with
              | (mlpath,g1) ->
                  let mlsymbol = FStar_Pervasives_Native.snd mlpath  in
                  let mly = FStar_Extraction_ML_Syntax.MLE_Name mlpath  in
                  let mly1 =
                    if add_unit
                    then
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top)
                        (FStar_Extraction_ML_Syntax.MLE_App
                           ((FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.MLTY_Top mly),
                             [FStar_Extraction_ML_Syntax.ml_unit]))
                    else FStar_Extraction_ML_Syntax.with_ty ml_ty mly  in
                  let t_x1 =
                    if add_unit
                    then FStar_Extraction_ML_Syntax.pop_unit t_x
                    else t_x  in
                  let exp_binding1 =
                    {
                      exp_b_name = mlsymbol;
                      exp_b_expr = mly1;
                      exp_b_tscheme = t_x1;
                      exp_b_inst_ok = false
                    }  in
                  let gamma = (Fv (x, exp_binding1)) :: (g1.env_bindings)  in
                  let mlident_map =
                    FStar_Util.psmap_add g1.env_mlident_map mlsymbol ""  in
                  ((let uu___358_2129 = g1  in
                    {
                      env_tcenv = (uu___358_2129.env_tcenv);
                      env_bindings = gamma;
                      env_mlident_map = mlident_map;
                      mlpath_of_lid = (uu___358_2129.mlpath_of_lid);
                      env_fieldname_map = (uu___358_2129.env_fieldname_map);
                      mlpath_of_fieldname =
                        (uu___358_2129.mlpath_of_fieldname);
                      tydefs = (uu___358_2129.tydefs);
                      type_names = (uu___358_2129.type_names);
                      currentModule = (uu___358_2129.currentModule)
                    }), mlsymbol, exp_binding1)
            else failwith "freevars found"
  
let (extend_lb :
  uenv ->
    FStar_Syntax_Syntax.lbname ->
      FStar_Syntax_Syntax.typ ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          Prims.bool ->
            Prims.bool ->
              (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g  ->
    fun l  ->
      fun t  ->
        fun t_x  ->
          fun add_unit  ->
            fun is_rec  ->
              match l with
              | FStar_Util.Inl x -> extend_bv g x t_x add_unit is_rec false
              | FStar_Util.Inr f -> extend_fv g f t_x add_unit is_rec
  
let (extend_tydef :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        (tydef * FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g  ->
    fun fv  ->
      fun ts  ->
        let uu____2220 =
          new_mlpath_of_lident g
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____2220 with
        | (name,g1) ->
            let tydef1 =
              {
                tydef_fv = fv;
                tydef_mlmodule_name = (FStar_Pervasives_Native.fst name);
                tydef_name = (FStar_Pervasives_Native.snd name);
                tydef_def = ts
              }  in
            (tydef1, name,
              (let uu___386_2243 = g1  in
               {
                 env_tcenv = (uu___386_2243.env_tcenv);
                 env_bindings = (uu___386_2243.env_bindings);
                 env_mlident_map = (uu___386_2243.env_mlident_map);
                 mlpath_of_lid = (uu___386_2243.mlpath_of_lid);
                 env_fieldname_map = (uu___386_2243.env_fieldname_map);
                 mlpath_of_fieldname = (uu___386_2243.mlpath_of_fieldname);
                 tydefs = (tydef1 :: (g1.tydefs));
                 type_names = ((fv, name) :: (g1.type_names));
                 currentModule = (uu___386_2243.currentModule)
               }))
  
let (extend_type_name :
  uenv ->
    FStar_Syntax_Syntax.fv -> (FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g  ->
    fun fv  ->
      let uu____2267 =
        new_mlpath_of_lident g
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      match uu____2267 with
      | (name,g1) ->
          (name,
            (let uu___395_2279 = g1  in
             {
               env_tcenv = (uu___395_2279.env_tcenv);
               env_bindings = (uu___395_2279.env_bindings);
               env_mlident_map = (uu___395_2279.env_mlident_map);
               mlpath_of_lid = (uu___395_2279.mlpath_of_lid);
               env_fieldname_map = (uu___395_2279.env_fieldname_map);
               mlpath_of_fieldname = (uu___395_2279.mlpath_of_fieldname);
               tydefs = (uu___395_2279.tydefs);
               type_names = ((fv, name) :: (g1.type_names));
               currentModule = (uu___395_2279.currentModule)
             }))
  
let (extend_with_monad_op_name :
  uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      Prims.string ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident *
            exp_binding * uenv))
  =
  fun g  ->
    fun ed  ->
      fun nm  ->
        fun ts  ->
          let lid =
            let uu____2316 = FStar_Ident.id_of_text nm  in
            FStar_Syntax_Util.mk_field_projector_name_from_ident
              ed.FStar_Syntax_Syntax.mname uu____2316
             in
          let uu____2317 =
            let uu____2325 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            extend_fv g uu____2325 ts false false  in
          match uu____2317 with
          | (g1,mlid,exp_b) ->
              let mlp =
                let uu____2350 = mlns_of_lid lid  in (uu____2350, mlid)  in
              (mlp, lid, exp_b, g1)
  
let (extend_with_action_name :
  uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.action ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident *
            exp_binding * uenv))
  =
  fun g  ->
    fun ed  ->
      fun a  ->
        fun ts  ->
          let nm =
            ((a.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
             in
          let module_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ns  in
          let lid =
            let uu____2393 =
              let uu____2396 =
                let uu____2399 = FStar_Ident.id_of_text nm  in [uu____2399]
                 in
              FStar_List.append module_name uu____2396  in
            FStar_Ident.lid_of_ids uu____2393  in
          let uu____2400 =
            let uu____2408 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            extend_fv g uu____2408 ts false false  in
          match uu____2400 with
          | (g1,mlid,exp_b) ->
              let mlp =
                let uu____2433 = mlns_of_lid lid  in (uu____2433, mlid)  in
              (mlp, lid, exp_b, g1)
  
let (extend_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      (FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g  ->
    fun uu____2459  ->
      match uu____2459 with
      | (type_name,fn) ->
          let key =
            FStar_Ident.lid_of_ids
              (FStar_List.append type_name.FStar_Ident.ns [fn])
             in
          let uu____2471 =
            find_uniq g.env_fieldname_map fn.FStar_Ident.idText false  in
          (match uu____2471 with
           | (name,fieldname_map) ->
               let ns = mlns_of_lid key  in
               let mlp = (ns, name)  in
               let g1 =
                 let uu___435_2513 = g  in
                 let uu____2514 =
                   FStar_Util.psmap_add g.mlpath_of_fieldname
                     key.FStar_Ident.str mlp
                    in
                 {
                   env_tcenv = (uu___435_2513.env_tcenv);
                   env_bindings = (uu___435_2513.env_bindings);
                   env_mlident_map = (uu___435_2513.env_mlident_map);
                   mlpath_of_lid = (uu___435_2513.mlpath_of_lid);
                   env_fieldname_map = fieldname_map;
                   mlpath_of_fieldname = uu____2514;
                   tydefs = (uu___435_2513.tydefs);
                   type_names = (uu___435_2513.type_names);
                   currentModule = (uu___435_2513.currentModule)
                 }  in
               (mlp, g1))
  
let (extend_with_module_name :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g  ->
    fun m  ->
      let ns = mlns_of_lid m  in
      let p = (m.FStar_Ident.ident).FStar_Ident.idText  in ((ns, p), g)
  
let (exit_module : uenv -> uenv) =
  fun g  ->
    let uu___443_2548 = g  in
    let uu____2549 = initial_mlident_map ()  in
    let uu____2553 = initial_mlident_map ()  in
    {
      env_tcenv = (uu___443_2548.env_tcenv);
      env_bindings = (uu___443_2548.env_bindings);
      env_mlident_map = uu____2549;
      mlpath_of_lid = (uu___443_2548.mlpath_of_lid);
      env_fieldname_map = uu____2553;
      mlpath_of_fieldname = (uu___443_2548.mlpath_of_fieldname);
      tydefs = (uu___443_2548.tydefs);
      type_names = (uu___443_2548.type_names);
      currentModule = (uu___443_2548.currentModule)
    }
  
let (new_uenv : FStar_TypeChecker_Env.env -> uenv) =
  fun e  ->
    let env =
      let uu____2564 = initial_mlident_map ()  in
      let uu____2568 = FStar_Util.psmap_empty ()  in
      let uu____2571 = initial_mlident_map ()  in
      let uu____2575 = FStar_Util.psmap_empty ()  in
      {
        env_tcenv = e;
        env_bindings = [];
        env_mlident_map = uu____2564;
        mlpath_of_lid = uu____2568;
        env_fieldname_map = uu____2571;
        mlpath_of_fieldname = uu____2575;
        tydefs = [];
        type_names = [];
        currentModule = ([], "")
      }  in
    let a = "'a"  in
    let failwith_ty =
      ([a],
        (FStar_Extraction_ML_Syntax.MLTY_Fun
           ((FStar_Extraction_ML_Syntax.MLTY_Named
               ([], (["Prims"], "string"))),
             FStar_Extraction_ML_Syntax.E_IMPURE,
             (FStar_Extraction_ML_Syntax.MLTY_Var a))))
       in
    let uu____2608 =
      let uu____2616 =
        let uu____2617 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        FStar_Util.Inr uu____2617  in
      extend_lb env uu____2616 FStar_Syntax_Syntax.tun failwith_ty false
        false
       in
    match uu____2608 with | (g,uu____2621,uu____2622) -> g
  