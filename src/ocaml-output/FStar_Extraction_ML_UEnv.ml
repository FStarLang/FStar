open Prims
type ty_binding =
  {
  ty_b_name: FStar_Extraction_ML_Syntax.mlident ;
  ty_b_ty: FStar_Extraction_ML_Syntax.mlty }
let (__proj__Mkty_binding__item__ty_b_name :
  ty_binding -> FStar_Extraction_ML_Syntax.mlident) =
  fun projectee ->
    match projectee with | { ty_b_name; ty_b_ty;_} -> ty_b_name
let (__proj__Mkty_binding__item__ty_b_ty :
  ty_binding -> FStar_Extraction_ML_Syntax.mlty) =
  fun projectee -> match projectee with | { ty_b_name; ty_b_ty;_} -> ty_b_ty
type exp_binding =
  {
  exp_b_name: FStar_Extraction_ML_Syntax.mlident ;
  exp_b_expr: FStar_Extraction_ML_Syntax.mlexpr ;
  exp_b_tscheme: FStar_Extraction_ML_Syntax.mltyscheme }
let (__proj__Mkexp_binding__item__exp_b_name :
  exp_binding -> FStar_Extraction_ML_Syntax.mlident) =
  fun projectee ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme;_} -> exp_b_name
let (__proj__Mkexp_binding__item__exp_b_expr :
  exp_binding -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun projectee ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme;_} -> exp_b_expr
let (__proj__Mkexp_binding__item__exp_b_tscheme :
  exp_binding -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun projectee ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme;_} -> exp_b_tscheme
type ty_or_exp_b = (ty_binding, exp_binding) FStar_Util.either
type binding =
  | Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b) 
  | Fv of (FStar_Syntax_Syntax.fv * exp_binding) 
let (uu___is_Bv : binding -> Prims.bool) =
  fun projectee -> match projectee with | Bv _0 -> true | uu____113 -> false
let (__proj__Bv__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)) =
  fun projectee -> match projectee with | Bv _0 -> _0
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee -> match projectee with | Fv _0 -> true | uu____142 -> false
let (__proj__Fv__item___0 :
  binding -> (FStar_Syntax_Syntax.fv * exp_binding)) =
  fun projectee -> match projectee with | Fv _0 -> _0
type tydef =
  {
  tydef_fv: FStar_Syntax_Syntax.fv ;
  tydef_mlmodule_name: FStar_Extraction_ML_Syntax.mlsymbol Prims.list ;
  tydef_name: FStar_Extraction_ML_Syntax.mlsymbol ;
  tydef_def: FStar_Extraction_ML_Syntax.mltyscheme }
let (__proj__Mktydef__item__tydef_fv : tydef -> FStar_Syntax_Syntax.fv) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_def;_} -> tydef_fv
let (__proj__Mktydef__item__tydef_mlmodule_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol Prims.list) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_def;_} ->
        tydef_mlmodule_name
let (__proj__Mktydef__item__tydef_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_def;_} -> tydef_name
let (__proj__Mktydef__item__tydef_def :
  tydef -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_def;_} -> tydef_def
let (tydef_fv : tydef -> FStar_Syntax_Syntax.fv) = fun td -> td.tydef_fv
let (tydef_def : tydef -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun td -> td.tydef_def
let (tydef_mlpath : tydef -> FStar_Extraction_ML_Syntax.mlpath) =
  fun td -> ((td.tydef_mlmodule_name), (td.tydef_name))
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
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_tcenv
let (__proj__Mkuenv__item__env_bindings : uenv -> binding Prims.list) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_bindings
let (__proj__Mkuenv__item__env_mlident_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_mlident_map
let (__proj__Mkuenv__item__mlpath_of_lid :
  uenv -> FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> mlpath_of_lid
let (__proj__Mkuenv__item__env_fieldname_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_fieldname_map
let (__proj__Mkuenv__item__mlpath_of_fieldname :
  uenv -> FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> mlpath_of_fieldname
let (__proj__Mkuenv__item__tydefs : uenv -> tydef Prims.list) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> tydefs
let (__proj__Mkuenv__item__type_names :
  uenv ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> type_names
let (__proj__Mkuenv__item__currentModule :
  uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> currentModule
let (tcenv_of_uenv : uenv -> FStar_TypeChecker_Env.env) =
  fun u -> u.env_tcenv
let (set_tcenv : uenv -> FStar_TypeChecker_Env.env -> uenv) =
  fun u ->
    fun t ->
      let uu___67_650 = u in
      {
        env_tcenv = t;
        env_bindings = (uu___67_650.env_bindings);
        env_mlident_map = (uu___67_650.env_mlident_map);
        mlpath_of_lid = (uu___67_650.mlpath_of_lid);
        env_fieldname_map = (uu___67_650.env_fieldname_map);
        mlpath_of_fieldname = (uu___67_650.mlpath_of_fieldname);
        tydefs = (uu___67_650.tydefs);
        type_names = (uu___67_650.type_names);
        currentModule = (uu___67_650.currentModule)
      }
let (current_module_of_uenv : uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun u -> u.currentModule
let (set_current_module : uenv -> FStar_Extraction_ML_Syntax.mlpath -> uenv)
  =
  fun u ->
    fun m ->
      let uu___75_666 = u in
      {
        env_tcenv = (uu___75_666.env_tcenv);
        env_bindings = (uu___75_666.env_bindings);
        env_mlident_map = (uu___75_666.env_mlident_map);
        mlpath_of_lid = (uu___75_666.mlpath_of_lid);
        env_fieldname_map = (uu___75_666.env_fieldname_map);
        mlpath_of_fieldname = (uu___75_666.mlpath_of_fieldname);
        tydefs = (uu___75_666.tydefs);
        type_names = (uu___75_666.type_names);
        currentModule = m
      }
let (bindings_of_uenv : uenv -> binding Prims.list) = fun u -> u.env_bindings
let (debug : uenv -> (unit -> unit) -> unit) =
  fun g ->
    fun f ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule in
      let uu____690 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction") in
      if uu____690 then f () else ()
let (print_mlpath_map : uenv -> Prims.string) =
  fun g ->
    let string_of_mlpath mlp =
      Prims.op_Hat
        (FStar_String.concat "." (FStar_Pervasives_Native.fst mlp))
        (Prims.op_Hat "." (FStar_Pervasives_Native.snd mlp)) in
    let entries =
      FStar_Util.psmap_fold g.mlpath_of_lid
        (fun key ->
           fun value ->
             fun entries ->
               let uu____733 =
                 FStar_Util.format2 "%s -> %s" key (string_of_mlpath value) in
               uu____733 :: entries) [] in
    FStar_String.concat "\n" entries
let (try_lookup_fv :
  uenv ->
    FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun g ->
    fun fv ->
      FStar_Util.find_map g.env_bindings
        (fun uu___0_751 ->
           match uu___0_751 with
           | Fv (fv', t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____756 -> FStar_Pervasives_Native.None)
let (lookup_fv : uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun g ->
    fun fv ->
      let uu____767 = try_lookup_fv g fv in
      match uu____767 with
      | FStar_Pervasives_Native.None ->
          let uu____770 =
            let uu____771 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p in
            let uu____772 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____771
              uu____772 in
          failwith uu____770
      | FStar_Pervasives_Native.Some y -> y
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g ->
    fun bv ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___1_790 ->
             match uu___1_790 with
             | Bv (bv', r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____795 -> FStar_Pervasives_Native.None) in
      match x with
      | FStar_Pervasives_Native.None ->
          let uu____796 =
            let uu____797 =
              let uu____798 =
                FStar_Ident.range_of_id bv.FStar_Syntax_Syntax.ppname in
              FStar_Range.string_of_range uu____798 in
            let uu____799 = FStar_Syntax_Print.bv_to_string bv in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____797
              uu____799 in
          failwith uu____796
      | FStar_Pervasives_Native.Some y -> y
let (lookup_term :
  uenv ->
    FStar_Syntax_Syntax.term ->
      (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun t ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____824 = lookup_bv g x in
          (uu____824, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar x ->
          let uu____828 =
            let uu____829 = lookup_fv g x in FStar_Util.Inr uu____829 in
          (uu____828, (x.FStar_Syntax_Syntax.fv_qual))
      | uu____832 -> failwith "Impossible: lookup_term for a non-name"
let (lookup_ty : uenv -> FStar_Syntax_Syntax.bv -> ty_binding) =
  fun g ->
    fun x ->
      let uu____849 = lookup_bv g x in
      match uu____849 with
      | FStar_Util.Inl ty -> ty
      | uu____851 -> failwith "Expected a type name"
let (lookup_tydef :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env ->
    fun uu____863 ->
      match uu____863 with
      | (module_name, ty_name) ->
          FStar_Util.find_map env.tydefs
            (fun tydef1 ->
               if
                 (ty_name = tydef1.tydef_name) &&
                   (module_name = tydef1.tydef_mlmodule_name)
               then FStar_Pervasives_Native.Some (tydef1.tydef_def)
               else FStar_Pervasives_Native.None)
let (mlpath_of_lident :
  uenv -> FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlpath) =
  fun g ->
    fun x ->
      let uu____891 =
        let uu____894 = FStar_Ident.string_of_lid x in
        FStar_Util.psmap_try_find g.mlpath_of_lid uu____894 in
      match uu____891 with
      | FStar_Pervasives_Native.None ->
          (debug g
             (fun uu____899 ->
                (let uu____901 = FStar_Ident.string_of_lid x in
                 FStar_Util.print1 "Identifier not found: %s" uu____901);
                (let uu____902 = print_mlpath_map g in
                 FStar_Util.print1 "Env is \n%s\n" uu____902));
           (let uu____903 =
              let uu____904 = FStar_Ident.string_of_lid x in
              Prims.op_Hat "Identifier not found: " uu____904 in
            failwith uu____903))
      | FStar_Pervasives_Native.Some mlp -> mlp
let (is_type_name : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g ->
    fun fv ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some
           (fun uu____929 ->
              match uu____929 with
              | (x, uu____935) -> FStar_Syntax_Syntax.fv_eq fv x))
let (is_fv_type : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g ->
    fun fv ->
      (is_type_name g fv) ||
        (FStar_All.pipe_right g.tydefs
           (FStar_Util.for_some
              (fun tydef1 -> FStar_Syntax_Syntax.fv_eq fv tydef1.tydef_fv)))
let (lookup_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      FStar_Extraction_ML_Syntax.mlpath)
  =
  fun g ->
    fun uu____963 ->
      match uu____963 with
      | (type_name, fn) ->
          let key =
            let uu____971 =
              let uu____972 = FStar_Ident.ids_of_lid type_name in
              FStar_List.append uu____972 [fn] in
            FStar_Ident.lid_of_ids uu____971 in
          let uu____975 =
            let uu____978 = FStar_Ident.string_of_lid key in
            FStar_Util.psmap_try_find g.mlpath_of_fieldname uu____978 in
          (match uu____975 with
           | FStar_Pervasives_Native.None ->
               let uu____979 =
                 let uu____980 = FStar_Ident.string_of_lid key in
                 Prims.op_Hat "Field name not found: " uu____980 in
               failwith uu____979
           | FStar_Pervasives_Native.Some mlp -> mlp)
let (initial_mlident_map : unit -> Prims.string FStar_Util.psmap) =
  let map = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  fun uu____1001 ->
    let uu____1002 = FStar_ST.op_Bang map in
    match uu____1002 with
    | FStar_Pervasives_Native.Some m -> m
    | FStar_Pervasives_Native.None ->
        let m =
          let uu____1033 =
            let uu____1036 = FStar_Options.codegen () in
            match uu____1036 with
            | FStar_Pervasives_Native.Some (FStar_Options.FSharp) ->
                FStar_Extraction_ML_Syntax.fsharpkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.OCaml) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Plugin) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Kremlin) ->
                FStar_Extraction_ML_Syntax.kremlin_keywords ()
            | FStar_Pervasives_Native.None -> [] in
          let uu____1041 = FStar_Util.psmap_empty () in
          FStar_List.fold_right
            (fun x -> fun m -> FStar_Util.psmap_add m x "") uu____1033
            uu____1041 in
        (FStar_ST.op_Colon_Equals map (FStar_Pervasives_Native.Some m); m)
let (rename_conventional : Prims.string -> Prims.bool -> Prims.string) =
  fun s ->
    fun is_local_type_variable ->
      let cs = FStar_String.list_of_string s in
      let sanitize_typ uu____1089 =
        let valid_rest c = FStar_Util.is_letter_or_digit c in
        let aux cs1 =
          FStar_List.map
            (fun x ->
               let uu____1111 = valid_rest x in if uu____1111 then x else 117)
            cs1 in
        let uu____1113 = let uu____1114 = FStar_List.hd cs in uu____1114 = 39 in
        if uu____1113
        then
          let uu____1117 = FStar_List.hd cs in
          let uu____1118 =
            let uu____1121 = FStar_List.tail cs in aux uu____1121 in
          uu____1117 :: uu____1118
        else (let uu____1125 = aux cs in 39 :: uu____1125) in
      let sanitize_term uu____1135 =
        let valid c =
          ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39) in
        let cs' =
          FStar_List.fold_right
            (fun c ->
               fun cs1 ->
                 let uu____1154 =
                   let uu____1157 = valid c in
                   if uu____1157 then [c] else [95; 95] in
                 FStar_List.append uu____1154 cs1) cs [] in
        match cs' with
        | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
        | uu____1167 -> cs in
      let uu____1170 =
        if is_local_type_variable then sanitize_typ () else sanitize_term () in
      FStar_String.string_of_list uu____1170
let (root_name_of_bv :
  FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlident) =
  fun x ->
    let uu____1181 =
      (let uu____1184 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname in
       FStar_Util.starts_with uu____1184 FStar_Ident.reserved_prefix) ||
        (FStar_Syntax_Syntax.is_null_bv x) in
    if uu____1181
    then FStar_Ident.reserved_prefix
    else FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname
let (find_uniq :
  Prims.string FStar_Util.psmap ->
    Prims.string ->
      Prims.bool -> (Prims.string * Prims.string FStar_Util.psmap))
  =
  fun ml_ident_map ->
    fun root_name ->
      fun is_local_type_variable ->
        let rec aux i root_name1 =
          let target_mlident =
            if i = Prims.int_zero
            then root_name1
            else
              (let uu____1230 = FStar_Util.string_of_int i in
               Prims.op_Hat root_name1 uu____1230) in
          let uu____1231 =
            FStar_Util.psmap_try_find ml_ident_map target_mlident in
          match uu____1231 with
          | FStar_Pervasives_Native.Some x ->
              aux (i + Prims.int_one) root_name1
          | FStar_Pervasives_Native.None ->
              let map = FStar_Util.psmap_add ml_ident_map target_mlident "" in
              (target_mlident, map) in
        let mlident = rename_conventional root_name is_local_type_variable in
        if is_local_type_variable
        then
          let uu____1253 =
            let uu____1260 = FStar_Util.substring_from mlident Prims.int_one in
            aux Prims.int_zero uu____1260 in
          match uu____1253 with | (nm, map) -> ((Prims.op_Hat "'" nm), map)
        else aux Prims.int_zero mlident
let (mlns_of_lid : FStar_Ident.lident -> Prims.string Prims.list) =
  fun x ->
    let uu____1283 = FStar_Ident.ns_of_lid x in
    FStar_List.map FStar_Ident.string_of_id uu____1283
let (new_mlpath_of_lident :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g ->
    fun x ->
      let uu____1304 =
        let uu____1309 =
          FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid in
        if uu____1309
        then
          let uu____1314 =
            let uu____1315 =
              let uu____1316 = FStar_Ident.ident_of_lid x in
              FStar_Ident.string_of_id uu____1316 in
            ([], uu____1315) in
          (uu____1314, g)
        else
          (let uu____1320 =
             let uu____1327 =
               let uu____1328 = FStar_Ident.ident_of_lid x in
               FStar_Ident.string_of_id uu____1328 in
             find_uniq g.env_mlident_map uu____1327 false in
           match uu____1320 with
           | (name, map) ->
               let g1 =
                 let uu___239_1340 = g in
                 {
                   env_tcenv = (uu___239_1340.env_tcenv);
                   env_bindings = (uu___239_1340.env_bindings);
                   env_mlident_map = map;
                   mlpath_of_lid = (uu___239_1340.mlpath_of_lid);
                   env_fieldname_map = (uu___239_1340.env_fieldname_map);
                   mlpath_of_fieldname = (uu___239_1340.mlpath_of_fieldname);
                   tydefs = (uu___239_1340.tydefs);
                   type_names = (uu___239_1340.type_names);
                   currentModule = (uu___239_1340.currentModule)
                 } in
               let uu____1341 =
                 let uu____1342 = mlns_of_lid x in (uu____1342, name) in
               (uu____1341, g1)) in
      match uu____1304 with
      | (mlp, g1) ->
          let g2 =
            let uu___245_1354 = g1 in
            let uu____1355 =
              let uu____1358 = FStar_Ident.string_of_lid x in
              FStar_Util.psmap_add g1.mlpath_of_lid uu____1358 mlp in
            {
              env_tcenv = (uu___245_1354.env_tcenv);
              env_bindings = (uu___245_1354.env_bindings);
              env_mlident_map = (uu___245_1354.env_mlident_map);
              mlpath_of_lid = uu____1355;
              env_fieldname_map = (uu___245_1354.env_fieldname_map);
              mlpath_of_fieldname = (uu___245_1354.mlpath_of_fieldname);
              tydefs = (uu___245_1354.tydefs);
              type_names = (uu___245_1354.type_names);
              currentModule = (uu___245_1354.currentModule)
            } in
          (mlp, g2)
let (extend_ty : uenv -> FStar_Syntax_Syntax.bv -> Prims.bool -> uenv) =
  fun g ->
    fun a ->
      fun map_to_top ->
        let is_local_type_variable = Prims.op_Negation map_to_top in
        let uu____1375 =
          let uu____1382 = root_name_of_bv a in
          find_uniq g.env_mlident_map uu____1382 is_local_type_variable in
        match uu____1375 with
        | (ml_a, mlident_map) ->
            let mapped_to =
              if map_to_top
              then FStar_Extraction_ML_Syntax.MLTY_Top
              else FStar_Extraction_ML_Syntax.MLTY_Var ml_a in
            let gamma =
              (Bv
                 (a,
                   (FStar_Util.Inl { ty_b_name = ml_a; ty_b_ty = mapped_to })))
              :: (g.env_bindings) in
            let tcenv = FStar_TypeChecker_Env.push_bv g.env_tcenv a in
            let uu___262_1395 = g in
            {
              env_tcenv = tcenv;
              env_bindings = gamma;
              env_mlident_map = mlident_map;
              mlpath_of_lid = (uu___262_1395.mlpath_of_lid);
              env_fieldname_map = (uu___262_1395.env_fieldname_map);
              mlpath_of_fieldname = (uu___262_1395.mlpath_of_fieldname);
              tydefs = (uu___262_1395.tydefs);
              type_names = (uu___262_1395.type_names);
              currentModule = (uu___262_1395.currentModule)
            }
let (extend_bv :
  uenv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool ->
          Prims.bool ->
            (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g ->
    fun x ->
      fun t_x ->
        fun add_unit ->
          fun mk_unit ->
            let ml_ty =
              match t_x with
              | ([], t) -> t
              | uu____1435 -> FStar_Extraction_ML_Syntax.MLTY_Top in
            let uu____1436 =
              let uu____1443 = root_name_of_bv x in
              find_uniq g.env_mlident_map uu____1443 false in
            match uu____1436 with
            | (mlident, mlident_map) ->
                let mlx = FStar_Extraction_ML_Syntax.MLE_Var mlident in
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
                    else FStar_Extraction_ML_Syntax.with_ty ml_ty mlx in
                let t_x1 =
                  if add_unit
                  then FStar_Extraction_ML_Syntax.pop_unit t_x
                  else t_x in
                let exp_binding1 =
                  {
                    exp_b_name = mlident;
                    exp_b_expr = mlx1;
                    exp_b_tscheme = t_x1
                  } in
                let gamma = (Bv (x, (FStar_Util.Inr exp_binding1))) ::
                  (g.env_bindings) in
                let tcenv =
                  let uu____1469 = FStar_Syntax_Syntax.binders_of_list [x] in
                  FStar_TypeChecker_Env.push_binders g.env_tcenv uu____1469 in
                ((let uu___288_1471 = g in
                  {
                    env_tcenv = tcenv;
                    env_bindings = gamma;
                    env_mlident_map = mlident_map;
                    mlpath_of_lid = (uu___288_1471.mlpath_of_lid);
                    env_fieldname_map = (uu___288_1471.env_fieldname_map);
                    mlpath_of_fieldname = (uu___288_1471.mlpath_of_fieldname);
                    tydefs = (uu___288_1471.tydefs);
                    type_names = (uu___288_1471.type_names);
                    currentModule = (uu___288_1471.currentModule)
                  }), mlident, exp_binding1)
let (burn_name : uenv -> FStar_Extraction_ML_Syntax.mlident -> uenv) =
  fun g ->
    fun i ->
      let uu___292_1482 = g in
      let uu____1483 = FStar_Util.psmap_add g.env_mlident_map i "" in
      {
        env_tcenv = (uu___292_1482.env_tcenv);
        env_bindings = (uu___292_1482.env_bindings);
        env_mlident_map = uu____1483;
        mlpath_of_lid = (uu___292_1482.mlpath_of_lid);
        env_fieldname_map = (uu___292_1482.env_fieldname_map);
        mlpath_of_fieldname = (uu___292_1482.mlpath_of_fieldname);
        tydefs = (uu___292_1482.tydefs);
        type_names = (uu___292_1482.type_names);
        currentModule = (uu___292_1482.currentModule)
      }
let (new_mlident : uenv -> (uenv * FStar_Extraction_ML_Syntax.mlident)) =
  fun g ->
    let ml_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
    let x =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.tun in
    let uu____1501 =
      extend_bv g x ([], FStar_Extraction_ML_Syntax.MLTY_Top) false false in
    match uu____1501 with | (g1, id, uu____1514) -> (g1, id)
let (extend_fv :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool ->
          (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g ->
    fun x ->
      fun t_x ->
        fun add_unit ->
          let rec mltyFvars t =
            match t with
            | FStar_Extraction_ML_Syntax.MLTY_Var x1 -> [x1]
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) ->
                let uu____1561 = mltyFvars t1 in
                let uu____1564 = mltyFvars t2 in
                FStar_List.append uu____1561 uu____1564
            | FStar_Extraction_ML_Syntax.MLTY_Named (args, path) ->
                FStar_List.collect mltyFvars args
            | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
                FStar_List.collect mltyFvars ts
            | FStar_Extraction_ML_Syntax.MLTY_Top -> []
            | FStar_Extraction_ML_Syntax.MLTY_Erased -> [] in
          let rec subsetMlidents la lb =
            match la with
            | h::tla -> (FStar_List.contains h lb) && (subsetMlidents tla lb)
            | [] -> true in
          let tySchemeIsClosed tys =
            let uu____1605 = mltyFvars (FStar_Pervasives_Native.snd tys) in
            subsetMlidents uu____1605 (FStar_Pervasives_Native.fst tys) in
          let uu____1608 = tySchemeIsClosed t_x in
          if uu____1608
          then
            let ml_ty =
              match t_x with
              | ([], t) -> t
              | uu____1617 -> FStar_Extraction_ML_Syntax.MLTY_Top in
            let uu____1618 =
              new_mlpath_of_lident g
                (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____1618 with
            | (mlpath, g1) ->
                let mlsymbol = FStar_Pervasives_Native.snd mlpath in
                let mly = FStar_Extraction_ML_Syntax.MLE_Name mlpath in
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
                  else FStar_Extraction_ML_Syntax.with_ty ml_ty mly in
                let t_x1 =
                  if add_unit
                  then FStar_Extraction_ML_Syntax.pop_unit t_x
                  else t_x in
                let exp_binding1 =
                  {
                    exp_b_name = mlsymbol;
                    exp_b_expr = mly1;
                    exp_b_tscheme = t_x1
                  } in
                let gamma = (Fv (x, exp_binding1)) :: (g1.env_bindings) in
                let mlident_map =
                  FStar_Util.psmap_add g1.env_mlident_map mlsymbol "" in
                ((let uu___351_1649 = g1 in
                  {
                    env_tcenv = (uu___351_1649.env_tcenv);
                    env_bindings = gamma;
                    env_mlident_map = mlident_map;
                    mlpath_of_lid = (uu___351_1649.mlpath_of_lid);
                    env_fieldname_map = (uu___351_1649.env_fieldname_map);
                    mlpath_of_fieldname = (uu___351_1649.mlpath_of_fieldname);
                    tydefs = (uu___351_1649.tydefs);
                    type_names = (uu___351_1649.type_names);
                    currentModule = (uu___351_1649.currentModule)
                  }), mlsymbol, exp_binding1)
          else failwith "freevars found"
let (extend_lb :
  uenv ->
    FStar_Syntax_Syntax.lbname ->
      FStar_Syntax_Syntax.typ ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          Prims.bool ->
            (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g ->
    fun l ->
      fun t ->
        fun t_x ->
          fun add_unit ->
            match l with
            | FStar_Util.Inl x -> extend_bv g x t_x add_unit false
            | FStar_Util.Inr f -> extend_fv g f t_x add_unit
let (extend_tydef :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        (tydef * FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g ->
    fun fv ->
      fun ts ->
        let uu____1723 =
          new_mlpath_of_lident g
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        match uu____1723 with
        | (name, g1) ->
            let tydef1 =
              {
                tydef_fv = fv;
                tydef_mlmodule_name = (FStar_Pervasives_Native.fst name);
                tydef_name = (FStar_Pervasives_Native.snd name);
                tydef_def = ts
              } in
            (tydef1, name,
              (let uu___373_1742 = g1 in
               {
                 env_tcenv = (uu___373_1742.env_tcenv);
                 env_bindings = (uu___373_1742.env_bindings);
                 env_mlident_map = (uu___373_1742.env_mlident_map);
                 mlpath_of_lid = (uu___373_1742.mlpath_of_lid);
                 env_fieldname_map = (uu___373_1742.env_fieldname_map);
                 mlpath_of_fieldname = (uu___373_1742.mlpath_of_fieldname);
                 tydefs = (tydef1 :: (g1.tydefs));
                 type_names = ((fv, name) :: (g1.type_names));
                 currentModule = (uu___373_1742.currentModule)
               }))
let (extend_type_name :
  uenv ->
    FStar_Syntax_Syntax.fv -> (FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g ->
    fun fv ->
      let uu____1765 =
        new_mlpath_of_lident g
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      match uu____1765 with
      | (name, g1) ->
          (name,
            (let uu___380_1777 = g1 in
             {
               env_tcenv = (uu___380_1777.env_tcenv);
               env_bindings = (uu___380_1777.env_bindings);
               env_mlident_map = (uu___380_1777.env_mlident_map);
               mlpath_of_lid = (uu___380_1777.mlpath_of_lid);
               env_fieldname_map = (uu___380_1777.env_fieldname_map);
               mlpath_of_fieldname = (uu___380_1777.mlpath_of_fieldname);
               tydefs = (uu___380_1777.tydefs);
               type_names = ((fv, name) :: (g1.type_names));
               currentModule = (uu___380_1777.currentModule)
             }))
let (extend_with_monad_op_name :
  uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      Prims.string ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident *
            exp_binding * uenv))
  =
  fun g ->
    fun ed ->
      fun nm ->
        fun ts ->
          let lid =
            let uu____1811 = FStar_Ident.id_of_text nm in
            FStar_Syntax_Util.mk_field_projector_name_from_ident
              ed.FStar_Syntax_Syntax.mname uu____1811 in
          let uu____1812 =
            let uu____1819 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            extend_fv g uu____1819 ts false in
          match uu____1812 with
          | (g1, mlid, exp_b) ->
              let mlp =
                let uu____1838 = mlns_of_lid lid in (uu____1838, mlid) in
              (mlp, lid, exp_b, g1)
let (extend_with_action_name :
  uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.action ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident *
            exp_binding * uenv))
  =
  fun g ->
    fun ed ->
      fun a ->
        fun ts ->
          let nm =
            let uu____1872 =
              FStar_Ident.ident_of_lid a.FStar_Syntax_Syntax.action_name in
            FStar_Ident.string_of_id uu____1872 in
          let module_name =
            FStar_Ident.ns_of_lid ed.FStar_Syntax_Syntax.mname in
          let lid =
            let uu____1875 =
              let uu____1876 =
                let uu____1879 = FStar_Ident.id_of_text nm in [uu____1879] in
              FStar_List.append module_name uu____1876 in
            FStar_Ident.lid_of_ids uu____1875 in
          let uu____1880 =
            let uu____1887 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            extend_fv g uu____1887 ts false in
          match uu____1880 with
          | (g1, mlid, exp_b) ->
              let mlp =
                let uu____1906 = mlns_of_lid lid in (uu____1906, mlid) in
              (mlp, lid, exp_b, g1)
let (extend_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      (FStar_Extraction_ML_Syntax.mlident * uenv))
  =
  fun g ->
    fun uu____1928 ->
      match uu____1928 with
      | (type_name, fn) ->
          let key =
            let uu____1940 =
              let uu____1941 = FStar_Ident.ids_of_lid type_name in
              FStar_List.append uu____1941 [fn] in
            FStar_Ident.lid_of_ids uu____1940 in
          let uu____1944 =
            let uu____1951 = FStar_Ident.string_of_id fn in
            find_uniq g.env_fieldname_map uu____1951 false in
          (match uu____1944 with
           | (name, fieldname_map) ->
               let ns = mlns_of_lid type_name in
               let mlp = (ns, name) in
               let g1 =
                 let uu___414_1975 = g in
                 let uu____1976 =
                   let uu____1979 = FStar_Ident.string_of_lid key in
                   FStar_Util.psmap_add g.mlpath_of_fieldname uu____1979 mlp in
                 {
                   env_tcenv = (uu___414_1975.env_tcenv);
                   env_bindings = (uu___414_1975.env_bindings);
                   env_mlident_map = (uu___414_1975.env_mlident_map);
                   mlpath_of_lid = (uu___414_1975.mlpath_of_lid);
                   env_fieldname_map = fieldname_map;
                   mlpath_of_fieldname = uu____1976;
                   tydefs = (uu___414_1975.tydefs);
                   type_names = (uu___414_1975.type_names);
                   currentModule = (uu___414_1975.currentModule)
                 } in
               (name, g1))
let (extend_with_module_name :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g ->
    fun m ->
      let ns = mlns_of_lid m in
      let p =
        let uu____1998 = FStar_Ident.ident_of_lid m in
        FStar_Ident.string_of_id uu____1998 in
      ((ns, p), g)
let (exit_module : uenv -> uenv) =
  fun g ->
    let uu___422_2006 = g in
    let uu____2007 = initial_mlident_map () in
    let uu____2010 = initial_mlident_map () in
    {
      env_tcenv = (uu___422_2006.env_tcenv);
      env_bindings = (uu___422_2006.env_bindings);
      env_mlident_map = uu____2007;
      mlpath_of_lid = (uu___422_2006.mlpath_of_lid);
      env_fieldname_map = uu____2010;
      mlpath_of_fieldname = (uu___422_2006.mlpath_of_fieldname);
      tydefs = (uu___422_2006.tydefs);
      type_names = (uu___422_2006.type_names);
      currentModule = (uu___422_2006.currentModule)
    }
let (new_uenv : FStar_TypeChecker_Env.env -> uenv) =
  fun e ->
    let env =
      let uu____2019 = initial_mlident_map () in
      let uu____2022 = FStar_Util.psmap_empty () in
      let uu____2025 = initial_mlident_map () in
      let uu____2028 = FStar_Util.psmap_empty () in
      {
        env_tcenv = e;
        env_bindings = [];
        env_mlident_map = uu____2019;
        mlpath_of_lid = uu____2022;
        env_fieldname_map = uu____2025;
        mlpath_of_fieldname = uu____2028;
        tydefs = [];
        type_names = [];
        currentModule = ([], "")
      } in
    let a = "'a" in
    let failwith_ty =
      ([a],
        (FStar_Extraction_ML_Syntax.MLTY_Fun
           ((FStar_Extraction_ML_Syntax.MLTY_Named
               ([], (["Prims"], "string"))),
             FStar_Extraction_ML_Syntax.E_IMPURE,
             (FStar_Extraction_ML_Syntax.MLTY_Var a)))) in
    let uu____2047 =
      let uu____2054 =
        let uu____2055 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        FStar_Util.Inr uu____2055 in
      extend_lb env uu____2054 FStar_Syntax_Syntax.tun failwith_ty false in
    match uu____2047 with | (g, uu____2057, uu____2058) -> g