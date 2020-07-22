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
  fun projectee -> match projectee with | Bv _0 -> true | uu____114 -> false
let (__proj__Bv__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)) =
  fun projectee -> match projectee with | Bv _0 -> _0
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee -> match projectee with | Fv _0 -> true | uu____143 -> false
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
  env_remove_typars: FStar_Extraction_ML_RemoveUnusedParameters.env_t ;
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
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; currentModule;_} -> env_tcenv
let (__proj__Mkuenv__item__env_bindings : uenv -> binding Prims.list) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; currentModule;_} -> env_bindings
let (__proj__Mkuenv__item__env_mlident_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; currentModule;_} -> env_mlident_map
let (__proj__Mkuenv__item__env_remove_typars :
  uenv -> FStar_Extraction_ML_RemoveUnusedParameters.env_t) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; currentModule;_} -> env_remove_typars
let (__proj__Mkuenv__item__mlpath_of_lid :
  uenv -> FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; currentModule;_} -> mlpath_of_lid
let (__proj__Mkuenv__item__env_fieldname_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; currentModule;_} -> env_fieldname_map
let (__proj__Mkuenv__item__mlpath_of_fieldname :
  uenv -> FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; currentModule;_} -> mlpath_of_fieldname
let (__proj__Mkuenv__item__tydefs : uenv -> tydef Prims.list) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; currentModule;_} -> tydefs
let (__proj__Mkuenv__item__type_names :
  uenv ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; currentModule;_} -> type_names
let (__proj__Mkuenv__item__currentModule :
  uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; currentModule;_} -> currentModule
let (tcenv_of_uenv : uenv -> FStar_TypeChecker_Env.env) =
  fun u -> u.env_tcenv
let (set_tcenv : uenv -> FStar_TypeChecker_Env.env -> uenv) =
  fun u ->
    fun t ->
      let uu___70_698 = u in
      {
        env_tcenv = t;
        env_bindings = (uu___70_698.env_bindings);
        env_mlident_map = (uu___70_698.env_mlident_map);
        env_remove_typars = (uu___70_698.env_remove_typars);
        mlpath_of_lid = (uu___70_698.mlpath_of_lid);
        env_fieldname_map = (uu___70_698.env_fieldname_map);
        mlpath_of_fieldname = (uu___70_698.mlpath_of_fieldname);
        tydefs = (uu___70_698.tydefs);
        type_names = (uu___70_698.type_names);
        currentModule = (uu___70_698.currentModule)
      }
let (current_module_of_uenv : uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun u -> u.currentModule
let (set_current_module : uenv -> FStar_Extraction_ML_Syntax.mlpath -> uenv)
  =
  fun u ->
    fun m ->
      let uu___78_714 = u in
      {
        env_tcenv = (uu___78_714.env_tcenv);
        env_bindings = (uu___78_714.env_bindings);
        env_mlident_map = (uu___78_714.env_mlident_map);
        env_remove_typars = (uu___78_714.env_remove_typars);
        mlpath_of_lid = (uu___78_714.mlpath_of_lid);
        env_fieldname_map = (uu___78_714.env_fieldname_map);
        mlpath_of_fieldname = (uu___78_714.mlpath_of_fieldname);
        tydefs = (uu___78_714.tydefs);
        type_names = (uu___78_714.type_names);
        currentModule = m
      }
let with_typars_env :
  'a .
    uenv ->
      (FStar_Extraction_ML_RemoveUnusedParameters.env_t ->
         (FStar_Extraction_ML_RemoveUnusedParameters.env_t * 'a))
        -> (uenv * 'a)
  =
  fun u ->
    fun f ->
      let uu____749 = f u.env_remove_typars in
      match uu____749 with
      | (e, x) ->
          ((let uu___86_761 = u in
            {
              env_tcenv = (uu___86_761.env_tcenv);
              env_bindings = (uu___86_761.env_bindings);
              env_mlident_map = (uu___86_761.env_mlident_map);
              env_remove_typars = e;
              mlpath_of_lid = (uu___86_761.mlpath_of_lid);
              env_fieldname_map = (uu___86_761.env_fieldname_map);
              mlpath_of_fieldname = (uu___86_761.mlpath_of_fieldname);
              tydefs = (uu___86_761.tydefs);
              type_names = (uu___86_761.type_names);
              currentModule = (uu___86_761.currentModule)
            }), x)
let (bindings_of_uenv : uenv -> binding Prims.list) = fun u -> u.env_bindings
let (debug : uenv -> (unit -> unit) -> unit) =
  fun g ->
    fun f ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule in
      let uu____785 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction") in
      if uu____785 then f () else ()
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
               let uu____828 =
                 FStar_Util.format2 "%s -> %s" key (string_of_mlpath value) in
               uu____828 :: entries) [] in
    FStar_String.concat "\n" entries
let (try_lookup_fv :
  uenv ->
    FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun g ->
    fun fv ->
      FStar_Util.find_map g.env_bindings
        (fun uu___0_846 ->
           match uu___0_846 with
           | Fv (fv', t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____851 -> FStar_Pervasives_Native.None)
let (lookup_fv : uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun g ->
    fun fv ->
      let uu____862 = try_lookup_fv g fv in
      match uu____862 with
      | FStar_Pervasives_Native.None ->
          let uu____865 =
            let uu____866 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p in
            let uu____867 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____866
              uu____867 in
          failwith uu____865
      | FStar_Pervasives_Native.Some y -> y
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g ->
    fun bv ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___1_885 ->
             match uu___1_885 with
             | Bv (bv', r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____890 -> FStar_Pervasives_Native.None) in
      match x with
      | FStar_Pervasives_Native.None ->
          let uu____891 =
            let uu____892 =
              let uu____893 =
                FStar_Ident.range_of_id bv.FStar_Syntax_Syntax.ppname in
              FStar_Range.string_of_range uu____893 in
            let uu____894 = FStar_Syntax_Print.bv_to_string bv in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____892
              uu____894 in
          failwith uu____891
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
          let uu____919 = lookup_bv g x in
          (uu____919, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar x ->
          let uu____923 =
            let uu____924 = lookup_fv g x in FStar_Util.Inr uu____924 in
          (uu____923, (x.FStar_Syntax_Syntax.fv_qual))
      | uu____927 -> failwith "Impossible: lookup_term for a non-name"
let (lookup_ty : uenv -> FStar_Syntax_Syntax.bv -> ty_binding) =
  fun g ->
    fun x ->
      let uu____944 = lookup_bv g x in
      match uu____944 with
      | FStar_Util.Inl ty -> ty
      | uu____946 -> failwith "Expected a type name"
let (lookup_tydef :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env ->
    fun uu____958 ->
      match uu____958 with
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
      let uu____986 =
        let uu____989 = FStar_Ident.string_of_lid x in
        FStar_Util.psmap_try_find g.mlpath_of_lid uu____989 in
      match uu____986 with
      | FStar_Pervasives_Native.None ->
          (debug g
             (fun uu____994 ->
                (let uu____996 = FStar_Ident.string_of_lid x in
                 FStar_Util.print1 "Identifier not found: %s" uu____996);
                (let uu____997 = print_mlpath_map g in
                 FStar_Util.print1 "Env is \n%s\n" uu____997));
           (let uu____998 =
              let uu____999 = FStar_Ident.string_of_lid x in
              Prims.op_Hat "Identifier not found: " uu____999 in
            failwith uu____998))
      | FStar_Pervasives_Native.Some mlp -> mlp
let (is_type_name : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g ->
    fun fv ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some
           (fun uu____1024 ->
              match uu____1024 with
              | (x, uu____1030) -> FStar_Syntax_Syntax.fv_eq fv x))
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
    fun uu____1058 ->
      match uu____1058 with
      | (type_name, fn) ->
          let key =
            let uu____1066 =
              let uu____1067 = FStar_Ident.ids_of_lid type_name in
              FStar_List.append uu____1067 [fn] in
            FStar_Ident.lid_of_ids uu____1066 in
          let uu____1070 =
            let uu____1073 = FStar_Ident.string_of_lid key in
            FStar_Util.psmap_try_find g.mlpath_of_fieldname uu____1073 in
          (match uu____1070 with
           | FStar_Pervasives_Native.None ->
               let uu____1074 =
                 let uu____1075 = FStar_Ident.string_of_lid key in
                 Prims.op_Hat "Field name not found: " uu____1075 in
               failwith uu____1074
           | FStar_Pervasives_Native.Some mlp -> mlp)
let (initial_mlident_map : unit -> Prims.string FStar_Util.psmap) =
  let map = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  fun uu____1096 ->
    let uu____1097 = FStar_ST.op_Bang map in
    match uu____1097 with
    | FStar_Pervasives_Native.Some m -> m
    | FStar_Pervasives_Native.None ->
        let m =
          let uu____1128 =
            let uu____1131 = FStar_Options.codegen () in
            match uu____1131 with
            | FStar_Pervasives_Native.Some (FStar_Options.FSharp) ->
                FStar_Extraction_ML_Syntax.fsharpkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.OCaml) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Plugin) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Kremlin) ->
                FStar_Extraction_ML_Syntax.kremlin_keywords ()
            | FStar_Pervasives_Native.None -> [] in
          let uu____1136 = FStar_Util.psmap_empty () in
          FStar_List.fold_right
            (fun x -> fun m -> FStar_Util.psmap_add m x "") uu____1128
            uu____1136 in
        (FStar_ST.op_Colon_Equals map (FStar_Pervasives_Native.Some m); m)
let (rename_conventional : Prims.string -> Prims.bool -> Prims.string) =
  fun s ->
    fun is_local_type_variable ->
      let cs = FStar_String.list_of_string s in
      let sanitize_typ uu____1184 =
        let valid_rest c = FStar_Util.is_letter_or_digit c in
        let aux cs1 =
          FStar_List.map
            (fun x ->
               let uu____1206 = valid_rest x in if uu____1206 then x else 117)
            cs1 in
        let uu____1208 = let uu____1209 = FStar_List.hd cs in uu____1209 = 39 in
        if uu____1208
        then
          let uu____1212 = FStar_List.hd cs in
          let uu____1213 =
            let uu____1216 = FStar_List.tail cs in aux uu____1216 in
          uu____1212 :: uu____1213
        else (let uu____1220 = aux cs in 39 :: uu____1220) in
      let sanitize_term uu____1230 =
        let valid c =
          ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39) in
        let cs' =
          FStar_List.fold_right
            (fun c ->
               fun cs1 ->
                 let uu____1249 =
                   let uu____1252 = valid c in
                   if uu____1252 then [c] else [95; 95] in
                 FStar_List.append uu____1249 cs1) cs [] in
        match cs' with
        | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
        | uu____1262 -> cs in
      let uu____1265 =
        if is_local_type_variable then sanitize_typ () else sanitize_term () in
      FStar_String.string_of_list uu____1265
let (root_name_of_bv :
  FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlident) =
  fun x ->
    let uu____1276 =
      (let uu____1279 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname in
       FStar_Util.starts_with uu____1279 FStar_Ident.reserved_prefix) ||
        (FStar_Syntax_Syntax.is_null_bv x) in
    if uu____1276
    then
      let uu____1280 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname in
      let uu____1281 =
        let uu____1282 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.op_Hat "_" uu____1282 in
      Prims.op_Hat uu____1280 uu____1281
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
              (let uu____1328 = FStar_Util.string_of_int i in
               Prims.op_Hat root_name1 uu____1328) in
          let uu____1329 =
            FStar_Util.psmap_try_find ml_ident_map target_mlident in
          match uu____1329 with
          | FStar_Pervasives_Native.Some x ->
              aux (i + Prims.int_one) root_name1
          | FStar_Pervasives_Native.None ->
              let map = FStar_Util.psmap_add ml_ident_map target_mlident "" in
              (target_mlident, map) in
        let mlident = rename_conventional root_name is_local_type_variable in
        if is_local_type_variable
        then
          let uu____1351 =
            let uu____1358 = FStar_Util.substring_from mlident Prims.int_one in
            aux Prims.int_zero uu____1358 in
          match uu____1351 with | (nm, map) -> ((Prims.op_Hat "'" nm), map)
        else aux Prims.int_zero mlident
let (mlns_of_lid : FStar_Ident.lident -> Prims.string Prims.list) =
  fun x ->
    let uu____1381 = FStar_Ident.ns_of_lid x in
    FStar_List.map FStar_Ident.string_of_id uu____1381
let (new_mlpath_of_lident :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g ->
    fun x ->
      let uu____1402 =
        let uu____1407 =
          FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid in
        if uu____1407
        then
          let uu____1412 =
            let uu____1413 =
              let uu____1414 = FStar_Ident.ident_of_lid x in
              FStar_Ident.string_of_id uu____1414 in
            ([], uu____1413) in
          (uu____1412, g)
        else
          (let uu____1418 =
             let uu____1425 =
               let uu____1426 = FStar_Ident.ident_of_lid x in
               FStar_Ident.string_of_id uu____1426 in
             find_uniq g.env_mlident_map uu____1425 false in
           match uu____1418 with
           | (name, map) ->
               let g1 =
                 let uu___250_1438 = g in
                 {
                   env_tcenv = (uu___250_1438.env_tcenv);
                   env_bindings = (uu___250_1438.env_bindings);
                   env_mlident_map = map;
                   env_remove_typars = (uu___250_1438.env_remove_typars);
                   mlpath_of_lid = (uu___250_1438.mlpath_of_lid);
                   env_fieldname_map = (uu___250_1438.env_fieldname_map);
                   mlpath_of_fieldname = (uu___250_1438.mlpath_of_fieldname);
                   tydefs = (uu___250_1438.tydefs);
                   type_names = (uu___250_1438.type_names);
                   currentModule = (uu___250_1438.currentModule)
                 } in
               let uu____1439 =
                 let uu____1440 = mlns_of_lid x in (uu____1440, name) in
               (uu____1439, g1)) in
      match uu____1402 with
      | (mlp, g1) ->
          let g2 =
            let uu___256_1452 = g1 in
            let uu____1453 =
              let uu____1456 = FStar_Ident.string_of_lid x in
              FStar_Util.psmap_add g1.mlpath_of_lid uu____1456 mlp in
            {
              env_tcenv = (uu___256_1452.env_tcenv);
              env_bindings = (uu___256_1452.env_bindings);
              env_mlident_map = (uu___256_1452.env_mlident_map);
              env_remove_typars = (uu___256_1452.env_remove_typars);
              mlpath_of_lid = uu____1453;
              env_fieldname_map = (uu___256_1452.env_fieldname_map);
              mlpath_of_fieldname = (uu___256_1452.mlpath_of_fieldname);
              tydefs = (uu___256_1452.tydefs);
              type_names = (uu___256_1452.type_names);
              currentModule = (uu___256_1452.currentModule)
            } in
          (mlp, g2)
let (extend_ty : uenv -> FStar_Syntax_Syntax.bv -> Prims.bool -> uenv) =
  fun g ->
    fun a ->
      fun map_to_top ->
        let is_local_type_variable = Prims.op_Negation map_to_top in
        let uu____1473 =
          let uu____1480 = root_name_of_bv a in
          find_uniq g.env_mlident_map uu____1480 is_local_type_variable in
        match uu____1473 with
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
            let uu___273_1493 = g in
            {
              env_tcenv = tcenv;
              env_bindings = gamma;
              env_mlident_map = mlident_map;
              env_remove_typars = (uu___273_1493.env_remove_typars);
              mlpath_of_lid = (uu___273_1493.mlpath_of_lid);
              env_fieldname_map = (uu___273_1493.env_fieldname_map);
              mlpath_of_fieldname = (uu___273_1493.mlpath_of_fieldname);
              tydefs = (uu___273_1493.tydefs);
              type_names = (uu___273_1493.type_names);
              currentModule = (uu___273_1493.currentModule)
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
              | uu____1533 -> FStar_Extraction_ML_Syntax.MLTY_Top in
            let uu____1534 =
              let uu____1541 = root_name_of_bv x in
              find_uniq g.env_mlident_map uu____1541 false in
            match uu____1534 with
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
                  let uu____1567 = FStar_Syntax_Syntax.binders_of_list [x] in
                  FStar_TypeChecker_Env.push_binders g.env_tcenv uu____1567 in
                ((let uu___299_1569 = g in
                  {
                    env_tcenv = tcenv;
                    env_bindings = gamma;
                    env_mlident_map = mlident_map;
                    env_remove_typars = (uu___299_1569.env_remove_typars);
                    mlpath_of_lid = (uu___299_1569.mlpath_of_lid);
                    env_fieldname_map = (uu___299_1569.env_fieldname_map);
                    mlpath_of_fieldname = (uu___299_1569.mlpath_of_fieldname);
                    tydefs = (uu___299_1569.tydefs);
                    type_names = (uu___299_1569.type_names);
                    currentModule = (uu___299_1569.currentModule)
                  }), mlident, exp_binding1)
let (new_mlident : uenv -> (uenv * FStar_Extraction_ML_Syntax.mlident)) =
  fun g ->
    let ml_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
    let x =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.tun in
    let uu____1585 =
      extend_bv g x ([], FStar_Extraction_ML_Syntax.MLTY_Top) false false in
    match uu____1585 with | (g1, id, uu____1598) -> (g1, id)
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
                let uu____1645 = mltyFvars t1 in
                let uu____1648 = mltyFvars t2 in
                FStar_List.append uu____1645 uu____1648
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
            let uu____1689 = mltyFvars (FStar_Pervasives_Native.snd tys) in
            subsetMlidents uu____1689 (FStar_Pervasives_Native.fst tys) in
          let uu____1692 = tySchemeIsClosed t_x in
          if uu____1692
          then
            let ml_ty =
              match t_x with
              | ([], t) -> t
              | uu____1701 -> FStar_Extraction_ML_Syntax.MLTY_Top in
            let uu____1702 =
              new_mlpath_of_lident g
                (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____1702 with
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
                ((let uu___358_1733 = g1 in
                  {
                    env_tcenv = (uu___358_1733.env_tcenv);
                    env_bindings = gamma;
                    env_mlident_map = mlident_map;
                    env_remove_typars = (uu___358_1733.env_remove_typars);
                    mlpath_of_lid = (uu___358_1733.mlpath_of_lid);
                    env_fieldname_map = (uu___358_1733.env_fieldname_map);
                    mlpath_of_fieldname = (uu___358_1733.mlpath_of_fieldname);
                    tydefs = (uu___358_1733.tydefs);
                    type_names = (uu___358_1733.type_names);
                    currentModule = (uu___358_1733.currentModule)
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
        let uu____1807 =
          new_mlpath_of_lident g
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        match uu____1807 with
        | (name, g1) ->
            let tydef1 =
              {
                tydef_fv = fv;
                tydef_mlmodule_name = (FStar_Pervasives_Native.fst name);
                tydef_name = (FStar_Pervasives_Native.snd name);
                tydef_def = ts
              } in
            (tydef1, name,
              (let uu___380_1826 = g1 in
               {
                 env_tcenv = (uu___380_1826.env_tcenv);
                 env_bindings = (uu___380_1826.env_bindings);
                 env_mlident_map = (uu___380_1826.env_mlident_map);
                 env_remove_typars = (uu___380_1826.env_remove_typars);
                 mlpath_of_lid = (uu___380_1826.mlpath_of_lid);
                 env_fieldname_map = (uu___380_1826.env_fieldname_map);
                 mlpath_of_fieldname = (uu___380_1826.mlpath_of_fieldname);
                 tydefs = (tydef1 :: (g1.tydefs));
                 type_names = ((fv, name) :: (g1.type_names));
                 currentModule = (uu___380_1826.currentModule)
               }))
let (extend_type_name :
  uenv ->
    FStar_Syntax_Syntax.fv -> (FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g ->
    fun fv ->
      let uu____1849 =
        new_mlpath_of_lident g
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      match uu____1849 with
      | (name, g1) ->
          (name,
            (let uu___387_1861 = g1 in
             {
               env_tcenv = (uu___387_1861.env_tcenv);
               env_bindings = (uu___387_1861.env_bindings);
               env_mlident_map = (uu___387_1861.env_mlident_map);
               env_remove_typars = (uu___387_1861.env_remove_typars);
               mlpath_of_lid = (uu___387_1861.mlpath_of_lid);
               env_fieldname_map = (uu___387_1861.env_fieldname_map);
               mlpath_of_fieldname = (uu___387_1861.mlpath_of_fieldname);
               tydefs = (uu___387_1861.tydefs);
               type_names = ((fv, name) :: (g1.type_names));
               currentModule = (uu___387_1861.currentModule)
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
            let uu____1895 = FStar_Ident.id_of_text nm in
            FStar_Syntax_Util.mk_field_projector_name_from_ident
              ed.FStar_Syntax_Syntax.mname uu____1895 in
          let uu____1896 =
            let uu____1903 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            extend_fv g uu____1903 ts false in
          match uu____1896 with
          | (g1, mlid, exp_b) ->
              let mlp =
                let uu____1922 = mlns_of_lid lid in (uu____1922, mlid) in
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
            let uu____1956 =
              FStar_Ident.ident_of_lid a.FStar_Syntax_Syntax.action_name in
            FStar_Ident.string_of_id uu____1956 in
          let module_name =
            FStar_Ident.ns_of_lid ed.FStar_Syntax_Syntax.mname in
          let lid =
            let uu____1959 =
              let uu____1960 =
                let uu____1963 = FStar_Ident.id_of_text nm in [uu____1963] in
              FStar_List.append module_name uu____1960 in
            FStar_Ident.lid_of_ids uu____1959 in
          let uu____1964 =
            let uu____1971 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            extend_fv g uu____1971 ts false in
          match uu____1964 with
          | (g1, mlid, exp_b) ->
              let mlp =
                let uu____1990 = mlns_of_lid lid in (uu____1990, mlid) in
              (mlp, lid, exp_b, g1)
let (extend_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      (FStar_Extraction_ML_Syntax.mlident * uenv))
  =
  fun g ->
    fun uu____2012 ->
      match uu____2012 with
      | (type_name, fn) ->
          let key =
            let uu____2024 =
              let uu____2025 = FStar_Ident.ids_of_lid type_name in
              FStar_List.append uu____2025 [fn] in
            FStar_Ident.lid_of_ids uu____2024 in
          let uu____2028 =
            let uu____2035 = FStar_Ident.string_of_id fn in
            find_uniq g.env_fieldname_map uu____2035 false in
          (match uu____2028 with
           | (name, fieldname_map) ->
               let ns = mlns_of_lid type_name in
               let mlp = (ns, name) in
               let g1 =
                 let uu___421_2059 = g in
                 let uu____2060 =
                   let uu____2063 = FStar_Ident.string_of_lid key in
                   FStar_Util.psmap_add g.mlpath_of_fieldname uu____2063 mlp in
                 {
                   env_tcenv = (uu___421_2059.env_tcenv);
                   env_bindings = (uu___421_2059.env_bindings);
                   env_mlident_map = (uu___421_2059.env_mlident_map);
                   env_remove_typars = (uu___421_2059.env_remove_typars);
                   mlpath_of_lid = (uu___421_2059.mlpath_of_lid);
                   env_fieldname_map = fieldname_map;
                   mlpath_of_fieldname = uu____2060;
                   tydefs = (uu___421_2059.tydefs);
                   type_names = (uu___421_2059.type_names);
                   currentModule = (uu___421_2059.currentModule)
                 } in
               (name, g1))
let (extend_with_module_name :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g ->
    fun m ->
      let ns = mlns_of_lid m in
      let p =
        let uu____2082 = FStar_Ident.ident_of_lid m in
        FStar_Ident.string_of_id uu____2082 in
      ((ns, p), g)
let (exit_module : uenv -> uenv) =
  fun g ->
    let uu___429_2090 = g in
    let uu____2091 = initial_mlident_map () in
    let uu____2094 = initial_mlident_map () in
    {
      env_tcenv = (uu___429_2090.env_tcenv);
      env_bindings = (uu___429_2090.env_bindings);
      env_mlident_map = uu____2091;
      env_remove_typars = (uu___429_2090.env_remove_typars);
      mlpath_of_lid = (uu___429_2090.mlpath_of_lid);
      env_fieldname_map = uu____2094;
      mlpath_of_fieldname = (uu___429_2090.mlpath_of_fieldname);
      tydefs = (uu___429_2090.tydefs);
      type_names = (uu___429_2090.type_names);
      currentModule = (uu___429_2090.currentModule)
    }
let (new_uenv : FStar_TypeChecker_Env.env -> uenv) =
  fun e ->
    let env =
      let uu____2103 = initial_mlident_map () in
      let uu____2106 = FStar_Util.psmap_empty () in
      let uu____2109 = initial_mlident_map () in
      let uu____2112 = FStar_Util.psmap_empty () in
      {
        env_tcenv = e;
        env_bindings = [];
        env_mlident_map = uu____2103;
        env_remove_typars =
          FStar_Extraction_ML_RemoveUnusedParameters.initial_env;
        mlpath_of_lid = uu____2106;
        env_fieldname_map = uu____2109;
        mlpath_of_fieldname = uu____2112;
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
    let uu____2131 =
      let uu____2138 =
        let uu____2139 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        FStar_Util.Inr uu____2139 in
      extend_lb env uu____2138 FStar_Syntax_Syntax.tun failwith_ty false in
    match uu____2131 with | (g, uu____2141, uu____2142) -> g