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
  fun projectee -> match projectee with | Bv _0 -> true | uu____116 -> false
let (__proj__Bv__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)) =
  fun projectee -> match projectee with | Bv _0 -> _0
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee -> match projectee with | Fv _0 -> true | uu____145 -> false
let (__proj__Fv__item___0 :
  binding -> (FStar_Syntax_Syntax.fv * exp_binding)) =
  fun projectee -> match projectee with | Fv _0 -> _0
type tydef =
  {
  tydef_fv: FStar_Syntax_Syntax.fv ;
  tydef_mlmodule_name: FStar_Extraction_ML_Syntax.mlsymbol Prims.list ;
  tydef_name: FStar_Extraction_ML_Syntax.mlsymbol ;
  tydef_meta: FStar_Extraction_ML_Syntax.metadata ;
  tydef_def: FStar_Extraction_ML_Syntax.mltyscheme }
let (__proj__Mktydef__item__tydef_fv : tydef -> FStar_Syntax_Syntax.fv) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_meta; tydef_def;_}
        -> tydef_fv
let (__proj__Mktydef__item__tydef_mlmodule_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol Prims.list) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_meta; tydef_def;_}
        -> tydef_mlmodule_name
let (__proj__Mktydef__item__tydef_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_meta; tydef_def;_}
        -> tydef_name
let (__proj__Mktydef__item__tydef_meta :
  tydef -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_meta; tydef_def;_}
        -> tydef_meta
let (__proj__Mktydef__item__tydef_def :
  tydef -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_meta; tydef_def;_}
        -> tydef_def
let (tydef_fv : tydef -> FStar_Syntax_Syntax.fv) = fun td -> td.tydef_fv
let (tydef_meta : tydef -> FStar_Extraction_ML_Syntax.metadata) =
  fun td -> td.tydef_meta
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
  tydef_declarations: Prims.bool FStar_Util.psmap ;
  currentModule: FStar_Extraction_ML_Syntax.mlpath }
let (__proj__Mkuenv__item__env_tcenv : uenv -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; tydef_declarations; currentModule;_} -> env_tcenv
let (__proj__Mkuenv__item__env_bindings : uenv -> binding Prims.list) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; tydef_declarations; currentModule;_} -> env_bindings
let (__proj__Mkuenv__item__env_mlident_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; tydef_declarations; currentModule;_} -> env_mlident_map
let (__proj__Mkuenv__item__env_remove_typars :
  uenv -> FStar_Extraction_ML_RemoveUnusedParameters.env_t) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; tydef_declarations; currentModule;_} -> env_remove_typars
let (__proj__Mkuenv__item__mlpath_of_lid :
  uenv -> FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; tydef_declarations; currentModule;_} -> mlpath_of_lid
let (__proj__Mkuenv__item__env_fieldname_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; tydef_declarations; currentModule;_} -> env_fieldname_map
let (__proj__Mkuenv__item__mlpath_of_fieldname :
  uenv -> FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; tydef_declarations; currentModule;_} ->
        mlpath_of_fieldname
let (__proj__Mkuenv__item__tydefs : uenv -> tydef Prims.list) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; tydef_declarations; currentModule;_} -> tydefs
let (__proj__Mkuenv__item__type_names :
  uenv ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; tydef_declarations; currentModule;_} -> type_names
let (__proj__Mkuenv__item__tydef_declarations :
  uenv -> Prims.bool FStar_Util.psmap) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; tydef_declarations; currentModule;_} ->
        tydef_declarations
let (__proj__Mkuenv__item__currentModule :
  uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
        mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
        type_names; tydef_declarations; currentModule;_} -> currentModule
let (tcenv_of_uenv : uenv -> FStar_TypeChecker_Env.env) =
  fun u -> u.env_tcenv
let (set_tcenv : uenv -> FStar_TypeChecker_Env.env -> uenv) =
  fun u ->
    fun t ->
      let uu___77_803 = u in
      {
        env_tcenv = t;
        env_bindings = (uu___77_803.env_bindings);
        env_mlident_map = (uu___77_803.env_mlident_map);
        env_remove_typars = (uu___77_803.env_remove_typars);
        mlpath_of_lid = (uu___77_803.mlpath_of_lid);
        env_fieldname_map = (uu___77_803.env_fieldname_map);
        mlpath_of_fieldname = (uu___77_803.mlpath_of_fieldname);
        tydefs = (uu___77_803.tydefs);
        type_names = (uu___77_803.type_names);
        tydef_declarations = (uu___77_803.tydef_declarations);
        currentModule = (uu___77_803.currentModule)
      }
let (current_module_of_uenv : uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun u -> u.currentModule
let (set_current_module : uenv -> FStar_Extraction_ML_Syntax.mlpath -> uenv)
  =
  fun u ->
    fun m ->
      let uu___85_819 = u in
      {
        env_tcenv = (uu___85_819.env_tcenv);
        env_bindings = (uu___85_819.env_bindings);
        env_mlident_map = (uu___85_819.env_mlident_map);
        env_remove_typars = (uu___85_819.env_remove_typars);
        mlpath_of_lid = (uu___85_819.mlpath_of_lid);
        env_fieldname_map = (uu___85_819.env_fieldname_map);
        mlpath_of_fieldname = (uu___85_819.mlpath_of_fieldname);
        tydefs = (uu___85_819.tydefs);
        type_names = (uu___85_819.type_names);
        tydef_declarations = (uu___85_819.tydef_declarations);
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
      let uu____854 = f u.env_remove_typars in
      match uu____854 with
      | (e, x) ->
          ((let uu___93_866 = u in
            {
              env_tcenv = (uu___93_866.env_tcenv);
              env_bindings = (uu___93_866.env_bindings);
              env_mlident_map = (uu___93_866.env_mlident_map);
              env_remove_typars = e;
              mlpath_of_lid = (uu___93_866.mlpath_of_lid);
              env_fieldname_map = (uu___93_866.env_fieldname_map);
              mlpath_of_fieldname = (uu___93_866.mlpath_of_fieldname);
              tydefs = (uu___93_866.tydefs);
              type_names = (uu___93_866.type_names);
              tydef_declarations = (uu___93_866.tydef_declarations);
              currentModule = (uu___93_866.currentModule)
            }), x)
let (bindings_of_uenv : uenv -> binding Prims.list) = fun u -> u.env_bindings
let (debug : uenv -> (unit -> unit) -> unit) =
  fun g ->
    fun f ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule in
      let uu____890 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction") in
      if uu____890 then f () else ()
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
               let uu____933 =
                 FStar_Util.format2 "%s -> %s" key (string_of_mlpath value) in
               uu____933 :: entries) [] in
    FStar_String.concat "\n" entries
let (try_lookup_fv :
  uenv ->
    FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun g ->
    fun fv ->
      FStar_Util.find_map g.env_bindings
        (fun uu___0_951 ->
           match uu___0_951 with
           | Fv (fv', t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____956 -> FStar_Pervasives_Native.None)
let (lookup_fv : uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun g ->
    fun fv ->
      let uu____967 = try_lookup_fv g fv in
      match uu____967 with
      | FStar_Pervasives_Native.None ->
          let uu____970 =
            let uu____971 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p in
            let uu____972 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____971
              uu____972 in
          failwith uu____970
      | FStar_Pervasives_Native.Some y -> y
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g ->
    fun bv ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___1_990 ->
             match uu___1_990 with
             | Bv (bv', r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____995 -> FStar_Pervasives_Native.None) in
      match x with
      | FStar_Pervasives_Native.None ->
          let uu____996 =
            let uu____997 =
              let uu____998 =
                FStar_Ident.range_of_id bv.FStar_Syntax_Syntax.ppname in
              FStar_Range.string_of_range uu____998 in
            let uu____999 = FStar_Syntax_Print.bv_to_string bv in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____997
              uu____999 in
          failwith uu____996
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
          let uu____1024 = lookup_bv g x in
          (uu____1024, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar x ->
          let uu____1028 =
            let uu____1029 = lookup_fv g x in FStar_Util.Inr uu____1029 in
          (uu____1028, (x.FStar_Syntax_Syntax.fv_qual))
      | uu____1032 -> failwith "Impossible: lookup_term for a non-name"
let (lookup_ty : uenv -> FStar_Syntax_Syntax.bv -> ty_binding) =
  fun g ->
    fun x ->
      let uu____1049 = lookup_bv g x in
      match uu____1049 with
      | FStar_Util.Inl ty -> ty
      | uu____1051 -> failwith "Expected a type name"
let (lookup_tydef :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env ->
    fun uu____1063 ->
      match uu____1063 with
      | (module_name, ty_name) ->
          FStar_Util.find_map env.tydefs
            (fun tydef1 ->
               if
                 (ty_name = tydef1.tydef_name) &&
                   (module_name = tydef1.tydef_mlmodule_name)
               then FStar_Pervasives_Native.Some (tydef1.tydef_def)
               else FStar_Pervasives_Native.None)
let (has_tydef_declaration : uenv -> FStar_Ident.lident -> Prims.bool) =
  fun u ->
    fun l ->
      let uu____1091 =
        let uu____1094 = FStar_Ident.string_of_lid l in
        FStar_Util.psmap_try_find u.tydef_declarations uu____1094 in
      match uu____1091 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some b -> b
let (mlpath_of_lident :
  uenv -> FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlpath) =
  fun g ->
    fun x ->
      let uu____1106 =
        let uu____1109 = FStar_Ident.string_of_lid x in
        FStar_Util.psmap_try_find g.mlpath_of_lid uu____1109 in
      match uu____1106 with
      | FStar_Pervasives_Native.None ->
          (debug g
             (fun uu____1114 ->
                (let uu____1116 = FStar_Ident.string_of_lid x in
                 FStar_Util.print1 "Identifier not found: %s" uu____1116);
                (let uu____1117 = print_mlpath_map g in
                 FStar_Util.print1 "Env is \n%s\n" uu____1117));
           (let uu____1118 =
              let uu____1119 = FStar_Ident.string_of_lid x in
              Prims.op_Hat "Identifier not found: " uu____1119 in
            failwith uu____1118))
      | FStar_Pervasives_Native.Some mlp -> mlp
let (is_type_name : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g ->
    fun fv ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some
           (fun uu____1144 ->
              match uu____1144 with
              | (x, uu____1150) -> FStar_Syntax_Syntax.fv_eq fv x))
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
    fun uu____1178 ->
      match uu____1178 with
      | (type_name, fn) ->
          let key =
            let uu____1186 =
              let uu____1187 = FStar_Ident.ids_of_lid type_name in
              FStar_List.append uu____1187 [fn] in
            FStar_Ident.lid_of_ids uu____1186 in
          let uu____1190 =
            let uu____1193 = FStar_Ident.string_of_lid key in
            FStar_Util.psmap_try_find g.mlpath_of_fieldname uu____1193 in
          (match uu____1190 with
           | FStar_Pervasives_Native.None ->
               let uu____1194 =
                 let uu____1195 = FStar_Ident.string_of_lid key in
                 Prims.op_Hat "Field name not found: " uu____1195 in
               failwith uu____1194
           | FStar_Pervasives_Native.Some mlp -> mlp)
let (initial_mlident_map : unit -> Prims.string FStar_Util.psmap) =
  let map = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  fun uu____1216 ->
    let uu____1217 = FStar_ST.op_Bang map in
    match uu____1217 with
    | FStar_Pervasives_Native.Some m -> m
    | FStar_Pervasives_Native.None ->
        let m =
          let uu____1248 =
            let uu____1251 = FStar_Options.codegen () in
            match uu____1251 with
            | FStar_Pervasives_Native.Some (FStar_Options.FSharp) ->
                FStar_Extraction_ML_Syntax.fsharpkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.OCaml) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Plugin) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Kremlin) ->
                FStar_Extraction_ML_Syntax.kremlin_keywords ()
            | FStar_Pervasives_Native.None -> [] in
          let uu____1256 = FStar_Util.psmap_empty () in
          FStar_List.fold_right
            (fun x -> fun m -> FStar_Util.psmap_add m x "") uu____1248
            uu____1256 in
        (FStar_ST.op_Colon_Equals map (FStar_Pervasives_Native.Some m); m)
let (rename_conventional : Prims.string -> Prims.bool -> Prims.string) =
  fun s ->
    fun is_local_type_variable ->
      let cs = FStar_String.list_of_string s in
      let sanitize_typ uu____1304 =
        let valid_rest c = FStar_Util.is_letter_or_digit c in
        let aux cs1 =
          FStar_List.map
            (fun x ->
               let uu____1326 = valid_rest x in if uu____1326 then x else 117)
            cs1 in
        let uu____1328 = let uu____1329 = FStar_List.hd cs in uu____1329 = 39 in
        if uu____1328
        then
          let uu____1332 = FStar_List.hd cs in
          let uu____1333 =
            let uu____1336 = FStar_List.tail cs in aux uu____1336 in
          uu____1332 :: uu____1333
        else (let uu____1340 = aux cs in 39 :: uu____1340) in
      let sanitize_term uu____1350 =
        let valid c =
          ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39) in
        let cs' =
          FStar_List.fold_right
            (fun c ->
               fun cs1 ->
                 let uu____1369 =
                   let uu____1372 = valid c in
                   if uu____1372 then [c] else [95; 95] in
                 FStar_List.append uu____1369 cs1) cs [] in
        match cs' with
        | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
        | uu____1382 -> cs in
      let uu____1385 =
        if is_local_type_variable then sanitize_typ () else sanitize_term () in
      FStar_String.string_of_list uu____1385
let (root_name_of_bv :
  FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlident) =
  fun x ->
    let uu____1396 =
      (let uu____1399 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname in
       FStar_Util.starts_with uu____1399 FStar_Ident.reserved_prefix) ||
        (FStar_Syntax_Syntax.is_null_bv x) in
    if uu____1396
    then
      let uu____1400 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname in
      let uu____1401 =
        let uu____1402 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.op_Hat "_" uu____1402 in
      Prims.op_Hat uu____1400 uu____1401
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
              (let uu____1448 = FStar_Util.string_of_int i in
               Prims.op_Hat root_name1 uu____1448) in
          let uu____1449 =
            FStar_Util.psmap_try_find ml_ident_map target_mlident in
          match uu____1449 with
          | FStar_Pervasives_Native.Some x ->
              aux (i + Prims.int_one) root_name1
          | FStar_Pervasives_Native.None ->
              let map = FStar_Util.psmap_add ml_ident_map target_mlident "" in
              (target_mlident, map) in
        let mlident = rename_conventional root_name is_local_type_variable in
        if is_local_type_variable
        then
          let uu____1471 =
            let uu____1478 = FStar_Util.substring_from mlident Prims.int_one in
            aux Prims.int_zero uu____1478 in
          match uu____1471 with | (nm, map) -> ((Prims.op_Hat "'" nm), map)
        else aux Prims.int_zero mlident
let (mlns_of_lid : FStar_Ident.lident -> Prims.string Prims.list) =
  fun x ->
    let uu____1501 = FStar_Ident.ns_of_lid x in
    FStar_List.map FStar_Ident.string_of_id uu____1501
let (new_mlpath_of_lident :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g ->
    fun x ->
      let uu____1522 =
        let uu____1527 =
          FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid in
        if uu____1527
        then
          let uu____1532 =
            let uu____1533 =
              let uu____1534 = FStar_Ident.ident_of_lid x in
              FStar_Ident.string_of_id uu____1534 in
            ([], uu____1533) in
          (uu____1532, g)
        else
          (let uu____1538 =
             let uu____1545 =
               let uu____1546 = FStar_Ident.ident_of_lid x in
               FStar_Ident.string_of_id uu____1546 in
             find_uniq g.env_mlident_map uu____1545 false in
           match uu____1538 with
           | (name, map) ->
               let g1 =
                 let uu___262_1558 = g in
                 {
                   env_tcenv = (uu___262_1558.env_tcenv);
                   env_bindings = (uu___262_1558.env_bindings);
                   env_mlident_map = map;
                   env_remove_typars = (uu___262_1558.env_remove_typars);
                   mlpath_of_lid = (uu___262_1558.mlpath_of_lid);
                   env_fieldname_map = (uu___262_1558.env_fieldname_map);
                   mlpath_of_fieldname = (uu___262_1558.mlpath_of_fieldname);
                   tydefs = (uu___262_1558.tydefs);
                   type_names = (uu___262_1558.type_names);
                   tydef_declarations = (uu___262_1558.tydef_declarations);
                   currentModule = (uu___262_1558.currentModule)
                 } in
               let uu____1559 =
                 let uu____1560 = mlns_of_lid x in (uu____1560, name) in
               (uu____1559, g1)) in
      match uu____1522 with
      | (mlp, g1) ->
          let g2 =
            let uu___268_1572 = g1 in
            let uu____1573 =
              let uu____1576 = FStar_Ident.string_of_lid x in
              FStar_Util.psmap_add g1.mlpath_of_lid uu____1576 mlp in
            {
              env_tcenv = (uu___268_1572.env_tcenv);
              env_bindings = (uu___268_1572.env_bindings);
              env_mlident_map = (uu___268_1572.env_mlident_map);
              env_remove_typars = (uu___268_1572.env_remove_typars);
              mlpath_of_lid = uu____1573;
              env_fieldname_map = (uu___268_1572.env_fieldname_map);
              mlpath_of_fieldname = (uu___268_1572.mlpath_of_fieldname);
              tydefs = (uu___268_1572.tydefs);
              type_names = (uu___268_1572.type_names);
              tydef_declarations = (uu___268_1572.tydef_declarations);
              currentModule = (uu___268_1572.currentModule)
            } in
          (mlp, g2)
let (extend_ty : uenv -> FStar_Syntax_Syntax.bv -> Prims.bool -> uenv) =
  fun g ->
    fun a ->
      fun map_to_top ->
        let is_local_type_variable = Prims.op_Negation map_to_top in
        let uu____1593 =
          let uu____1600 = root_name_of_bv a in
          find_uniq g.env_mlident_map uu____1600 is_local_type_variable in
        match uu____1593 with
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
            let uu___285_1613 = g in
            {
              env_tcenv = tcenv;
              env_bindings = gamma;
              env_mlident_map = mlident_map;
              env_remove_typars = (uu___285_1613.env_remove_typars);
              mlpath_of_lid = (uu___285_1613.mlpath_of_lid);
              env_fieldname_map = (uu___285_1613.env_fieldname_map);
              mlpath_of_fieldname = (uu___285_1613.mlpath_of_fieldname);
              tydefs = (uu___285_1613.tydefs);
              type_names = (uu___285_1613.type_names);
              tydef_declarations = (uu___285_1613.tydef_declarations);
              currentModule = (uu___285_1613.currentModule)
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
              | uu____1653 -> FStar_Extraction_ML_Syntax.MLTY_Top in
            let uu____1654 =
              let uu____1661 = root_name_of_bv x in
              find_uniq g.env_mlident_map uu____1661 false in
            match uu____1654 with
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
                  let uu____1687 = FStar_Syntax_Syntax.binders_of_list [x] in
                  FStar_TypeChecker_Env.push_binders g.env_tcenv uu____1687 in
                ((let uu___311_1689 = g in
                  {
                    env_tcenv = tcenv;
                    env_bindings = gamma;
                    env_mlident_map = mlident_map;
                    env_remove_typars = (uu___311_1689.env_remove_typars);
                    mlpath_of_lid = (uu___311_1689.mlpath_of_lid);
                    env_fieldname_map = (uu___311_1689.env_fieldname_map);
                    mlpath_of_fieldname = (uu___311_1689.mlpath_of_fieldname);
                    tydefs = (uu___311_1689.tydefs);
                    type_names = (uu___311_1689.type_names);
                    tydef_declarations = (uu___311_1689.tydef_declarations);
                    currentModule = (uu___311_1689.currentModule)
                  }), mlident, exp_binding1)
let (new_mlident : uenv -> (uenv * FStar_Extraction_ML_Syntax.mlident)) =
  fun g ->
    let ml_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
    let x =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.tun in
    let uu____1705 =
      extend_bv g x ([], FStar_Extraction_ML_Syntax.MLTY_Top) false false in
    match uu____1705 with | (g1, id, uu____1718) -> (g1, id)
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
                let uu____1765 = mltyFvars t1 in
                let uu____1768 = mltyFvars t2 in
                FStar_List.append uu____1765 uu____1768
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
            let uu____1809 = mltyFvars (FStar_Pervasives_Native.snd tys) in
            subsetMlidents uu____1809 (FStar_Pervasives_Native.fst tys) in
          let uu____1812 = tySchemeIsClosed t_x in
          if uu____1812
          then
            let ml_ty =
              match t_x with
              | ([], t) -> t
              | uu____1821 -> FStar_Extraction_ML_Syntax.MLTY_Top in
            let uu____1822 =
              new_mlpath_of_lident g
                (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____1822 with
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
                ((let uu___370_1853 = g1 in
                  {
                    env_tcenv = (uu___370_1853.env_tcenv);
                    env_bindings = gamma;
                    env_mlident_map = mlident_map;
                    env_remove_typars = (uu___370_1853.env_remove_typars);
                    mlpath_of_lid = (uu___370_1853.mlpath_of_lid);
                    env_fieldname_map = (uu___370_1853.env_fieldname_map);
                    mlpath_of_fieldname = (uu___370_1853.mlpath_of_fieldname);
                    tydefs = (uu___370_1853.tydefs);
                    type_names = (uu___370_1853.type_names);
                    tydef_declarations = (uu___370_1853.tydef_declarations);
                    currentModule = (uu___370_1853.currentModule)
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
        FStar_Extraction_ML_Syntax.metadata ->
          (tydef * FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g ->
    fun fv ->
      fun ts ->
        fun meta ->
          let uu____1932 =
            new_mlpath_of_lident g
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____1932 with
          | (name, g1) ->
              let tydef1 =
                {
                  tydef_fv = fv;
                  tydef_mlmodule_name = (FStar_Pervasives_Native.fst name);
                  tydef_name = (FStar_Pervasives_Native.snd name);
                  tydef_meta = meta;
                  tydef_def = ts
                } in
              (tydef1, name,
                (let uu___393_1951 = g1 in
                 {
                   env_tcenv = (uu___393_1951.env_tcenv);
                   env_bindings = (uu___393_1951.env_bindings);
                   env_mlident_map = (uu___393_1951.env_mlident_map);
                   env_remove_typars = (uu___393_1951.env_remove_typars);
                   mlpath_of_lid = (uu___393_1951.mlpath_of_lid);
                   env_fieldname_map = (uu___393_1951.env_fieldname_map);
                   mlpath_of_fieldname = (uu___393_1951.mlpath_of_fieldname);
                   tydefs = (tydef1 :: (g1.tydefs));
                   type_names = ((fv, name) :: (g1.type_names));
                   tydef_declarations = (uu___393_1951.tydef_declarations);
                   currentModule = (uu___393_1951.currentModule)
                 }))
let (extend_with_tydef_declaration : uenv -> FStar_Ident.lident -> uenv) =
  fun u ->
    fun l ->
      let uu___397_1966 = u in
      let uu____1967 =
        let uu____1970 = FStar_Ident.string_of_lid l in
        FStar_Util.psmap_add u.tydef_declarations uu____1970 true in
      {
        env_tcenv = (uu___397_1966.env_tcenv);
        env_bindings = (uu___397_1966.env_bindings);
        env_mlident_map = (uu___397_1966.env_mlident_map);
        env_remove_typars = (uu___397_1966.env_remove_typars);
        mlpath_of_lid = (uu___397_1966.mlpath_of_lid);
        env_fieldname_map = (uu___397_1966.env_fieldname_map);
        mlpath_of_fieldname = (uu___397_1966.mlpath_of_fieldname);
        tydefs = (uu___397_1966.tydefs);
        type_names = (uu___397_1966.type_names);
        tydef_declarations = uu____1967;
        currentModule = (uu___397_1966.currentModule)
      }
let (extend_type_name :
  uenv ->
    FStar_Syntax_Syntax.fv -> (FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g ->
    fun fv ->
      let uu____1989 =
        new_mlpath_of_lident g
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      match uu____1989 with
      | (name, g1) ->
          (name,
            (let uu___404_2001 = g1 in
             {
               env_tcenv = (uu___404_2001.env_tcenv);
               env_bindings = (uu___404_2001.env_bindings);
               env_mlident_map = (uu___404_2001.env_mlident_map);
               env_remove_typars = (uu___404_2001.env_remove_typars);
               mlpath_of_lid = (uu___404_2001.mlpath_of_lid);
               env_fieldname_map = (uu___404_2001.env_fieldname_map);
               mlpath_of_fieldname = (uu___404_2001.mlpath_of_fieldname);
               tydefs = (uu___404_2001.tydefs);
               type_names = ((fv, name) :: (g1.type_names));
               tydef_declarations = (uu___404_2001.tydef_declarations);
               currentModule = (uu___404_2001.currentModule)
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
            let uu____2035 = FStar_Ident.id_of_text nm in
            FStar_Syntax_Util.mk_field_projector_name_from_ident
              ed.FStar_Syntax_Syntax.mname uu____2035 in
          let uu____2036 =
            let uu____2043 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            extend_fv g uu____2043 ts false in
          match uu____2036 with
          | (g1, mlid, exp_b) ->
              let mlp =
                let uu____2062 = mlns_of_lid lid in (uu____2062, mlid) in
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
            let uu____2096 =
              FStar_Ident.ident_of_lid a.FStar_Syntax_Syntax.action_name in
            FStar_Ident.string_of_id uu____2096 in
          let module_name =
            FStar_Ident.ns_of_lid ed.FStar_Syntax_Syntax.mname in
          let lid =
            let uu____2099 =
              let uu____2100 =
                let uu____2103 = FStar_Ident.id_of_text nm in [uu____2103] in
              FStar_List.append module_name uu____2100 in
            FStar_Ident.lid_of_ids uu____2099 in
          let uu____2104 =
            let uu____2111 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            extend_fv g uu____2111 ts false in
          match uu____2104 with
          | (g1, mlid, exp_b) ->
              let mlp =
                let uu____2130 = mlns_of_lid lid in (uu____2130, mlid) in
              (mlp, lid, exp_b, g1)
let (extend_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      (FStar_Extraction_ML_Syntax.mlident * uenv))
  =
  fun g ->
    fun uu____2152 ->
      match uu____2152 with
      | (type_name, fn) ->
          let key =
            let uu____2164 =
              let uu____2165 = FStar_Ident.ids_of_lid type_name in
              FStar_List.append uu____2165 [fn] in
            FStar_Ident.lid_of_ids uu____2164 in
          let uu____2168 =
            let uu____2175 = FStar_Ident.string_of_id fn in
            find_uniq g.env_fieldname_map uu____2175 false in
          (match uu____2168 with
           | (name, fieldname_map) ->
               let ns = mlns_of_lid type_name in
               let mlp = (ns, name) in
               let g1 =
                 let uu___438_2199 = g in
                 let uu____2200 =
                   let uu____2203 = FStar_Ident.string_of_lid key in
                   FStar_Util.psmap_add g.mlpath_of_fieldname uu____2203 mlp in
                 {
                   env_tcenv = (uu___438_2199.env_tcenv);
                   env_bindings = (uu___438_2199.env_bindings);
                   env_mlident_map = (uu___438_2199.env_mlident_map);
                   env_remove_typars = (uu___438_2199.env_remove_typars);
                   mlpath_of_lid = (uu___438_2199.mlpath_of_lid);
                   env_fieldname_map = fieldname_map;
                   mlpath_of_fieldname = uu____2200;
                   tydefs = (uu___438_2199.tydefs);
                   type_names = (uu___438_2199.type_names);
                   tydef_declarations = (uu___438_2199.tydef_declarations);
                   currentModule = (uu___438_2199.currentModule)
                 } in
               (name, g1))
let (extend_with_module_name :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g ->
    fun m ->
      let ns = mlns_of_lid m in
      let p =
        let uu____2222 = FStar_Ident.ident_of_lid m in
        FStar_Ident.string_of_id uu____2222 in
      ((ns, p), g)
let (exit_module : uenv -> uenv) =
  fun g ->
    let uu___446_2230 = g in
    let uu____2231 = initial_mlident_map () in
    let uu____2234 = initial_mlident_map () in
    {
      env_tcenv = (uu___446_2230.env_tcenv);
      env_bindings = (uu___446_2230.env_bindings);
      env_mlident_map = uu____2231;
      env_remove_typars = (uu___446_2230.env_remove_typars);
      mlpath_of_lid = (uu___446_2230.mlpath_of_lid);
      env_fieldname_map = uu____2234;
      mlpath_of_fieldname = (uu___446_2230.mlpath_of_fieldname);
      tydefs = (uu___446_2230.tydefs);
      type_names = (uu___446_2230.type_names);
      tydef_declarations = (uu___446_2230.tydef_declarations);
      currentModule = (uu___446_2230.currentModule)
    }
let (new_uenv : FStar_TypeChecker_Env.env -> uenv) =
  fun e ->
    let env =
      let uu____2243 = initial_mlident_map () in
      let uu____2246 = FStar_Util.psmap_empty () in
      let uu____2249 = initial_mlident_map () in
      let uu____2252 = FStar_Util.psmap_empty () in
      let uu____2255 = FStar_Util.psmap_empty () in
      {
        env_tcenv = e;
        env_bindings = [];
        env_mlident_map = uu____2243;
        env_remove_typars =
          FStar_Extraction_ML_RemoveUnusedParameters.initial_env;
        mlpath_of_lid = uu____2246;
        env_fieldname_map = uu____2249;
        mlpath_of_fieldname = uu____2252;
        tydefs = [];
        type_names = [];
        tydef_declarations = uu____2255;
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
    let uu____2274 =
      let uu____2281 =
        let uu____2282 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        FStar_Util.Inr uu____2282 in
      extend_lb env uu____2281 FStar_Syntax_Syntax.tun failwith_ty false in
    match uu____2274 with | (g, uu____2284, uu____2285) -> g