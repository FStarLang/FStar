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
  fun projectee -> match projectee with | Bv _0 -> true | uu____133 -> false
let (__proj__Bv__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)) =
  fun projectee -> match projectee with | Bv _0 -> _0
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee -> match projectee with | Fv _0 -> true | uu____168 -> false
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
      let uu___70_786 = u in
      {
        env_tcenv = t;
        env_bindings = (uu___70_786.env_bindings);
        env_mlident_map = (uu___70_786.env_mlident_map);
        env_remove_typars = (uu___70_786.env_remove_typars);
        mlpath_of_lid = (uu___70_786.mlpath_of_lid);
        env_fieldname_map = (uu___70_786.env_fieldname_map);
        mlpath_of_fieldname = (uu___70_786.mlpath_of_fieldname);
        tydefs = (uu___70_786.tydefs);
        type_names = (uu___70_786.type_names);
        currentModule = (uu___70_786.currentModule)
      }
let (current_module_of_uenv : uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun u -> u.currentModule
let (set_current_module : uenv -> FStar_Extraction_ML_Syntax.mlpath -> uenv)
  =
  fun u ->
    fun m ->
      let uu___78_804 = u in
      {
        env_tcenv = (uu___78_804.env_tcenv);
        env_bindings = (uu___78_804.env_bindings);
        env_mlident_map = (uu___78_804.env_mlident_map);
        env_remove_typars = (uu___78_804.env_remove_typars);
        mlpath_of_lid = (uu___78_804.mlpath_of_lid);
        env_fieldname_map = (uu___78_804.env_fieldname_map);
        mlpath_of_fieldname = (uu___78_804.mlpath_of_fieldname);
        tydefs = (uu___78_804.tydefs);
        type_names = (uu___78_804.type_names);
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
      let uu____840 = f u.env_remove_typars in
      match uu____840 with
      | (e, x) ->
          ((let uu___86_852 = u in
            {
              env_tcenv = (uu___86_852.env_tcenv);
              env_bindings = (uu___86_852.env_bindings);
              env_mlident_map = (uu___86_852.env_mlident_map);
              env_remove_typars = e;
              mlpath_of_lid = (uu___86_852.mlpath_of_lid);
              env_fieldname_map = (uu___86_852.env_fieldname_map);
              mlpath_of_fieldname = (uu___86_852.mlpath_of_fieldname);
              tydefs = (uu___86_852.tydefs);
              type_names = (uu___86_852.type_names);
              currentModule = (uu___86_852.currentModule)
            }), x)
let (bindings_of_uenv : uenv -> binding Prims.list) = fun u -> u.env_bindings
let (debug : uenv -> (unit -> unit) -> unit) =
  fun g ->
    fun f ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule in
      let uu____879 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction") in
      if uu____879 then f () else ()
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
               let uu____943 =
                 FStar_Util.format2 "%s -> %s" key (string_of_mlpath value) in
               uu____943 :: entries) [] in
    FStar_String.concat "\n" entries
let (try_lookup_fv :
  uenv ->
    FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun g ->
    fun fv ->
      FStar_Util.find_map g.env_bindings
        (fun uu___0_967 ->
           match uu___0_967 with
           | Fv (fv', t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____972 -> FStar_Pervasives_Native.None)
let (lookup_fv : uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun g ->
    fun fv ->
      let uu____984 = try_lookup_fv g fv in
      match uu____984 with
      | FStar_Pervasives_Native.None ->
          let uu____987 =
            let uu____989 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p in
            let uu____991 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____989
              uu____991 in
          failwith uu____987
      | FStar_Pervasives_Native.Some y -> y
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g ->
    fun bv ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___1_1012 ->
             match uu___1_1012 with
             | Bv (bv', r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____1017 -> FStar_Pervasives_Native.None) in
      match x with
      | FStar_Pervasives_Native.None ->
          let uu____1018 =
            let uu____1020 =
              let uu____1022 =
                FStar_Ident.range_of_id bv.FStar_Syntax_Syntax.ppname in
              FStar_Range.string_of_range uu____1022 in
            let uu____1023 = FStar_Syntax_Print.bv_to_string bv in
            FStar_Util.format2 "(%s) bound Variable %s not found\n"
              uu____1020 uu____1023 in
          failwith uu____1018
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
          let uu____1051 = lookup_bv g x in
          (uu____1051, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar x ->
          let uu____1055 =
            let uu____1056 = lookup_fv g x in FStar_Util.Inr uu____1056 in
          (uu____1055, (x.FStar_Syntax_Syntax.fv_qual))
      | uu____1059 -> failwith "Impossible: lookup_term for a non-name"
let (lookup_ty : uenv -> FStar_Syntax_Syntax.bv -> ty_binding) =
  fun g ->
    fun x ->
      let uu____1078 = lookup_bv g x in
      match uu____1078 with
      | FStar_Util.Inl ty -> ty
      | uu____1080 -> failwith "Expected a type name"
let (lookup_tydef :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env ->
    fun uu____1094 ->
      match uu____1094 with
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
      let uu____1131 =
        let uu____1134 = FStar_Ident.string_of_lid x in
        FStar_Util.psmap_try_find g.mlpath_of_lid uu____1134 in
      match uu____1131 with
      | FStar_Pervasives_Native.None ->
          (debug g
             (fun uu____1140 ->
                (let uu____1142 = FStar_Ident.string_of_lid x in
                 FStar_Util.print1 "Identifier not found: %s" uu____1142);
                (let uu____1145 = print_mlpath_map g in
                 FStar_Util.print1 "Env is \n%s\n" uu____1145));
           (let uu____1148 =
              let uu____1150 = FStar_Ident.string_of_lid x in
              Prims.op_Hat "Identifier not found: " uu____1150 in
            failwith uu____1148))
      | FStar_Pervasives_Native.Some mlp -> mlp
let (is_type_name : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g ->
    fun fv ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some
           (fun uu____1180 ->
              match uu____1180 with
              | (x, uu____1187) -> FStar_Syntax_Syntax.fv_eq fv x))
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
    fun uu____1219 ->
      match uu____1219 with
      | (type_name, fn) ->
          let key =
            let uu____1227 =
              let uu____1228 = FStar_Ident.ids_of_lid type_name in
              FStar_List.append uu____1228 [fn] in
            FStar_Ident.lid_of_ids uu____1227 in
          let uu____1231 =
            let uu____1234 = FStar_Ident.string_of_lid key in
            FStar_Util.psmap_try_find g.mlpath_of_fieldname uu____1234 in
          (match uu____1231 with
           | FStar_Pervasives_Native.None ->
               let uu____1236 =
                 let uu____1238 = FStar_Ident.string_of_lid key in
                 Prims.op_Hat "Field name not found: " uu____1238 in
               failwith uu____1236
           | FStar_Pervasives_Native.Some mlp -> mlp)
let (initial_mlident_map : unit -> Prims.string FStar_Util.psmap) =
  let map = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  fun uu____1266 ->
    let uu____1267 = FStar_ST.op_Bang map in
    match uu____1267 with
    | FStar_Pervasives_Native.Some m -> m
    | FStar_Pervasives_Native.None ->
        let m =
          let uu____1319 =
            let uu____1323 = FStar_Options.codegen () in
            match uu____1323 with
            | FStar_Pervasives_Native.Some (FStar_Options.FSharp) ->
                FStar_Extraction_ML_Syntax.fsharpkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.OCaml) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Plugin) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Kremlin) ->
                FStar_Extraction_ML_Syntax.kremlin_keywords ()
            | FStar_Pervasives_Native.None -> [] in
          let uu____1331 = FStar_Util.psmap_empty () in
          FStar_List.fold_right
            (fun x -> fun m -> FStar_Util.psmap_add m x "") uu____1319
            uu____1331 in
        (FStar_ST.op_Colon_Equals map (FStar_Pervasives_Native.Some m); m)
let (rename_conventional : Prims.string -> Prims.bool -> Prims.string) =
  fun s ->
    fun is_local_type_variable ->
      let cs = FStar_String.list_of_string s in
      let sanitize_typ uu____1412 =
        let valid_rest c = FStar_Util.is_letter_or_digit c in
        let aux cs1 =
          FStar_List.map
            (fun x ->
               let uu____1443 = valid_rest x in if uu____1443 then x else 117)
            cs1 in
        let uu____1450 = let uu____1452 = FStar_List.hd cs in uu____1452 = 39 in
        if uu____1450
        then
          let uu____1461 = FStar_List.hd cs in
          let uu____1464 =
            let uu____1468 = FStar_List.tail cs in aux uu____1468 in
          uu____1461 :: uu____1464
        else (let uu____1476 = aux cs in 39 :: uu____1476) in
      let sanitize_term uu____1490 =
        let valid c =
          ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39) in
        let cs' =
          FStar_List.fold_right
            (fun c ->
               fun cs1 ->
                 let uu____1521 =
                   let uu____1525 = valid c in
                   if uu____1525 then [c] else [95; 95] in
                 FStar_List.append uu____1521 cs1) cs [] in
        match cs' with
        | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
        | uu____1557 -> cs in
      let uu____1561 =
        if is_local_type_variable then sanitize_typ () else sanitize_term () in
      FStar_String.string_of_list uu____1561
let (root_name_of_bv :
  FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlident) =
  fun x ->
    let uu____1579 =
      (let uu____1583 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname in
       FStar_Util.starts_with uu____1583 FStar_Ident.reserved_prefix) ||
        (FStar_Syntax_Syntax.is_null_bv x) in
    if uu____1579
    then
      let uu____1587 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname in
      let uu____1589 =
        let uu____1591 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index in
        Prims.op_Hat "_" uu____1591 in
      Prims.op_Hat uu____1587 uu____1589
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
              (let uu____1661 = FStar_Util.string_of_int i in
               Prims.op_Hat root_name1 uu____1661) in
          let uu____1663 =
            FStar_Util.psmap_try_find ml_ident_map target_mlident in
          match uu____1663 with
          | FStar_Pervasives_Native.Some x ->
              aux (i + Prims.int_one) root_name1
          | FStar_Pervasives_Native.None ->
              let map = FStar_Util.psmap_add ml_ident_map target_mlident "" in
              (target_mlident, map) in
        let mlident = rename_conventional root_name is_local_type_variable in
        if is_local_type_variable
        then
          let uu____1702 =
            let uu____1711 = FStar_Util.substring_from mlident Prims.int_one in
            aux Prims.int_zero uu____1711 in
          match uu____1702 with | (nm, map) -> ((Prims.op_Hat "'" nm), map)
        else aux Prims.int_zero mlident
let (mlns_of_lid : FStar_Ident.lident -> Prims.string Prims.list) =
  fun x ->
    let uu____1750 = FStar_Ident.ns_of_lid x in
    FStar_List.map FStar_Ident.string_of_id uu____1750
let (new_mlpath_of_lident :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g ->
    fun x ->
      let uu____1773 =
        let uu____1778 =
          FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid in
        if uu____1778
        then
          let uu____1785 =
            let uu____1786 =
              let uu____1788 = FStar_Ident.ident_of_lid x in
              FStar_Ident.string_of_id uu____1788 in
            ([], uu____1786) in
          (uu____1785, g)
        else
          (let uu____1796 =
             let uu____1805 =
               let uu____1807 = FStar_Ident.ident_of_lid x in
               FStar_Ident.string_of_id uu____1807 in
             find_uniq g.env_mlident_map uu____1805 false in
           match uu____1796 with
           | (name, map) ->
               let g1 =
                 let uu___250_1824 = g in
                 {
                   env_tcenv = (uu___250_1824.env_tcenv);
                   env_bindings = (uu___250_1824.env_bindings);
                   env_mlident_map = map;
                   env_remove_typars = (uu___250_1824.env_remove_typars);
                   mlpath_of_lid = (uu___250_1824.mlpath_of_lid);
                   env_fieldname_map = (uu___250_1824.env_fieldname_map);
                   mlpath_of_fieldname = (uu___250_1824.mlpath_of_fieldname);
                   tydefs = (uu___250_1824.tydefs);
                   type_names = (uu___250_1824.type_names);
                   currentModule = (uu___250_1824.currentModule)
                 } in
               let uu____1825 =
                 let uu____1826 = mlns_of_lid x in (uu____1826, name) in
               (uu____1825, g1)) in
      match uu____1773 with
      | (mlp, g1) ->
          let g2 =
            let uu___256_1841 = g1 in
            let uu____1842 =
              let uu____1845 = FStar_Ident.string_of_lid x in
              FStar_Util.psmap_add g1.mlpath_of_lid uu____1845 mlp in
            {
              env_tcenv = (uu___256_1841.env_tcenv);
              env_bindings = (uu___256_1841.env_bindings);
              env_mlident_map = (uu___256_1841.env_mlident_map);
              env_remove_typars = (uu___256_1841.env_remove_typars);
              mlpath_of_lid = uu____1842;
              env_fieldname_map = (uu___256_1841.env_fieldname_map);
              mlpath_of_fieldname = (uu___256_1841.mlpath_of_fieldname);
              tydefs = (uu___256_1841.tydefs);
              type_names = (uu___256_1841.type_names);
              currentModule = (uu___256_1841.currentModule)
            } in
          (mlp, g2)
let (extend_ty : uenv -> FStar_Syntax_Syntax.bv -> Prims.bool -> uenv) =
  fun g ->
    fun a ->
      fun map_to_top ->
        let is_local_type_variable = Prims.op_Negation map_to_top in
        let uu____1867 =
          let uu____1876 = root_name_of_bv a in
          find_uniq g.env_mlident_map uu____1876 is_local_type_variable in
        match uu____1867 with
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
            let uu___273_1896 = g in
            {
              env_tcenv = tcenv;
              env_bindings = gamma;
              env_mlident_map = mlident_map;
              env_remove_typars = (uu___273_1896.env_remove_typars);
              mlpath_of_lid = (uu___273_1896.mlpath_of_lid);
              env_fieldname_map = (uu___273_1896.env_fieldname_map);
              mlpath_of_fieldname = (uu___273_1896.mlpath_of_fieldname);
              tydefs = (uu___273_1896.tydefs);
              type_names = (uu___273_1896.type_names);
              currentModule = (uu___273_1896.currentModule)
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
              | uu____1944 -> FStar_Extraction_ML_Syntax.MLTY_Top in
            let uu____1945 =
              let uu____1954 = root_name_of_bv x in
              find_uniq g.env_mlident_map uu____1954 false in
            match uu____1945 with
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
                  let uu____1993 = FStar_Syntax_Syntax.binders_of_list [x] in
                  FStar_TypeChecker_Env.push_binders g.env_tcenv uu____1993 in
                ((let uu___299_1996 = g in
                  {
                    env_tcenv = tcenv;
                    env_bindings = gamma;
                    env_mlident_map = mlident_map;
                    env_remove_typars = (uu___299_1996.env_remove_typars);
                    mlpath_of_lid = (uu___299_1996.mlpath_of_lid);
                    env_fieldname_map = (uu___299_1996.env_fieldname_map);
                    mlpath_of_fieldname = (uu___299_1996.mlpath_of_fieldname);
                    tydefs = (uu___299_1996.tydefs);
                    type_names = (uu___299_1996.type_names);
                    currentModule = (uu___299_1996.currentModule)
                  }), mlident, exp_binding1)
let (new_mlident : uenv -> (uenv * FStar_Extraction_ML_Syntax.mlident)) =
  fun g ->
    let ml_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
    let x =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.tun in
    let uu____2015 =
      extend_bv g x ([], FStar_Extraction_ML_Syntax.MLTY_Top) false false in
    match uu____2015 with | (g1, id, uu____2033) -> (g1, id)
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
                let uu____2093 = mltyFvars t1 in
                let uu____2097 = mltyFvars t2 in
                FStar_List.append uu____2093 uu____2097
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
            let uu____2158 = mltyFvars (FStar_Pervasives_Native.snd tys) in
            subsetMlidents uu____2158 (FStar_Pervasives_Native.fst tys) in
          let uu____2162 = tySchemeIsClosed t_x in
          if uu____2162
          then
            let ml_ty =
              match t_x with
              | ([], t) -> t
              | uu____2175 -> FStar_Extraction_ML_Syntax.MLTY_Top in
            let uu____2176 =
              new_mlpath_of_lident g
                (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____2176 with
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
                ((let uu___358_2219 = g1 in
                  {
                    env_tcenv = (uu___358_2219.env_tcenv);
                    env_bindings = gamma;
                    env_mlident_map = mlident_map;
                    env_remove_typars = (uu___358_2219.env_remove_typars);
                    mlpath_of_lid = (uu___358_2219.mlpath_of_lid);
                    env_fieldname_map = (uu___358_2219.env_fieldname_map);
                    mlpath_of_fieldname = (uu___358_2219.mlpath_of_fieldname);
                    tydefs = (uu___358_2219.tydefs);
                    type_names = (uu___358_2219.type_names);
                    currentModule = (uu___358_2219.currentModule)
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
        let uu____2303 =
          new_mlpath_of_lident g
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        match uu____2303 with
        | (name, g1) ->
            let tydef1 =
              {
                tydef_fv = fv;
                tydef_mlmodule_name = (FStar_Pervasives_Native.fst name);
                tydef_name = (FStar_Pervasives_Native.snd name);
                tydef_def = ts
              } in
            (tydef1, name,
              (let uu___380_2326 = g1 in
               {
                 env_tcenv = (uu___380_2326.env_tcenv);
                 env_bindings = (uu___380_2326.env_bindings);
                 env_mlident_map = (uu___380_2326.env_mlident_map);
                 env_remove_typars = (uu___380_2326.env_remove_typars);
                 mlpath_of_lid = (uu___380_2326.mlpath_of_lid);
                 env_fieldname_map = (uu___380_2326.env_fieldname_map);
                 mlpath_of_fieldname = (uu___380_2326.mlpath_of_fieldname);
                 tydefs = (tydef1 :: (g1.tydefs));
                 type_names = ((fv, name) :: (g1.type_names));
                 currentModule = (uu___380_2326.currentModule)
               }))
let (extend_type_name :
  uenv ->
    FStar_Syntax_Syntax.fv -> (FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g ->
    fun fv ->
      let uu____2350 =
        new_mlpath_of_lident g
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      match uu____2350 with
      | (name, g1) ->
          (name,
            (let uu___387_2362 = g1 in
             {
               env_tcenv = (uu___387_2362.env_tcenv);
               env_bindings = (uu___387_2362.env_bindings);
               env_mlident_map = (uu___387_2362.env_mlident_map);
               env_remove_typars = (uu___387_2362.env_remove_typars);
               mlpath_of_lid = (uu___387_2362.mlpath_of_lid);
               env_fieldname_map = (uu___387_2362.env_fieldname_map);
               mlpath_of_fieldname = (uu___387_2362.mlpath_of_fieldname);
               tydefs = (uu___387_2362.tydefs);
               type_names = ((fv, name) :: (g1.type_names));
               currentModule = (uu___387_2362.currentModule)
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
            let uu____2399 = FStar_Ident.id_of_text nm in
            FStar_Syntax_Util.mk_field_projector_name_from_ident
              ed.FStar_Syntax_Syntax.mname uu____2399 in
          let uu____2400 =
            let uu____2408 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            extend_fv g uu____2408 ts false in
          match uu____2400 with
          | (g1, mlid, exp_b) ->
              let mlp =
                let uu____2432 = mlns_of_lid lid in (uu____2432, mlid) in
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
            let uu____2471 =
              FStar_Ident.ident_of_lid a.FStar_Syntax_Syntax.action_name in
            FStar_Ident.string_of_id uu____2471 in
          let module_name =
            FStar_Ident.ns_of_lid ed.FStar_Syntax_Syntax.mname in
          let lid =
            let uu____2474 =
              let uu____2475 =
                let uu____2478 = FStar_Ident.id_of_text nm in [uu____2478] in
              FStar_List.append module_name uu____2475 in
            FStar_Ident.lid_of_ids uu____2474 in
          let uu____2479 =
            let uu____2487 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            extend_fv g uu____2487 ts false in
          match uu____2479 with
          | (g1, mlid, exp_b) ->
              let mlp =
                let uu____2511 = mlns_of_lid lid in (uu____2511, mlid) in
              (mlp, lid, exp_b, g1)
let (extend_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      (FStar_Extraction_ML_Syntax.mlident * uenv))
  =
  fun g ->
    fun uu____2538 ->
      match uu____2538 with
      | (type_name, fn) ->
          let key =
            let uu____2551 =
              let uu____2552 = FStar_Ident.ids_of_lid type_name in
              FStar_List.append uu____2552 [fn] in
            FStar_Ident.lid_of_ids uu____2551 in
          let uu____2555 =
            let uu____2564 = FStar_Ident.string_of_id fn in
            find_uniq g.env_fieldname_map uu____2564 false in
          (match uu____2555 with
           | (name, fieldname_map) ->
               let ns = mlns_of_lid type_name in
               let mlp = (ns, name) in
               let g1 =
                 let uu___421_2600 = g in
                 let uu____2601 =
                   let uu____2604 = FStar_Ident.string_of_lid key in
                   FStar_Util.psmap_add g.mlpath_of_fieldname uu____2604 mlp in
                 {
                   env_tcenv = (uu___421_2600.env_tcenv);
                   env_bindings = (uu___421_2600.env_bindings);
                   env_mlident_map = (uu___421_2600.env_mlident_map);
                   env_remove_typars = (uu___421_2600.env_remove_typars);
                   mlpath_of_lid = (uu___421_2600.mlpath_of_lid);
                   env_fieldname_map = fieldname_map;
                   mlpath_of_fieldname = uu____2601;
                   tydefs = (uu___421_2600.tydefs);
                   type_names = (uu___421_2600.type_names);
                   currentModule = (uu___421_2600.currentModule)
                 } in
               (name, g1))
let (extend_with_module_name :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g ->
    fun m ->
      let ns = mlns_of_lid m in
      let p =
        let uu____2628 = FStar_Ident.ident_of_lid m in
        FStar_Ident.string_of_id uu____2628 in
      ((ns, p), g)
let (exit_module : uenv -> uenv) =
  fun g ->
    let uu___429_2639 = g in
    let uu____2640 = initial_mlident_map () in
    let uu____2644 = initial_mlident_map () in
    {
      env_tcenv = (uu___429_2639.env_tcenv);
      env_bindings = (uu___429_2639.env_bindings);
      env_mlident_map = uu____2640;
      env_remove_typars = (uu___429_2639.env_remove_typars);
      mlpath_of_lid = (uu___429_2639.mlpath_of_lid);
      env_fieldname_map = uu____2644;
      mlpath_of_fieldname = (uu___429_2639.mlpath_of_fieldname);
      tydefs = (uu___429_2639.tydefs);
      type_names = (uu___429_2639.type_names);
      currentModule = (uu___429_2639.currentModule)
    }
let (new_uenv : FStar_TypeChecker_Env.env -> uenv) =
  fun e ->
    let env =
      let uu____2655 = initial_mlident_map () in
      let uu____2659 = FStar_Util.psmap_empty () in
      let uu____2662 = initial_mlident_map () in
      let uu____2666 = FStar_Util.psmap_empty () in
      {
        env_tcenv = e;
        env_bindings = [];
        env_mlident_map = uu____2655;
        env_remove_typars =
          FStar_Extraction_ML_RemoveUnusedParameters.initial_env;
        mlpath_of_lid = uu____2659;
        env_fieldname_map = uu____2662;
        mlpath_of_fieldname = uu____2666;
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
    let uu____2699 =
      let uu____2707 =
        let uu____2708 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        FStar_Util.Inr uu____2708 in
      extend_lb env uu____2707 FStar_Syntax_Syntax.tun failwith_ty false in
    match uu____2699 with | (g, uu____2711, uu____2712) -> g