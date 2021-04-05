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
type ty_or_exp_b = (ty_binding, exp_binding) FStar_Pervasives.either
type binding =
  | Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b) 
  | Fv of (FStar_Syntax_Syntax.fv * exp_binding) 
  | ErasedFv of FStar_Syntax_Syntax.fv 
let (uu___is_Bv : binding -> Prims.bool) =
  fun projectee -> match projectee with | Bv _0 -> true | uu___ -> false
let (__proj__Bv__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)) =
  fun projectee -> match projectee with | Bv _0 -> _0
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee -> match projectee with | Fv _0 -> true | uu___ -> false
let (__proj__Fv__item___0 :
  binding -> (FStar_Syntax_Syntax.fv * exp_binding)) =
  fun projectee -> match projectee with | Fv _0 -> _0
let (uu___is_ErasedFv : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | ErasedFv _0 -> true | uu___ -> false
let (__proj__ErasedFv__item___0 : binding -> FStar_Syntax_Syntax.fv) =
  fun projectee -> match projectee with | ErasedFv _0 -> _0
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
      let uu___ = u in
      {
        env_tcenv = t;
        env_bindings = (uu___.env_bindings);
        env_mlident_map = (uu___.env_mlident_map);
        env_remove_typars = (uu___.env_remove_typars);
        mlpath_of_lid = (uu___.mlpath_of_lid);
        env_fieldname_map = (uu___.env_fieldname_map);
        mlpath_of_fieldname = (uu___.mlpath_of_fieldname);
        tydefs = (uu___.tydefs);
        type_names = (uu___.type_names);
        tydef_declarations = (uu___.tydef_declarations);
        currentModule = (uu___.currentModule)
      }
let (current_module_of_uenv : uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun u -> u.currentModule
let (set_current_module : uenv -> FStar_Extraction_ML_Syntax.mlpath -> uenv)
  =
  fun u ->
    fun m ->
      let uu___ = u in
      {
        env_tcenv = (uu___.env_tcenv);
        env_bindings = (uu___.env_bindings);
        env_mlident_map = (uu___.env_mlident_map);
        env_remove_typars = (uu___.env_remove_typars);
        mlpath_of_lid = (uu___.mlpath_of_lid);
        env_fieldname_map = (uu___.env_fieldname_map);
        mlpath_of_fieldname = (uu___.mlpath_of_fieldname);
        tydefs = (uu___.tydefs);
        type_names = (uu___.type_names);
        tydef_declarations = (uu___.tydef_declarations);
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
      let uu___ = f u.env_remove_typars in
      match uu___ with
      | (e, x) ->
          ((let uu___1 = u in
            {
              env_tcenv = (uu___1.env_tcenv);
              env_bindings = (uu___1.env_bindings);
              env_mlident_map = (uu___1.env_mlident_map);
              env_remove_typars = e;
              mlpath_of_lid = (uu___1.mlpath_of_lid);
              env_fieldname_map = (uu___1.env_fieldname_map);
              mlpath_of_fieldname = (uu___1.mlpath_of_fieldname);
              tydefs = (uu___1.tydefs);
              type_names = (uu___1.type_names);
              tydef_declarations = (uu___1.tydef_declarations);
              currentModule = (uu___1.currentModule)
            }), x)
let (bindings_of_uenv : uenv -> binding Prims.list) = fun u -> u.env_bindings
let (debug : uenv -> (unit -> unit) -> unit) =
  fun g ->
    fun f ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule in
      let uu___ =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction") in
      if uu___ then f () else ()
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
             fun entries1 ->
               let uu___ =
                 FStar_Util.format2 "%s -> %s" key (string_of_mlpath value) in
               uu___ :: entries1) [] in
    FStar_String.concat "\n" entries
let (lookup_fv_generic :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      (Prims.bool, exp_binding) FStar_Pervasives.either)
  =
  fun g ->
    fun fv ->
      let v =
        FStar_Util.find_map g.env_bindings
          (fun uu___ ->
             match uu___ with
             | Fv (fv', t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
                 FStar_Pervasives_Native.Some (FStar_Pervasives.Inr t)
             | ErasedFv fv' when FStar_Syntax_Syntax.fv_eq fv fv' ->
                 FStar_Pervasives_Native.Some (FStar_Pervasives.Inl true)
             | uu___1 -> FStar_Pervasives_Native.None) in
      match v with
      | FStar_Pervasives_Native.Some r -> r
      | FStar_Pervasives_Native.None -> FStar_Pervasives.Inl false
let (try_lookup_fv :
  FStar_Range.range ->
    uenv ->
      FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun r ->
    fun g ->
      fun fv ->
        let uu___ = lookup_fv_generic g fv in
        match uu___ with
        | FStar_Pervasives.Inr r1 -> FStar_Pervasives_Native.Some r1
        | FStar_Pervasives.Inl (true) ->
            ((let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Syntax_Print.fv_to_string fv in
                  let uu___5 =
                    FStar_Util.string_of_int
                      FStar_Errors.call_to_erased_errno in
                  FStar_Util.format2
                    "Will not extract reference to variable `%s` since it is noextract; either remove its qualifier or add it to this definition. This error can be ignored with `--warn_error -%s`."
                    uu___4 uu___5 in
                (FStar_Errors.Error_CallToErased, uu___3) in
              FStar_Errors.log_issue r uu___2);
             FStar_Pervasives_Native.None)
        | FStar_Pervasives.Inl (false) -> FStar_Pervasives_Native.None
let (lookup_fv :
  FStar_Range.range -> uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun r ->
    fun g ->
      fun fv ->
        let uu___ = lookup_fv_generic g fv in
        match uu___ with
        | FStar_Pervasives.Inr t -> t
        | FStar_Pervasives.Inl b ->
            let uu___1 =
              let uu___2 =
                FStar_Range.string_of_range
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p in
              let uu___3 =
                FStar_Syntax_Print.lid_to_string
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let uu___4 = FStar_Util.string_of_bool b in
              FStar_Util.format3
                "Internal error: (%s) free variable %s not found during extraction (erased=%s)\n"
                uu___2 uu___3 uu___4 in
            failwith uu___1
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g ->
    fun bv ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___ ->
             match uu___ with
             | Bv (bv', r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu___1 -> FStar_Pervasives_Native.None) in
      match x with
      | FStar_Pervasives_Native.None ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_Ident.range_of_id bv.FStar_Syntax_Syntax.ppname in
              FStar_Range.string_of_range uu___2 in
            let uu___2 = FStar_Syntax_Print.bv_to_string bv in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu___1
              uu___2 in
          failwith uu___
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
          let uu___ = lookup_bv g x in (uu___, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar x ->
          let uu___ =
            let uu___1 = lookup_fv t.FStar_Syntax_Syntax.pos g x in
            FStar_Pervasives.Inr uu___1 in
          (uu___, (x.FStar_Syntax_Syntax.fv_qual))
      | uu___ -> failwith "Impossible: lookup_term for a non-name"
let (lookup_ty : uenv -> FStar_Syntax_Syntax.bv -> ty_binding) =
  fun g ->
    fun x ->
      let uu___ = lookup_bv g x in
      match uu___ with
      | FStar_Pervasives.Inl ty -> ty
      | uu___1 -> failwith "Expected a type name"
let (lookup_tydef :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env ->
    fun uu___ ->
      match uu___ with
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
      let uu___ =
        let uu___1 = FStar_Ident.string_of_lid l in
        FStar_Util.psmap_try_find u.tydef_declarations uu___1 in
      match uu___ with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some b -> b
let (mlpath_of_lident :
  uenv -> FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlpath) =
  fun g ->
    fun x ->
      let uu___ =
        let uu___1 = FStar_Ident.string_of_lid x in
        FStar_Util.psmap_try_find g.mlpath_of_lid uu___1 in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          (debug g
             (fun uu___2 ->
                (let uu___4 = FStar_Ident.string_of_lid x in
                 FStar_Util.print1 "Identifier not found: %s" uu___4);
                (let uu___4 = print_mlpath_map g in
                 FStar_Util.print1 "Env is \n%s\n" uu___4));
           (let uu___2 =
              let uu___3 = FStar_Ident.string_of_lid x in
              Prims.op_Hat "Identifier not found: " uu___3 in
            failwith uu___2))
      | FStar_Pervasives_Native.Some mlp -> mlp
let (is_type_name : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g ->
    fun fv ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some
           (fun uu___ ->
              match uu___ with
              | (x, uu___1) -> FStar_Syntax_Syntax.fv_eq fv x))
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
    fun uu___ ->
      match uu___ with
      | (type_name, fn) ->
          let key =
            let uu___1 =
              let uu___2 = FStar_Ident.ids_of_lid type_name in
              FStar_List.append uu___2 [fn] in
            FStar_Ident.lid_of_ids uu___1 in
          let uu___1 =
            let uu___2 = FStar_Ident.string_of_lid key in
            FStar_Util.psmap_try_find g.mlpath_of_fieldname uu___2 in
          (match uu___1 with
           | FStar_Pervasives_Native.None ->
               let uu___2 =
                 let uu___3 = FStar_Ident.string_of_lid key in
                 Prims.op_Hat "Field name not found: " uu___3 in
               failwith uu___2
           | FStar_Pervasives_Native.Some mlp -> mlp)
let (initial_mlident_map : unit -> Prims.string FStar_Util.psmap) =
  let map = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  fun uu___ ->
    let uu___1 = FStar_ST.op_Bang map in
    match uu___1 with
    | FStar_Pervasives_Native.Some m -> m
    | FStar_Pervasives_Native.None ->
        let m =
          let uu___2 =
            let uu___3 = FStar_Options.codegen () in
            match uu___3 with
            | FStar_Pervasives_Native.Some (FStar_Options.FSharp) ->
                FStar_Extraction_ML_Syntax.fsharpkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.OCaml) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Plugin) ->
                FStar_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStar_Options.Kremlin) ->
                FStar_Extraction_ML_Syntax.kremlin_keywords ()
            | FStar_Pervasives_Native.None -> [] in
          let uu___3 = FStar_Util.psmap_empty () in
          FStar_List.fold_right
            (fun x -> fun m1 -> FStar_Util.psmap_add m1 x "") uu___2 uu___3 in
        (FStar_ST.op_Colon_Equals map (FStar_Pervasives_Native.Some m); m)
let (rename_conventional : Prims.string -> Prims.bool -> Prims.string) =
  fun s ->
    fun is_local_type_variable ->
      let cs = FStar_String.list_of_string s in
      let sanitize_typ uu___ =
        let valid_rest c = FStar_Util.is_letter_or_digit c in
        let aux cs1 =
          FStar_List.map
            (fun x -> let uu___1 = valid_rest x in if uu___1 then x else 117)
            cs1 in
        let uu___1 = let uu___2 = FStar_List.hd cs in uu___2 = 39 in
        if uu___1
        then
          let uu___2 = FStar_List.hd cs in
          let uu___3 = let uu___4 = FStar_List.tail cs in aux uu___4 in
          uu___2 :: uu___3
        else (let uu___3 = aux cs in 39 :: uu___3) in
      let sanitize_term uu___ =
        let valid c =
          ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39) in
        let cs' =
          FStar_List.fold_right
            (fun c ->
               fun cs1 ->
                 let uu___1 =
                   let uu___2 = valid c in if uu___2 then [c] else [95; 95] in
                 FStar_List.append uu___1 cs1) cs [] in
        match cs' with
        | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
        | uu___1 -> cs in
      let uu___ =
        if is_local_type_variable then sanitize_typ () else sanitize_term () in
      FStar_String.string_of_list uu___
let (root_name_of_bv :
  FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlident) =
  fun x ->
    let uu___ =
      (let uu___1 = FStar_Ident.string_of_id x.FStar_Syntax_Syntax.ppname in
       FStar_Util.starts_with uu___1 FStar_Ident.reserved_prefix) ||
        (FStar_Syntax_Syntax.is_null_bv x) in
    if uu___
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
              (let uu___1 = FStar_Util.string_of_int i in
               Prims.op_Hat root_name1 uu___1) in
          let uu___ = FStar_Util.psmap_try_find ml_ident_map target_mlident in
          match uu___ with
          | FStar_Pervasives_Native.Some x ->
              aux (i + Prims.int_one) root_name1
          | FStar_Pervasives_Native.None ->
              let map = FStar_Util.psmap_add ml_ident_map target_mlident "" in
              (target_mlident, map) in
        let mlident = rename_conventional root_name is_local_type_variable in
        if is_local_type_variable
        then
          let uu___ =
            let uu___1 = FStar_Util.substring_from mlident Prims.int_one in
            aux Prims.int_zero uu___1 in
          match uu___ with | (nm, map) -> ((Prims.op_Hat "'" nm), map)
        else aux Prims.int_zero mlident
let (mlns_of_lid : FStar_Ident.lident -> Prims.string Prims.list) =
  fun x ->
    let uu___ = FStar_Ident.ns_of_lid x in
    FStar_List.map FStar_Ident.string_of_id uu___
let (new_mlpath_of_lident :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g ->
    fun x ->
      let uu___ =
        let uu___1 = FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid in
        if uu___1
        then
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Ident.ident_of_lid x in
              FStar_Ident.string_of_id uu___4 in
            ([], uu___3) in
          (uu___2, g)
        else
          (let uu___3 =
             let uu___4 =
               let uu___5 = FStar_Ident.ident_of_lid x in
               FStar_Ident.string_of_id uu___5 in
             find_uniq g.env_mlident_map uu___4 false in
           match uu___3 with
           | (name, map) ->
               let g1 =
                 let uu___4 = g in
                 {
                   env_tcenv = (uu___4.env_tcenv);
                   env_bindings = (uu___4.env_bindings);
                   env_mlident_map = map;
                   env_remove_typars = (uu___4.env_remove_typars);
                   mlpath_of_lid = (uu___4.mlpath_of_lid);
                   env_fieldname_map = (uu___4.env_fieldname_map);
                   mlpath_of_fieldname = (uu___4.mlpath_of_fieldname);
                   tydefs = (uu___4.tydefs);
                   type_names = (uu___4.type_names);
                   tydef_declarations = (uu___4.tydef_declarations);
                   currentModule = (uu___4.currentModule)
                 } in
               let uu___4 = let uu___5 = mlns_of_lid x in (uu___5, name) in
               (uu___4, g1)) in
      match uu___ with
      | (mlp, g1) ->
          let g2 =
            let uu___1 = g1 in
            let uu___2 =
              let uu___3 = FStar_Ident.string_of_lid x in
              FStar_Util.psmap_add g1.mlpath_of_lid uu___3 mlp in
            {
              env_tcenv = (uu___1.env_tcenv);
              env_bindings = (uu___1.env_bindings);
              env_mlident_map = (uu___1.env_mlident_map);
              env_remove_typars = (uu___1.env_remove_typars);
              mlpath_of_lid = uu___2;
              env_fieldname_map = (uu___1.env_fieldname_map);
              mlpath_of_fieldname = (uu___1.mlpath_of_fieldname);
              tydefs = (uu___1.tydefs);
              type_names = (uu___1.type_names);
              tydef_declarations = (uu___1.tydef_declarations);
              currentModule = (uu___1.currentModule)
            } in
          (mlp, g2)
let (extend_ty : uenv -> FStar_Syntax_Syntax.bv -> Prims.bool -> uenv) =
  fun g ->
    fun a ->
      fun map_to_top ->
        let is_local_type_variable = Prims.op_Negation map_to_top in
        let uu___ =
          let uu___1 = root_name_of_bv a in
          find_uniq g.env_mlident_map uu___1 is_local_type_variable in
        match uu___ with
        | (ml_a, mlident_map) ->
            let mapped_to =
              if map_to_top
              then FStar_Extraction_ML_Syntax.MLTY_Top
              else FStar_Extraction_ML_Syntax.MLTY_Var ml_a in
            let gamma =
              (Bv
                 (a,
                   (FStar_Pervasives.Inl
                      { ty_b_name = ml_a; ty_b_ty = mapped_to })))
              :: (g.env_bindings) in
            let tcenv = FStar_TypeChecker_Env.push_bv g.env_tcenv a in
            let uu___1 = g in
            {
              env_tcenv = tcenv;
              env_bindings = gamma;
              env_mlident_map = mlident_map;
              env_remove_typars = (uu___1.env_remove_typars);
              mlpath_of_lid = (uu___1.mlpath_of_lid);
              env_fieldname_map = (uu___1.env_fieldname_map);
              mlpath_of_fieldname = (uu___1.mlpath_of_fieldname);
              tydefs = (uu___1.tydefs);
              type_names = (uu___1.type_names);
              tydef_declarations = (uu___1.tydef_declarations);
              currentModule = (uu___1.currentModule)
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
              | uu___ -> FStar_Extraction_ML_Syntax.MLTY_Top in
            let uu___ =
              let uu___1 = root_name_of_bv x in
              find_uniq g.env_mlident_map uu___1 false in
            match uu___ with
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
                let gamma = (Bv (x, (FStar_Pervasives.Inr exp_binding1))) ::
                  (g.env_bindings) in
                let tcenv =
                  let uu___1 = FStar_Syntax_Syntax.binders_of_list [x] in
                  FStar_TypeChecker_Env.push_binders g.env_tcenv uu___1 in
                ((let uu___1 = g in
                  {
                    env_tcenv = tcenv;
                    env_bindings = gamma;
                    env_mlident_map = mlident_map;
                    env_remove_typars = (uu___1.env_remove_typars);
                    mlpath_of_lid = (uu___1.mlpath_of_lid);
                    env_fieldname_map = (uu___1.env_fieldname_map);
                    mlpath_of_fieldname = (uu___1.mlpath_of_fieldname);
                    tydefs = (uu___1.tydefs);
                    type_names = (uu___1.type_names);
                    tydef_declarations = (uu___1.tydef_declarations);
                    currentModule = (uu___1.currentModule)
                  }), mlident, exp_binding1)
let (burn_name : uenv -> FStar_Extraction_ML_Syntax.mlident -> uenv) =
  fun g ->
    fun i ->
      let uu___ = g in
      let uu___1 = FStar_Util.psmap_add g.env_mlident_map i "" in
      {
        env_tcenv = (uu___.env_tcenv);
        env_bindings = (uu___.env_bindings);
        env_mlident_map = uu___1;
        env_remove_typars = (uu___.env_remove_typars);
        mlpath_of_lid = (uu___.mlpath_of_lid);
        env_fieldname_map = (uu___.env_fieldname_map);
        mlpath_of_fieldname = (uu___.mlpath_of_fieldname);
        tydefs = (uu___.tydefs);
        type_names = (uu___.type_names);
        tydef_declarations = (uu___.tydef_declarations);
        currentModule = (uu___.currentModule)
      }
let (new_mlident : uenv -> (uenv * FStar_Extraction_ML_Syntax.mlident)) =
  fun g ->
    let ml_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
    let x =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.tun in
    let uu___ =
      extend_bv g x ([], FStar_Extraction_ML_Syntax.MLTY_Top) false false in
    match uu___ with | (g1, id, uu___1) -> (g1, id)
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
                let uu___ = mltyFvars t1 in
                let uu___1 = mltyFvars t2 in FStar_List.append uu___ uu___1
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
            let uu___ = mltyFvars (FStar_Pervasives_Native.snd tys) in
            subsetMlidents uu___ (FStar_Pervasives_Native.fst tys) in
          let uu___ = tySchemeIsClosed t_x in
          if uu___
          then
            let ml_ty =
              match t_x with
              | ([], t) -> t
              | uu___1 -> FStar_Extraction_ML_Syntax.MLTY_Top in
            let uu___1 =
              new_mlpath_of_lident g
                (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu___1 with
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
                ((let uu___2 = g1 in
                  {
                    env_tcenv = (uu___2.env_tcenv);
                    env_bindings = gamma;
                    env_mlident_map = mlident_map;
                    env_remove_typars = (uu___2.env_remove_typars);
                    mlpath_of_lid = (uu___2.mlpath_of_lid);
                    env_fieldname_map = (uu___2.env_fieldname_map);
                    mlpath_of_fieldname = (uu___2.mlpath_of_fieldname);
                    tydefs = (uu___2.tydefs);
                    type_names = (uu___2.type_names);
                    tydef_declarations = (uu___2.tydef_declarations);
                    currentModule = (uu___2.currentModule)
                  }), mlsymbol, exp_binding1)
          else failwith "freevars found"
let (extend_erased_fv : uenv -> FStar_Syntax_Syntax.fv -> uenv) =
  fun g ->
    fun f ->
      let uu___ = g in
      {
        env_tcenv = (uu___.env_tcenv);
        env_bindings = ((ErasedFv f) :: (g.env_bindings));
        env_mlident_map = (uu___.env_mlident_map);
        env_remove_typars = (uu___.env_remove_typars);
        mlpath_of_lid = (uu___.mlpath_of_lid);
        env_fieldname_map = (uu___.env_fieldname_map);
        mlpath_of_fieldname = (uu___.mlpath_of_fieldname);
        tydefs = (uu___.tydefs);
        type_names = (uu___.type_names);
        tydef_declarations = (uu___.tydef_declarations);
        currentModule = (uu___.currentModule)
      }
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
            | FStar_Pervasives.Inl x -> extend_bv g x t_x add_unit false
            | FStar_Pervasives.Inr f -> extend_fv g f t_x add_unit
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
          let uu___ =
            new_mlpath_of_lident g
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu___ with
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
                (let uu___1 = g1 in
                 {
                   env_tcenv = (uu___1.env_tcenv);
                   env_bindings = (uu___1.env_bindings);
                   env_mlident_map = (uu___1.env_mlident_map);
                   env_remove_typars = (uu___1.env_remove_typars);
                   mlpath_of_lid = (uu___1.mlpath_of_lid);
                   env_fieldname_map = (uu___1.env_fieldname_map);
                   mlpath_of_fieldname = (uu___1.mlpath_of_fieldname);
                   tydefs = (tydef1 :: (g1.tydefs));
                   type_names = ((fv, name) :: (g1.type_names));
                   tydef_declarations = (uu___1.tydef_declarations);
                   currentModule = (uu___1.currentModule)
                 }))
let (extend_with_tydef_declaration : uenv -> FStar_Ident.lident -> uenv) =
  fun u ->
    fun l ->
      let uu___ = u in
      let uu___1 =
        let uu___2 = FStar_Ident.string_of_lid l in
        FStar_Util.psmap_add u.tydef_declarations uu___2 true in
      {
        env_tcenv = (uu___.env_tcenv);
        env_bindings = (uu___.env_bindings);
        env_mlident_map = (uu___.env_mlident_map);
        env_remove_typars = (uu___.env_remove_typars);
        mlpath_of_lid = (uu___.mlpath_of_lid);
        env_fieldname_map = (uu___.env_fieldname_map);
        mlpath_of_fieldname = (uu___.mlpath_of_fieldname);
        tydefs = (uu___.tydefs);
        type_names = (uu___.type_names);
        tydef_declarations = uu___1;
        currentModule = (uu___.currentModule)
      }
let (extend_type_name :
  uenv ->
    FStar_Syntax_Syntax.fv -> (FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g ->
    fun fv ->
      let uu___ =
        new_mlpath_of_lident g
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      match uu___ with
      | (name, g1) ->
          (name,
            (let uu___1 = g1 in
             {
               env_tcenv = (uu___1.env_tcenv);
               env_bindings = (uu___1.env_bindings);
               env_mlident_map = (uu___1.env_mlident_map);
               env_remove_typars = (uu___1.env_remove_typars);
               mlpath_of_lid = (uu___1.mlpath_of_lid);
               env_fieldname_map = (uu___1.env_fieldname_map);
               mlpath_of_fieldname = (uu___1.mlpath_of_fieldname);
               tydefs = (uu___1.tydefs);
               type_names = ((fv, name) :: (g1.type_names));
               tydef_declarations = (uu___1.tydef_declarations);
               currentModule = (uu___1.currentModule)
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
            let uu___ = FStar_Ident.id_of_text nm in
            FStar_Syntax_Util.mk_field_projector_name_from_ident
              ed.FStar_Syntax_Syntax.mname uu___ in
          let uu___ =
            let uu___1 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            extend_fv g uu___1 ts false in
          match uu___ with
          | (g1, mlid, exp_b) ->
              let mlp = let uu___1 = mlns_of_lid lid in (uu___1, mlid) in
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
            let uu___ =
              FStar_Ident.ident_of_lid a.FStar_Syntax_Syntax.action_name in
            FStar_Ident.string_of_id uu___ in
          let module_name =
            FStar_Ident.ns_of_lid ed.FStar_Syntax_Syntax.mname in
          let lid =
            let uu___ =
              let uu___1 = let uu___2 = FStar_Ident.id_of_text nm in [uu___2] in
              FStar_List.append module_name uu___1 in
            FStar_Ident.lid_of_ids uu___ in
          let uu___ =
            let uu___1 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            extend_fv g uu___1 ts false in
          match uu___ with
          | (g1, mlid, exp_b) ->
              let mlp = let uu___1 = mlns_of_lid lid in (uu___1, mlid) in
              (mlp, lid, exp_b, g1)
let (extend_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      (FStar_Extraction_ML_Syntax.mlident * uenv))
  =
  fun g ->
    fun uu___ ->
      match uu___ with
      | (type_name, fn) ->
          let key =
            let uu___1 =
              let uu___2 = FStar_Ident.ids_of_lid type_name in
              FStar_List.append uu___2 [fn] in
            FStar_Ident.lid_of_ids uu___1 in
          let uu___1 =
            let uu___2 = FStar_Ident.string_of_id fn in
            find_uniq g.env_fieldname_map uu___2 false in
          (match uu___1 with
           | (name, fieldname_map) ->
               let ns = mlns_of_lid type_name in
               let mlp = (ns, name) in
               let g1 =
                 let uu___2 = g in
                 let uu___3 =
                   let uu___4 = FStar_Ident.string_of_lid key in
                   FStar_Util.psmap_add g.mlpath_of_fieldname uu___4 mlp in
                 {
                   env_tcenv = (uu___2.env_tcenv);
                   env_bindings = (uu___2.env_bindings);
                   env_mlident_map = (uu___2.env_mlident_map);
                   env_remove_typars = (uu___2.env_remove_typars);
                   mlpath_of_lid = (uu___2.mlpath_of_lid);
                   env_fieldname_map = fieldname_map;
                   mlpath_of_fieldname = uu___3;
                   tydefs = (uu___2.tydefs);
                   type_names = (uu___2.type_names);
                   tydef_declarations = (uu___2.tydef_declarations);
                   currentModule = (uu___2.currentModule)
                 } in
               (name, g1))
let (extend_with_module_name :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g ->
    fun m ->
      let ns = mlns_of_lid m in
      let p =
        let uu___ = FStar_Ident.ident_of_lid m in
        FStar_Ident.string_of_id uu___ in
      ((ns, p), g)
let (exit_module : uenv -> uenv) =
  fun g ->
    let uu___ = g in
    let uu___1 = initial_mlident_map () in
    let uu___2 = initial_mlident_map () in
    {
      env_tcenv = (uu___.env_tcenv);
      env_bindings = (uu___.env_bindings);
      env_mlident_map = uu___1;
      env_remove_typars = (uu___.env_remove_typars);
      mlpath_of_lid = (uu___.mlpath_of_lid);
      env_fieldname_map = uu___2;
      mlpath_of_fieldname = (uu___.mlpath_of_fieldname);
      tydefs = (uu___.tydefs);
      type_names = (uu___.type_names);
      tydef_declarations = (uu___.tydef_declarations);
      currentModule = (uu___.currentModule)
    }
let (new_uenv : FStar_TypeChecker_Env.env -> uenv) =
  fun e ->
    let env =
      let uu___ = initial_mlident_map () in
      let uu___1 = FStar_Util.psmap_empty () in
      let uu___2 = initial_mlident_map () in
      let uu___3 = FStar_Util.psmap_empty () in
      let uu___4 = FStar_Util.psmap_empty () in
      {
        env_tcenv = e;
        env_bindings = [];
        env_mlident_map = uu___;
        env_remove_typars =
          FStar_Extraction_ML_RemoveUnusedParameters.initial_env;
        mlpath_of_lid = uu___1;
        env_fieldname_map = uu___2;
        mlpath_of_fieldname = uu___3;
        tydefs = [];
        type_names = [];
        tydef_declarations = uu___4;
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
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        FStar_Pervasives.Inr uu___2 in
      extend_lb env uu___1 FStar_Syntax_Syntax.tun failwith_ty false in
    match uu___ with | (g, uu___1, uu___2) -> g