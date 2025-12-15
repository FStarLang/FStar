open Prims
type ty_binding =
  {
  ty_b_name: FStarC_Extraction_ML_Syntax.mlident ;
  ty_b_ty: FStarC_Extraction_ML_Syntax.mlty }
let __proj__Mkty_binding__item__ty_b_name (projectee : ty_binding) :
  FStarC_Extraction_ML_Syntax.mlident=
  match projectee with | { ty_b_name; ty_b_ty;_} -> ty_b_name
let __proj__Mkty_binding__item__ty_b_ty (projectee : ty_binding) :
  FStarC_Extraction_ML_Syntax.mlty=
  match projectee with | { ty_b_name; ty_b_ty;_} -> ty_b_ty
type exp_binding =
  {
  exp_b_name: FStarC_Extraction_ML_Syntax.mlident ;
  exp_b_expr: FStarC_Extraction_ML_Syntax.mlexpr ;
  exp_b_tscheme: FStarC_Extraction_ML_Syntax.mltyscheme ;
  exp_b_eff: FStarC_Extraction_ML_Syntax.e_tag }
let __proj__Mkexp_binding__item__exp_b_name (projectee : exp_binding) :
  FStarC_Extraction_ML_Syntax.mlident=
  match projectee with
  | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_eff;_} -> exp_b_name
let __proj__Mkexp_binding__item__exp_b_expr (projectee : exp_binding) :
  FStarC_Extraction_ML_Syntax.mlexpr=
  match projectee with
  | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_eff;_} -> exp_b_expr
let __proj__Mkexp_binding__item__exp_b_tscheme (projectee : exp_binding) :
  FStarC_Extraction_ML_Syntax.mltyscheme=
  match projectee with
  | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_eff;_} -> exp_b_tscheme
let __proj__Mkexp_binding__item__exp_b_eff (projectee : exp_binding) :
  FStarC_Extraction_ML_Syntax.e_tag=
  match projectee with
  | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_eff;_} -> exp_b_eff
type ty_or_exp_b = (ty_binding, exp_binding) FStar_Pervasives.either
type mlbinding =
  | Bv of (FStarC_Syntax_Syntax.bv * ty_or_exp_b) 
  | Fv of (FStarC_Syntax_Syntax.fv * exp_binding) 
  | ErasedFv of FStarC_Syntax_Syntax.fv 
let uu___is_Bv (projectee : mlbinding) : Prims.bool=
  match projectee with | Bv _0 -> true | uu___ -> false
let __proj__Bv__item___0 (projectee : mlbinding) :
  (FStarC_Syntax_Syntax.bv * ty_or_exp_b)= match projectee with | Bv _0 -> _0
let uu___is_Fv (projectee : mlbinding) : Prims.bool=
  match projectee with | Fv _0 -> true | uu___ -> false
let __proj__Fv__item___0 (projectee : mlbinding) :
  (FStarC_Syntax_Syntax.fv * exp_binding)= match projectee with | Fv _0 -> _0
let uu___is_ErasedFv (projectee : mlbinding) : Prims.bool=
  match projectee with | ErasedFv _0 -> true | uu___ -> false
let __proj__ErasedFv__item___0 (projectee : mlbinding) :
  FStarC_Syntax_Syntax.fv= match projectee with | ErasedFv _0 -> _0
let plug (uu___ : unit) : Prims.bool=
  (let uu___1 = FStarC_Options.codegen () in
   uu___1 = (FStar_Pervasives_Native.Some FStarC_Options.Plugin)) ||
    (let uu___1 = FStarC_Options.codegen () in
     uu___1 = (FStar_Pervasives_Native.Some FStarC_Options.PluginNoLib))
let plug_no_lib (uu___ : unit) : Prims.bool=
  let uu___1 = FStarC_Options.codegen () in
  uu___1 = (FStar_Pervasives_Native.Some FStarC_Options.PluginNoLib)
let showable_mlbinding : mlbinding FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Bv (x, uu___1) ->
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv x
         | Fv (x, uu___1) ->
             FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_fv x
         | ErasedFv x ->
             let uu___1 =
               FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_fv x in
             FStarC_Format.fmt1 "Erased %s" uu___1)
  }
type tydef =
  {
  tydef_fv: FStarC_Syntax_Syntax.fv ;
  tydef_mlmodule_name: FStarC_Extraction_ML_Syntax.mlsymbol Prims.list ;
  tydef_name: FStarC_Extraction_ML_Syntax.mlsymbol ;
  tydef_meta: FStarC_Extraction_ML_Syntax.metadata ;
  tydef_def: FStarC_Extraction_ML_Syntax.mltyscheme }
let __proj__Mktydef__item__tydef_fv (projectee : tydef) :
  FStarC_Syntax_Syntax.fv=
  match projectee with
  | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_meta; tydef_def;_} ->
      tydef_fv
let __proj__Mktydef__item__tydef_mlmodule_name (projectee : tydef) :
  FStarC_Extraction_ML_Syntax.mlsymbol Prims.list=
  match projectee with
  | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_meta; tydef_def;_} ->
      tydef_mlmodule_name
let __proj__Mktydef__item__tydef_name (projectee : tydef) :
  FStarC_Extraction_ML_Syntax.mlsymbol=
  match projectee with
  | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_meta; tydef_def;_} ->
      tydef_name
let __proj__Mktydef__item__tydef_meta (projectee : tydef) :
  FStarC_Extraction_ML_Syntax.metadata=
  match projectee with
  | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_meta; tydef_def;_} ->
      tydef_meta
let __proj__Mktydef__item__tydef_def (projectee : tydef) :
  FStarC_Extraction_ML_Syntax.mltyscheme=
  match projectee with
  | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_meta; tydef_def;_} ->
      tydef_def
let tydef_fv (td : tydef) : FStarC_Syntax_Syntax.fv= td.tydef_fv
let tydef_meta (td : tydef) : FStarC_Extraction_ML_Syntax.metadata=
  td.tydef_meta
let tydef_def (td : tydef) : FStarC_Extraction_ML_Syntax.mltyscheme=
  td.tydef_def
let tydef_mlpath (td : tydef) : FStarC_Extraction_ML_Syntax.mlpath=
  ((td.tydef_mlmodule_name), (td.tydef_name))
type uenv =
  {
  env_tcenv: FStarC_TypeChecker_Env.env ;
  env_bindings: mlbinding Prims.list ;
  env_mlident_map: FStarC_Extraction_ML_Syntax.mlident FStarC_PSMap.t ;
  env_remove_typars: FStarC_Extraction_ML_RemoveUnusedParameters.env_t ;
  mlpath_of_lid: FStarC_Extraction_ML_Syntax.mlpath FStarC_PSMap.t ;
  env_fieldname_map: FStarC_Extraction_ML_Syntax.mlident FStarC_PSMap.t ;
  mlpath_of_fieldname: FStarC_Extraction_ML_Syntax.mlpath FStarC_PSMap.t ;
  tydefs: tydef Prims.list ;
  type_names:
    (FStarC_Syntax_Syntax.fv * FStarC_Extraction_ML_Syntax.mlpath) Prims.list ;
  tydef_declarations: Prims.bool FStarC_PSMap.t ;
  currentModule: FStarC_Extraction_ML_Syntax.mlpath }
let __proj__Mkuenv__item__env_tcenv (projectee : uenv) :
  FStarC_TypeChecker_Env.env=
  match projectee with
  | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
      mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
      type_names; tydef_declarations; currentModule;_} -> env_tcenv
let __proj__Mkuenv__item__env_bindings (projectee : uenv) :
  mlbinding Prims.list=
  match projectee with
  | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
      mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
      type_names; tydef_declarations; currentModule;_} -> env_bindings
let __proj__Mkuenv__item__env_mlident_map (projectee : uenv) :
  FStarC_Extraction_ML_Syntax.mlident FStarC_PSMap.t=
  match projectee with
  | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
      mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
      type_names; tydef_declarations; currentModule;_} -> env_mlident_map
let __proj__Mkuenv__item__env_remove_typars (projectee : uenv) :
  FStarC_Extraction_ML_RemoveUnusedParameters.env_t=
  match projectee with
  | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
      mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
      type_names; tydef_declarations; currentModule;_} -> env_remove_typars
let __proj__Mkuenv__item__mlpath_of_lid (projectee : uenv) :
  FStarC_Extraction_ML_Syntax.mlpath FStarC_PSMap.t=
  match projectee with
  | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
      mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
      type_names; tydef_declarations; currentModule;_} -> mlpath_of_lid
let __proj__Mkuenv__item__env_fieldname_map (projectee : uenv) :
  FStarC_Extraction_ML_Syntax.mlident FStarC_PSMap.t=
  match projectee with
  | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
      mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
      type_names; tydef_declarations; currentModule;_} -> env_fieldname_map
let __proj__Mkuenv__item__mlpath_of_fieldname (projectee : uenv) :
  FStarC_Extraction_ML_Syntax.mlpath FStarC_PSMap.t=
  match projectee with
  | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
      mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
      type_names; tydef_declarations; currentModule;_} -> mlpath_of_fieldname
let __proj__Mkuenv__item__tydefs (projectee : uenv) : tydef Prims.list=
  match projectee with
  | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
      mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
      type_names; tydef_declarations; currentModule;_} -> tydefs
let __proj__Mkuenv__item__type_names (projectee : uenv) :
  (FStarC_Syntax_Syntax.fv * FStarC_Extraction_ML_Syntax.mlpath) Prims.list=
  match projectee with
  | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
      mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
      type_names; tydef_declarations; currentModule;_} -> type_names
let __proj__Mkuenv__item__tydef_declarations (projectee : uenv) :
  Prims.bool FStarC_PSMap.t=
  match projectee with
  | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
      mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
      type_names; tydef_declarations; currentModule;_} -> tydef_declarations
let __proj__Mkuenv__item__currentModule (projectee : uenv) :
  FStarC_Extraction_ML_Syntax.mlpath=
  match projectee with
  | { env_tcenv; env_bindings; env_mlident_map; env_remove_typars;
      mlpath_of_lid; env_fieldname_map; mlpath_of_fieldname; tydefs;
      type_names; tydef_declarations; currentModule;_} -> currentModule
let with_restored_tc_scope (env : uenv) (f : uenv -> ('a * uenv)) :
  ('a * uenv)=
  let uu___ =
    FStarC_TypeChecker_Env.with_restored_scope env.env_tcenv
      (fun tcenv ->
         let uenv1 =
           {
             env_tcenv = tcenv;
             env_bindings = (env.env_bindings);
             env_mlident_map = (env.env_mlident_map);
             env_remove_typars = (env.env_remove_typars);
             mlpath_of_lid = (env.mlpath_of_lid);
             env_fieldname_map = (env.env_fieldname_map);
             mlpath_of_fieldname = (env.mlpath_of_fieldname);
             tydefs = (env.tydefs);
             type_names = (env.type_names);
             tydef_declarations = (env.tydef_declarations);
             currentModule = (env.currentModule)
           } in
         let uu___1 = f uenv1 in
         match uu___1 with
         | (res, uenv') -> ((res, uenv'), (uenv'.env_tcenv))) in
  match uu___ with
  | ((res, uenv'), tcenv') ->
      (res,
        {
          env_tcenv = tcenv';
          env_bindings = (uenv'.env_bindings);
          env_mlident_map = (uenv'.env_mlident_map);
          env_remove_typars = (uenv'.env_remove_typars);
          mlpath_of_lid = (uenv'.mlpath_of_lid);
          env_fieldname_map = (uenv'.env_fieldname_map);
          mlpath_of_fieldname = (uenv'.mlpath_of_fieldname);
          tydefs = (uenv'.tydefs);
          type_names = (uenv'.type_names);
          tydef_declarations = (uenv'.tydef_declarations);
          currentModule = (uenv'.currentModule)
        })
let showable_uenv : uenv FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun e ->
         FStarC_Class_Show.show
           (FStarC_Class_Show.show_list showable_mlbinding) e.env_bindings)
  }
let tcenv_of_uenv (u : uenv) : FStarC_TypeChecker_Env.env= u.env_tcenv
let set_tcenv (u : uenv) (t : FStarC_TypeChecker_Env.env) : uenv=
  {
    env_tcenv = t;
    env_bindings = (u.env_bindings);
    env_mlident_map = (u.env_mlident_map);
    env_remove_typars = (u.env_remove_typars);
    mlpath_of_lid = (u.mlpath_of_lid);
    env_fieldname_map = (u.env_fieldname_map);
    mlpath_of_fieldname = (u.mlpath_of_fieldname);
    tydefs = (u.tydefs);
    type_names = (u.type_names);
    tydef_declarations = (u.tydef_declarations);
    currentModule = (u.currentModule)
  }
let current_module_of_uenv (u : uenv) : FStarC_Extraction_ML_Syntax.mlpath=
  u.currentModule
let set_current_module (u : uenv) (m : FStarC_Extraction_ML_Syntax.mlpath) :
  uenv=
  {
    env_tcenv = (u.env_tcenv);
    env_bindings = (u.env_bindings);
    env_mlident_map = (u.env_mlident_map);
    env_remove_typars = (u.env_remove_typars);
    mlpath_of_lid = (u.mlpath_of_lid);
    env_fieldname_map = (u.env_fieldname_map);
    mlpath_of_fieldname = (u.mlpath_of_fieldname);
    tydefs = (u.tydefs);
    type_names = (u.type_names);
    tydef_declarations = (u.tydef_declarations);
    currentModule = m
  }
let with_typars_env (u : uenv)
  (f :
    FStarC_Extraction_ML_RemoveUnusedParameters.env_t ->
      (FStarC_Extraction_ML_RemoveUnusedParameters.env_t * 'a))
  : (uenv * 'a)=
  let uu___ = f u.env_remove_typars in
  match uu___ with
  | (e, x) ->
      ({
         env_tcenv = (u.env_tcenv);
         env_bindings = (u.env_bindings);
         env_mlident_map = (u.env_mlident_map);
         env_remove_typars = e;
         mlpath_of_lid = (u.mlpath_of_lid);
         env_fieldname_map = (u.env_fieldname_map);
         mlpath_of_fieldname = (u.mlpath_of_fieldname);
         tydefs = (u.tydefs);
         type_names = (u.type_names);
         tydef_declarations = (u.tydef_declarations);
         currentModule = (u.currentModule)
       }, x)
let bindings_of_uenv (u : uenv) : mlbinding Prims.list= u.env_bindings
let dbg : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Extraction"
let debug (g : uenv) (f : unit -> unit) : unit=
  let uu___ = FStarC_Effect.op_Bang dbg in if uu___ then f () else ()
let print_mlpath_map (g : uenv) : Prims.string=
  let string_of_mlpath mlp =
    Prims.strcat (FStarC_String.concat "." (FStar_Pervasives_Native.fst mlp))
      (Prims.strcat "." (FStar_Pervasives_Native.snd mlp)) in
  let entries =
    FStarC_PSMap.fold g.mlpath_of_lid
      (fun key value entries1 ->
         let uu___ =
           FStarC_Format.fmt2 "%s -> %s" key (string_of_mlpath value) in
         uu___ :: entries1) [] in
  FStarC_String.concat "\n" entries
type lookup_res =
  | Found of exp_binding 
  | WasErased of FStarC_Range_Type.t 
  | NotFound 
let uu___is_Found (projectee : lookup_res) : Prims.bool=
  match projectee with | Found _0 -> true | uu___ -> false
let __proj__Found__item___0 (projectee : lookup_res) : exp_binding=
  match projectee with | Found _0 -> _0
let uu___is_WasErased (projectee : lookup_res) : Prims.bool=
  match projectee with | WasErased _0 -> true | uu___ -> false
let __proj__WasErased__item___0 (projectee : lookup_res) :
  FStarC_Range_Type.t= match projectee with | WasErased _0 -> _0
let uu___is_NotFound (projectee : lookup_res) : Prims.bool=
  match projectee with | NotFound -> true | uu___ -> false
let showable_lookup_res : lookup_res FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Found t -> "Found .."
         | WasErased r ->
             let uu___1 =
               FStarC_Class_Show.show FStarC_Range_Ops.showable_range r in
             Prims.strcat "WasErased " uu___1
         | NotFound -> "NotFound")
  }
let lookup_fv_generic (g : uenv) (fv : FStarC_Syntax_Syntax.fv) : lookup_res=
  let v =
    FStarC_Util.find_map g.env_bindings
      (fun uu___ ->
         match uu___ with
         | Fv (fv', t) when FStarC_Syntax_Syntax.fv_eq fv fv' ->
             FStar_Pervasives_Native.Some (Found t)
         | ErasedFv fv' when FStarC_Syntax_Syntax.fv_eq fv fv' ->
             let uu___1 =
               let uu___2 =
                 FStarC_Class_HasRange.pos FStarC_Syntax_Syntax.hasRange_fv
                   fv' in
               WasErased uu___2 in
             FStar_Pervasives_Native.Some uu___1
         | uu___1 -> FStar_Pervasives_Native.None) in
  match v with
  | FStar_Pervasives_Native.Some r -> r
  | FStar_Pervasives_Native.None -> NotFound
let try_lookup_fv (r : FStarC_Range_Type.t) (g : uenv)
  (fv : FStarC_Syntax_Syntax.fv) :
  exp_binding FStar_Pervasives_Native.option=
  let uu___ = lookup_fv_generic g fv in
  match uu___ with
  | Found r1 -> FStar_Pervasives_Native.Some r1
  | WasErased pos ->
      ((let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                FStarC_Ident.string_of_lid fv.FStarC_Syntax_Syntax.fv_name in
              FStarC_Format.fmt1
                "Will not extract reference to variable `%s` since it has the `noextract` qualifier."
                uu___5 in
            FStarC_Errors_Msg.text uu___4 in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  FStarC_Ident.string_of_lid fv.FStarC_Syntax_Syntax.fv_name in
                let uu___8 =
                  FStarC_Class_Show.show FStarC_Range_Ops.showable_range pos in
                FStarC_Format.fmt2
                  "Either remove the noextract qualifier from %s (defined in %s) or add it to this definition."
                  uu___7 uu___8 in
              FStarC_Errors_Msg.text uu___6 in
            let uu___6 =
              let uu___7 =
                let uu___8 =
                  let uu___9 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int
                      FStarC_Errors.call_to_erased_errno in
                  FStarC_Format.fmt1
                    "This error can be ignored with `--warn_error -%s`."
                    uu___9 in
                FStarC_Errors_Msg.text uu___8 in
              [uu___7] in
            uu___5 :: uu___6 in
          uu___3 :: uu___4 in
        FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
          FStarC_Errors_Codes.Error_CallToErased ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic uu___2));
       FStar_Pervasives_Native.None)
  | NotFound -> FStar_Pervasives_Native.None
let lookup_fv (r : FStarC_Range_Type.t) (g : uenv)
  (fv : FStarC_Syntax_Syntax.fv) : exp_binding=
  let uu___ = lookup_fv_generic g fv in
  match uu___ with
  | Found t -> t
  | res ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_Class_HasRange.pos FStarC_Syntax_Syntax.hasRange_fv fv in
          FStarC_Range_Ops.string_of_range uu___3 in
        let uu___3 =
          FStarC_Class_Show.show FStarC_Ident.showable_lident
            fv.FStarC_Syntax_Syntax.fv_name in
        let uu___4 = FStarC_Class_Show.show showable_lookup_res res in
        FStarC_Format.fmt3
          "Internal error: (%s) free variable %s not found during extraction (res=%s)\n"
          uu___2 uu___3 uu___4 in
      failwith uu___1
let lookup_bv (g : uenv) (bv : FStarC_Syntax_Syntax.bv) : ty_or_exp_b=
  let x =
    FStarC_Util.find_map g.env_bindings
      (fun uu___ ->
         match uu___ with
         | Bv (bv', r) when FStarC_Syntax_Syntax.bv_eq bv bv' ->
             FStar_Pervasives_Native.Some r
         | uu___1 -> FStar_Pervasives_Native.None) in
  match x with
  | FStar_Pervasives_Native.None ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Ident.range_of_id bv.FStarC_Syntax_Syntax.ppname in
          FStarC_Range_Ops.string_of_range uu___2 in
        let uu___2 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv bv in
        FStarC_Format.fmt2 "(%s) bound Variable %s not found\n" uu___1 uu___2 in
      failwith uu___
  | FStar_Pervasives_Native.Some y -> y
let lookup_term (g : uenv) (t : FStarC_Syntax_Syntax.term) :
  (ty_or_exp_b * FStarC_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)=
  match t.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_name x ->
      let uu___ = lookup_bv g x in (uu___, FStar_Pervasives_Native.None)
  | FStarC_Syntax_Syntax.Tm_fvar x ->
      let uu___ =
        let uu___1 = lookup_fv t.FStarC_Syntax_Syntax.pos g x in
        FStar_Pervasives.Inr uu___1 in
      (uu___, (x.FStarC_Syntax_Syntax.fv_qual))
  | uu___ -> failwith "Impossible: lookup_term for a non-name"
let lookup_ty (g : uenv) (x : FStarC_Syntax_Syntax.bv) : ty_binding=
  let uu___ = lookup_bv g x in
  match uu___ with
  | FStar_Pervasives.Inl ty -> ty
  | uu___1 -> failwith "Expected a type name"
let lookup_tydef (env : uenv) (uu___ : FStarC_Extraction_ML_Syntax.mlpath) :
  FStarC_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option=
  match uu___ with
  | (module_name, ty_name) ->
      FStarC_Util.find_map env.tydefs
        (fun tydef1 ->
           if
             (ty_name = tydef1.tydef_name) &&
               (module_name = tydef1.tydef_mlmodule_name)
           then FStar_Pervasives_Native.Some (tydef1.tydef_def)
           else FStar_Pervasives_Native.None)
let has_tydef_declaration (u : uenv) (l : FStarC_Ident.lid) : Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Ident.string_of_lid l in
    FStarC_PSMap.try_find u.tydef_declarations uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some b -> b
let mlpath_of_lident (g : uenv) (x : FStarC_Ident.lident) :
  FStarC_Extraction_ML_Syntax.mlpath=
  let uu___ =
    let uu___1 = FStarC_Ident.string_of_lid x in
    FStarC_PSMap.try_find g.mlpath_of_lid uu___1 in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      (debug g
         (fun uu___2 ->
            (let uu___4 = FStarC_Ident.string_of_lid x in
             FStarC_Format.print1 "Identifier not found: %s" uu___4);
            (let uu___4 = print_mlpath_map g in
             FStarC_Format.print1 "Env is \n%s\n" uu___4));
       (let uu___2 =
          let uu___3 = FStarC_Ident.string_of_lid x in
          Prims.strcat "Identifier not found: " uu___3 in
        failwith uu___2))
  | FStar_Pervasives_Native.Some mlp -> mlp
let is_type_name (g : uenv) (fv : FStarC_Syntax_Syntax.fv) : Prims.bool=
  FStarC_Util.for_some
    (fun uu___ ->
       match uu___ with | (x, uu___1) -> FStarC_Syntax_Syntax.fv_eq fv x)
    g.type_names
let is_fv_type (g : uenv) (fv : FStarC_Syntax_Syntax.fv) : Prims.bool=
  (is_type_name g fv) ||
    (FStarC_Util.for_some
       (fun tydef1 -> FStarC_Syntax_Syntax.fv_eq fv tydef1.tydef_fv) 
       g.tydefs)
let no_fstar_stubs_ns (ns : FStarC_Extraction_ML_Syntax.mlsymbol Prims.list)
  : FStarC_Extraction_ML_Syntax.mlsymbol Prims.list=
  match ns with
  | "FStar"::"NormSteps"::rest when plug () -> "Fstarcompiler.FStarC" ::
      "NormSteps" :: rest
  | "FStar"::"Stubs"::rest when plug_no_lib () -> "FStarC" :: rest
  | "FStar"::"Stubs"::"Tactics"::"V1"::"Builtins"::[] when plug () ->
      ["FStarC"; "Tactics"; "V1"; "Builtins"]
  | "FStar"::"Stubs"::"Tactics"::"V2"::"Builtins"::[] when plug () ->
      ["FStarC"; "Tactics"; "V2"; "Builtins"]
  | "FStar"::"Stubs"::"Tactics"::"Unseal"::[] when plug () ->
      ["FStarC"; "Tactics"; "Unseal"]
  | "FStar"::"Stubs"::rest when plug () -> "Fstarcompiler.FStarC" :: rest
  | "FStar"::"Stubs"::rest -> "FStar" :: rest
  | uu___ -> ns
let no_fstar_stubs (p : FStarC_Extraction_ML_Syntax.mlpath) :
  FStarC_Extraction_ML_Syntax.mlpath=
  let uu___ = p in
  match uu___ with | (ns, id) -> let ns1 = no_fstar_stubs_ns ns in (ns1, id)
let lookup_record_field_name (g : uenv)
  (uu___ : (FStarC_Ident.lident * FStarC_Ident.ident)) :
  FStarC_Extraction_ML_Syntax.mlpath=
  match uu___ with
  | (type_name, fn) ->
      let key =
        let uu___1 =
          let uu___2 = FStarC_Ident.ids_of_lid type_name in
          FStarC_List.op_At uu___2 [fn] in
        FStarC_Ident.lid_of_ids uu___1 in
      let uu___1 =
        let uu___2 = FStarC_Ident.string_of_lid key in
        FStarC_PSMap.try_find g.mlpath_of_fieldname uu___2 in
      (match uu___1 with
       | FStar_Pervasives_Native.None ->
           let uu___2 =
             let uu___3 = FStarC_Ident.string_of_lid key in
             Prims.strcat "Field name not found: " uu___3 in
           failwith uu___2
       | FStar_Pervasives_Native.Some mlp ->
           let uu___2 = mlp in
           (match uu___2 with
            | (ns, id) -> let ns1 = no_fstar_stubs_ns ns in (ns1, id)))
let initial_mlident_map : unit -> Prims.string FStarC_PSMap.t=
  let map = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  fun uu___ ->
    let uu___1 = FStarC_Effect.op_Bang map in
    match uu___1 with
    | FStar_Pervasives_Native.Some m -> m
    | FStar_Pervasives_Native.None ->
        let m =
          let uu___2 =
            let uu___3 = FStarC_Options.codegen () in
            match uu___3 with
            | FStar_Pervasives_Native.Some (FStarC_Options.FSharp) ->
                FStarC_Extraction_ML_Syntax.fsharpkeywords
            | FStar_Pervasives_Native.Some (FStarC_Options.OCaml) ->
                FStarC_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStarC_Options.Plugin) ->
                FStarC_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStarC_Options.PluginNoLib) ->
                FStarC_Extraction_ML_Syntax.ocamlkeywords
            | FStar_Pervasives_Native.Some (FStarC_Options.Krml) ->
                FStarC_Extraction_ML_Syntax.krml_keywords
            | FStar_Pervasives_Native.Some (FStarC_Options.Extension) -> []
            | FStar_Pervasives_Native.None -> [] in
          let uu___3 = FStarC_PSMap.empty () in
          FStarC_List.fold_right (fun x m1 -> FStarC_PSMap.add m1 x "")
            uu___2 uu___3 in
        (FStarC_Effect.op_Colon_Equals map (FStar_Pervasives_Native.Some m);
         m)
let rename_conventional (s : Prims.string)
  (is_local_type_variable : Prims.bool) : Prims.string=
  let cs = FStar_String.list_of_string s in
  let sanitize_typ uu___ =
    let valid_rest c = FStarC_Util.is_letter_or_digit c in
    let aux cs1 =
      FStarC_List.map
        (fun x -> let uu___1 = valid_rest x in if uu___1 then x else 117) cs1 in
    let uu___1 = let uu___2 = FStarC_List.hd cs in uu___2 = 39 in
    if uu___1
    then
      let uu___2 = FStarC_List.hd cs in
      let uu___3 = let uu___4 = FStarC_List.tail cs in aux uu___4 in uu___2
        :: uu___3
    else (let uu___3 = aux cs in 39 :: uu___3) in
  let sanitize_term uu___ =
    let valid c =
      ((FStarC_Util.is_letter_or_digit c) || (c = 95)) || (c = 39) in
    let cs' =
      FStarC_List.fold_right
        (fun c cs1 ->
           let uu___1 =
             let uu___2 = valid c in if uu___2 then [c] else [95; 95] in
           FStarC_List.op_At uu___1 cs1) cs [] in
    match cs' with
    | c::cs1 when (FStarC_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
    | uu___1 -> cs in
  let uu___ =
    if is_local_type_variable then sanitize_typ () else sanitize_term () in
  FStar_String.string_of_list uu___
let root_name_of_bv (x : FStarC_Syntax_Syntax.bv) :
  FStarC_Extraction_ML_Syntax.mlident=
  let uu___ =
    (let uu___1 = FStarC_Ident.string_of_id x.FStarC_Syntax_Syntax.ppname in
     FStarC_Util.starts_with uu___1 FStarC_Ident.reserved_prefix) ||
      (FStarC_Syntax_Syntax.is_null_bv x) in
  if uu___
  then FStarC_Ident.reserved_prefix
  else FStarC_Ident.string_of_id x.FStarC_Syntax_Syntax.ppname
let find_uniq (ml_ident_map : Prims.string FStarC_PSMap.t)
  (root_name : Prims.string) (is_local_type_variable : Prims.bool) :
  (Prims.string * Prims.string FStarC_PSMap.t)=
  let rec aux i root_name1 =
    let target_mlident =
      if i = Prims.int_zero
      then root_name1
      else
        (let uu___1 = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
         Prims.strcat root_name1 uu___1) in
    let uu___ = FStarC_PSMap.try_find ml_ident_map target_mlident in
    match uu___ with
    | FStar_Pervasives_Native.Some x -> aux (i + Prims.int_one) root_name1
    | FStar_Pervasives_Native.None ->
        let map = FStarC_PSMap.add ml_ident_map target_mlident "" in
        (target_mlident, map) in
  let mlident = rename_conventional root_name is_local_type_variable in
  if is_local_type_variable
  then
    let uu___ =
      let uu___1 = FStarC_Util.substring_from mlident Prims.int_one in
      aux Prims.int_zero uu___1 in
    match uu___ with | (nm, map) -> ((Prims.strcat "'" nm), map)
  else aux Prims.int_zero mlident
let mlns_of_lid (x : FStarC_Ident.lident) :
  FStarC_Extraction_ML_Syntax.mlsymbol Prims.list=
  let uu___ =
    let uu___1 = FStarC_Ident.ns_of_lid x in
    FStarC_List.map FStarC_Ident.string_of_id uu___1 in
  no_fstar_stubs_ns uu___
let new_mlpath_of_lident (g : uenv) (x : FStarC_Ident.lident) :
  (FStarC_Extraction_ML_Syntax.mlpath * uenv)=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Parser_Const.failwith_lid () in
      FStarC_Ident.lid_equals x uu___2 in
    if uu___1
    then
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_Ident.ident_of_lid x in
          FStarC_Ident.string_of_id uu___4 in
        ([], uu___3) in
      (uu___2, g)
    else
      (let uu___3 =
         let uu___4 =
           let uu___5 = FStarC_Ident.ident_of_lid x in
           FStarC_Ident.string_of_id uu___5 in
         find_uniq g.env_mlident_map uu___4 false in
       match uu___3 with
       | (name, map) ->
           let g1 =
             {
               env_tcenv = (g.env_tcenv);
               env_bindings = (g.env_bindings);
               env_mlident_map = map;
               env_remove_typars = (g.env_remove_typars);
               mlpath_of_lid = (g.mlpath_of_lid);
               env_fieldname_map = (g.env_fieldname_map);
               mlpath_of_fieldname = (g.mlpath_of_fieldname);
               tydefs = (g.tydefs);
               type_names = (g.type_names);
               tydef_declarations = (g.tydef_declarations);
               currentModule = (g.currentModule)
             } in
           let uu___4 = let uu___5 = mlns_of_lid x in (uu___5, name) in
           (uu___4, g1)) in
  match uu___ with
  | (mlp, g1) ->
      let guts uu___1 =
        match uu___1 with
        | (p::ps, l) -> (((Prims.strcat "Fstarcompiler." p) :: ps), l) in
      let mlp1 =
        let uu___1 = FStarC_Ident.string_of_lid x in
        match uu___1 with
        | "Prims.dtuple2" when plug () -> guts mlp
        | "Prims.Mkdtuple2" when plug () -> guts mlp
        | "FStar.Pervasives.either" when plug () -> guts mlp
        | "FStar.Pervasives.Inl" when plug () -> guts mlp
        | "FStar.Pervasives.Inr" when plug () -> guts mlp
        | "FStar.Stubs.Tactics.Common.Stop" ->
            (["Fstarcompiler.FStarC"; "Errors"], "Stop")
        | uu___2 -> mlp in
      let g2 =
        let uu___1 =
          let uu___2 = FStarC_Ident.string_of_lid x in
          FStarC_PSMap.add g1.mlpath_of_lid uu___2 mlp1 in
        {
          env_tcenv = (g1.env_tcenv);
          env_bindings = (g1.env_bindings);
          env_mlident_map = (g1.env_mlident_map);
          env_remove_typars = (g1.env_remove_typars);
          mlpath_of_lid = uu___1;
          env_fieldname_map = (g1.env_fieldname_map);
          mlpath_of_fieldname = (g1.mlpath_of_fieldname);
          tydefs = (g1.tydefs);
          type_names = (g1.type_names);
          tydef_declarations = (g1.tydef_declarations);
          currentModule = (g1.currentModule)
        } in
      (mlp1, g2)
let extend_ty (g : uenv) (a : FStarC_Syntax_Syntax.bv)
  (map_to_top : Prims.bool) : uenv=
  let is_local_type_variable = Prims.op_Negation map_to_top in
  let uu___ =
    let uu___1 = root_name_of_bv a in
    find_uniq g.env_mlident_map uu___1 is_local_type_variable in
  match uu___ with
  | (ml_a, mlident_map) ->
      let mapped_to =
        if map_to_top
        then FStarC_Extraction_ML_Syntax.MLTY_Top
        else FStarC_Extraction_ML_Syntax.MLTY_Var ml_a in
      let gamma =
        (Bv
           (a,
             (FStar_Pervasives.Inl { ty_b_name = ml_a; ty_b_ty = mapped_to })))
        :: (g.env_bindings) in
      let tcenv = FStarC_TypeChecker_Env.push_bv g.env_tcenv a in
      {
        env_tcenv = tcenv;
        env_bindings = gamma;
        env_mlident_map = mlident_map;
        env_remove_typars = (g.env_remove_typars);
        mlpath_of_lid = (g.mlpath_of_lid);
        env_fieldname_map = (g.env_fieldname_map);
        mlpath_of_fieldname = (g.mlpath_of_fieldname);
        tydefs = (g.tydefs);
        type_names = (g.type_names);
        tydef_declarations = (g.tydef_declarations);
        currentModule = (g.currentModule)
      }
let extend_bv (g : uenv) (x : FStarC_Syntax_Syntax.bv)
  (t_x : FStarC_Extraction_ML_Syntax.mltyscheme) (add_unit : Prims.bool)
  (mk_unit : Prims.bool) :
  (uenv * FStarC_Extraction_ML_Syntax.mlident * exp_binding)=
  let ml_ty =
    match t_x with
    | ([], t) -> t
    | uu___ -> FStarC_Extraction_ML_Syntax.MLTY_Top in
  let uu___ =
    let uu___1 = root_name_of_bv x in
    find_uniq g.env_mlident_map uu___1 false in
  match uu___ with
  | (mlident, mlident_map) ->
      let mlx = FStarC_Extraction_ML_Syntax.MLE_Var mlident in
      let mlx1 =
        if mk_unit
        then FStarC_Extraction_ML_Syntax.ml_unit
        else
          if add_unit
          then
            (let uu___2 =
               let uu___3 =
                 let uu___4 =
                   FStarC_Extraction_ML_Syntax.with_ty
                     FStarC_Extraction_ML_Syntax.MLTY_Top mlx in
                 (uu___4, [FStarC_Extraction_ML_Syntax.ml_unit]) in
               FStarC_Extraction_ML_Syntax.MLE_App uu___3 in
             FStarC_Extraction_ML_Syntax.with_ty
               FStarC_Extraction_ML_Syntax.MLTY_Top uu___2)
          else FStarC_Extraction_ML_Syntax.with_ty ml_ty mlx in
      let uu___1 =
        if add_unit
        then FStarC_Extraction_ML_Syntax.pop_unit t_x
        else (FStarC_Extraction_ML_Syntax.E_PURE, t_x) in
      (match uu___1 with
       | (eff, t_x1) ->
           let exp_binding1 =
             {
               exp_b_name = mlident;
               exp_b_expr = mlx1;
               exp_b_tscheme = t_x1;
               exp_b_eff = eff
             } in
           let gamma = (Bv (x, (FStar_Pervasives.Inr exp_binding1))) ::
             (g.env_bindings) in
           let tcenv =
             let uu___2 = FStarC_Syntax_Syntax.binders_of_list [x] in
             FStarC_TypeChecker_Env.push_binders g.env_tcenv uu___2 in
           ({
              env_tcenv = tcenv;
              env_bindings = gamma;
              env_mlident_map = mlident_map;
              env_remove_typars = (g.env_remove_typars);
              mlpath_of_lid = (g.mlpath_of_lid);
              env_fieldname_map = (g.env_fieldname_map);
              mlpath_of_fieldname = (g.mlpath_of_fieldname);
              tydefs = (g.tydefs);
              type_names = (g.type_names);
              tydef_declarations = (g.tydef_declarations);
              currentModule = (g.currentModule)
            }, mlident, exp_binding1))
let burn_name (g : uenv) (i : FStarC_Extraction_ML_Syntax.mlident) : 
  uenv=
  let uu___ = FStarC_PSMap.add g.env_mlident_map i "" in
  {
    env_tcenv = (g.env_tcenv);
    env_bindings = (g.env_bindings);
    env_mlident_map = uu___;
    env_remove_typars = (g.env_remove_typars);
    mlpath_of_lid = (g.mlpath_of_lid);
    env_fieldname_map = (g.env_fieldname_map);
    mlpath_of_fieldname = (g.mlpath_of_fieldname);
    tydefs = (g.tydefs);
    type_names = (g.type_names);
    tydef_declarations = (g.tydef_declarations);
    currentModule = (g.currentModule)
  }
let new_mlident (g : uenv) : (uenv * FStarC_Extraction_ML_Syntax.mlident)=
  let ml_ty = FStarC_Extraction_ML_Syntax.MLTY_Top in
  let x =
    FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStarC_Syntax_Syntax.tun in
  let uu___ =
    extend_bv g x ([], FStarC_Extraction_ML_Syntax.MLTY_Top) false false in
  match uu___ with | (g1, id, uu___1) -> (g1, id)
let extend_fv (g : uenv) (x : FStarC_Syntax_Syntax.fv)
  (t_x : FStarC_Extraction_ML_Syntax.mltyscheme) (add_unit : Prims.bool) :
  (uenv * FStarC_Extraction_ML_Syntax.mlident * exp_binding)=
  let rec mltyFvars t =
    match t with
    | FStarC_Extraction_ML_Syntax.MLTY_Var x1 -> [x1]
    | FStarC_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) ->
        let uu___ = mltyFvars t1 in
        let uu___1 = mltyFvars t2 in FStarC_List.append uu___ uu___1
    | FStarC_Extraction_ML_Syntax.MLTY_Named (args, path) ->
        FStarC_List.collect mltyFvars args
    | FStarC_Extraction_ML_Syntax.MLTY_Tuple ts ->
        FStarC_List.collect mltyFvars ts
    | FStarC_Extraction_ML_Syntax.MLTY_Top -> []
    | FStarC_Extraction_ML_Syntax.MLTY_Erased -> [] in
  let rec subsetMlidents la lb =
    match la with
    | h::tla -> (FStarC_List.contains h lb) && (subsetMlidents tla lb)
    | [] -> true in
  let tySchemeIsClosed tys =
    let uu___ = mltyFvars (FStar_Pervasives_Native.snd tys) in
    let uu___1 =
      FStarC_Extraction_ML_Syntax.ty_param_names
        (FStar_Pervasives_Native.fst tys) in
    subsetMlidents uu___ uu___1 in
  let uu___ = tySchemeIsClosed t_x in
  if uu___
  then
    let ml_ty =
      match t_x with
      | ([], t) -> t
      | uu___1 -> FStarC_Extraction_ML_Syntax.MLTY_Top in
    let uu___1 = new_mlpath_of_lident g x.FStarC_Syntax_Syntax.fv_name in
    match uu___1 with
    | (mlpath, g1) ->
        let mlsymbol = FStar_Pervasives_Native.snd mlpath in
        let mly = FStarC_Extraction_ML_Syntax.MLE_Name mlpath in
        let mly1 =
          if add_unit
          then
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_Extraction_ML_Syntax.with_ty
                    FStarC_Extraction_ML_Syntax.MLTY_Top mly in
                (uu___4, [FStarC_Extraction_ML_Syntax.ml_unit]) in
              FStarC_Extraction_ML_Syntax.MLE_App uu___3 in
            FStarC_Extraction_ML_Syntax.with_ty
              FStarC_Extraction_ML_Syntax.MLTY_Top uu___2
          else FStarC_Extraction_ML_Syntax.with_ty ml_ty mly in
        let uu___2 =
          if add_unit
          then FStarC_Extraction_ML_Syntax.pop_unit t_x
          else (FStarC_Extraction_ML_Syntax.E_PURE, t_x) in
        (match uu___2 with
         | (eff, t_x1) ->
             let exp_binding1 =
               {
                 exp_b_name = mlsymbol;
                 exp_b_expr = mly1;
                 exp_b_tscheme = t_x1;
                 exp_b_eff = eff
               } in
             let gamma = (Fv (x, exp_binding1)) :: (g1.env_bindings) in
             let mlident_map =
               FStarC_PSMap.add g1.env_mlident_map mlsymbol "" in
             ({
                env_tcenv = (g1.env_tcenv);
                env_bindings = gamma;
                env_mlident_map = mlident_map;
                env_remove_typars = (g1.env_remove_typars);
                mlpath_of_lid = (g1.mlpath_of_lid);
                env_fieldname_map = (g1.env_fieldname_map);
                mlpath_of_fieldname = (g1.mlpath_of_fieldname);
                tydefs = (g1.tydefs);
                type_names = (g1.type_names);
                tydef_declarations = (g1.tydef_declarations);
                currentModule = (g1.currentModule)
              }, mlsymbol, exp_binding1))
  else
    (let uu___2 =
       let uu___3 = FStarC_Extraction_ML_Syntax.mltyscheme_to_string t_x in
       FStarC_Format.fmt1 "freevars found (%s)" uu___3 in
     failwith uu___2)
let extend_erased_fv (g : uenv) (f : FStarC_Syntax_Syntax.fv) : uenv=
  {
    env_tcenv = (g.env_tcenv);
    env_bindings = ((ErasedFv f) :: (g.env_bindings));
    env_mlident_map = (g.env_mlident_map);
    env_remove_typars = (g.env_remove_typars);
    mlpath_of_lid = (g.mlpath_of_lid);
    env_fieldname_map = (g.env_fieldname_map);
    mlpath_of_fieldname = (g.mlpath_of_fieldname);
    tydefs = (g.tydefs);
    type_names = (g.type_names);
    tydef_declarations = (g.tydef_declarations);
    currentModule = (g.currentModule)
  }
let extend_lb (g : uenv) (l : FStarC_Syntax_Syntax.lbname)
  (t : FStarC_Syntax_Syntax.typ)
  (t_x : FStarC_Extraction_ML_Syntax.mltyscheme) (add_unit : Prims.bool) :
  (uenv * FStarC_Extraction_ML_Syntax.mlident * exp_binding)=
  match l with
  | FStar_Pervasives.Inl x -> extend_bv g x t_x add_unit false
  | FStar_Pervasives.Inr f -> extend_fv g f t_x add_unit
let extend_tydef (g : uenv) (fv : FStarC_Syntax_Syntax.fv)
  (ts : FStarC_Extraction_ML_Syntax.mltyscheme)
  (meta : FStarC_Extraction_ML_Syntax.metadata) :
  (tydef * FStarC_Extraction_ML_Syntax.mlpath * uenv)=
  let uu___ = new_mlpath_of_lident g fv.FStarC_Syntax_Syntax.fv_name in
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
        {
          env_tcenv = (g1.env_tcenv);
          env_bindings = (g1.env_bindings);
          env_mlident_map = (g1.env_mlident_map);
          env_remove_typars = (g1.env_remove_typars);
          mlpath_of_lid = (g1.mlpath_of_lid);
          env_fieldname_map = (g1.env_fieldname_map);
          mlpath_of_fieldname = (g1.mlpath_of_fieldname);
          tydefs = (tydef1 :: (g1.tydefs));
          type_names = ((fv, name) :: (g1.type_names));
          tydef_declarations = (g1.tydef_declarations);
          currentModule = (g1.currentModule)
        })
let extend_with_tydef_declaration (u : uenv) (l : FStarC_Ident.lident) :
  uenv=
  let uu___ =
    let uu___1 = FStarC_Ident.string_of_lid l in
    FStarC_PSMap.add u.tydef_declarations uu___1 true in
  {
    env_tcenv = (u.env_tcenv);
    env_bindings = (u.env_bindings);
    env_mlident_map = (u.env_mlident_map);
    env_remove_typars = (u.env_remove_typars);
    mlpath_of_lid = (u.mlpath_of_lid);
    env_fieldname_map = (u.env_fieldname_map);
    mlpath_of_fieldname = (u.mlpath_of_fieldname);
    tydefs = (u.tydefs);
    type_names = (u.type_names);
    tydef_declarations = uu___;
    currentModule = (u.currentModule)
  }
let extend_type_name (g : uenv) (fv : FStarC_Syntax_Syntax.fv) :
  (FStarC_Extraction_ML_Syntax.mlpath * uenv)=
  let uu___ = new_mlpath_of_lident g fv.FStarC_Syntax_Syntax.fv_name in
  match uu___ with
  | (name, g1) ->
      (name,
        {
          env_tcenv = (g1.env_tcenv);
          env_bindings = (g1.env_bindings);
          env_mlident_map = (g1.env_mlident_map);
          env_remove_typars = (g1.env_remove_typars);
          mlpath_of_lid = (g1.mlpath_of_lid);
          env_fieldname_map = (g1.env_fieldname_map);
          mlpath_of_fieldname = (g1.mlpath_of_fieldname);
          tydefs = (g1.tydefs);
          type_names = ((fv, name) :: (g1.type_names));
          tydef_declarations = (g1.tydef_declarations);
          currentModule = (g1.currentModule)
        })
let extend_with_monad_op_name (g : uenv) (ed : FStarC_Syntax_Syntax.eff_decl)
  (nm : Prims.string) (ts : FStarC_Extraction_ML_Syntax.mltyscheme) :
  (FStarC_Extraction_ML_Syntax.mlpath * FStarC_Ident.lident * exp_binding *
    uenv)=
  let lid =
    let uu___ = FStarC_Ident.id_of_text nm in
    FStarC_Syntax_Util.mk_field_projector_name_from_ident
      ed.FStarC_Syntax_Syntax.mname uu___ in
  let uu___ =
    let uu___1 =
      FStarC_Syntax_Syntax.lid_as_fv lid FStar_Pervasives_Native.None in
    extend_fv g uu___1 ts false in
  match uu___ with
  | (g1, mlid, exp_b) ->
      let mlp = let uu___1 = mlns_of_lid lid in (uu___1, mlid) in
      (mlp, lid, exp_b, g1)
let extend_with_action_name (g : uenv) (ed : FStarC_Syntax_Syntax.eff_decl)
  (a : FStarC_Syntax_Syntax.action)
  (ts : FStarC_Extraction_ML_Syntax.mltyscheme) :
  (FStarC_Extraction_ML_Syntax.mlpath * FStarC_Ident.lident * exp_binding *
    uenv)=
  let nm =
    let uu___ = FStarC_Ident.ident_of_lid a.FStarC_Syntax_Syntax.action_name in
    FStarC_Ident.string_of_id uu___ in
  let module_name = FStarC_Ident.ns_of_lid ed.FStarC_Syntax_Syntax.mname in
  let lid =
    let uu___ =
      let uu___1 = let uu___2 = FStarC_Ident.id_of_text nm in [uu___2] in
      FStarC_List.op_At module_name uu___1 in
    FStarC_Ident.lid_of_ids uu___ in
  let uu___ =
    let uu___1 =
      FStarC_Syntax_Syntax.lid_as_fv lid FStar_Pervasives_Native.None in
    extend_fv g uu___1 ts false in
  match uu___ with
  | (g1, mlid, exp_b) ->
      let mlp = let uu___1 = mlns_of_lid lid in (uu___1, mlid) in
      (mlp, lid, exp_b, g1)
let extend_record_field_name (g : uenv)
  (uu___ : (FStarC_Ident.lident * FStarC_Ident.ident)) :
  (FStarC_Extraction_ML_Syntax.mlident * uenv)=
  match uu___ with
  | (type_name, fn) ->
      let key =
        let uu___1 =
          let uu___2 = FStarC_Ident.ids_of_lid type_name in
          FStarC_List.op_At uu___2 [fn] in
        FStarC_Ident.lid_of_ids uu___1 in
      let uu___1 =
        let uu___2 = FStarC_Ident.string_of_id fn in
        find_uniq g.env_fieldname_map uu___2 false in
      (match uu___1 with
       | (name, fieldname_map) ->
           let ns = mlns_of_lid type_name in
           let mlp = (ns, name) in
           let mlp1 = no_fstar_stubs mlp in
           let g1 =
             let uu___2 =
               let uu___3 = FStarC_Ident.string_of_lid key in
               FStarC_PSMap.add g.mlpath_of_fieldname uu___3 mlp1 in
             {
               env_tcenv = (g.env_tcenv);
               env_bindings = (g.env_bindings);
               env_mlident_map = (g.env_mlident_map);
               env_remove_typars = (g.env_remove_typars);
               mlpath_of_lid = (g.mlpath_of_lid);
               env_fieldname_map = fieldname_map;
               mlpath_of_fieldname = uu___2;
               tydefs = (g.tydefs);
               type_names = (g.type_names);
               tydef_declarations = (g.tydef_declarations);
               currentModule = (g.currentModule)
             } in
           (name, g1))
let extend_with_module_name (g : uenv) (m : FStarC_Ident.lid) :
  (FStarC_Extraction_ML_Syntax.mlpath * uenv)=
  let ns = mlns_of_lid m in
  let p =
    let uu___ = FStarC_Ident.ident_of_lid m in
    FStarC_Ident.string_of_id uu___ in
  ((ns, p), g)
let exit_module (g : uenv) : uenv=
  let uu___ = initial_mlident_map () in
  let uu___1 = initial_mlident_map () in
  {
    env_tcenv = (g.env_tcenv);
    env_bindings = (g.env_bindings);
    env_mlident_map = uu___;
    env_remove_typars = (g.env_remove_typars);
    mlpath_of_lid = (g.mlpath_of_lid);
    env_fieldname_map = uu___1;
    mlpath_of_fieldname = (g.mlpath_of_fieldname);
    tydefs = (g.tydefs);
    type_names = (g.type_names);
    tydef_declarations = (g.tydef_declarations);
    currentModule = (g.currentModule)
  }
let new_uenv (e : FStarC_TypeChecker_Env.env) : uenv=
  let env =
    let uu___ = initial_mlident_map () in
    let uu___1 = FStarC_PSMap.empty () in
    let uu___2 = initial_mlident_map () in
    let uu___3 = FStarC_PSMap.empty () in
    let uu___4 = FStarC_PSMap.empty () in
    {
      env_tcenv = e;
      env_bindings = [];
      env_mlident_map = uu___;
      env_remove_typars =
        FStarC_Extraction_ML_RemoveUnusedParameters.initial_env;
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
    ([{
        FStarC_Extraction_ML_Syntax.ty_param_name = a;
        FStarC_Extraction_ML_Syntax.ty_param_attrs = []
      }],
      (FStarC_Extraction_ML_Syntax.MLTY_Fun
         ((FStarC_Extraction_ML_Syntax.MLTY_Named ([], (["Prims"], "string"))),
           FStarC_Extraction_ML_Syntax.E_IMPURE,
           (FStarC_Extraction_ML_Syntax.MLTY_Var a)))) in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Parser_Const.failwith_lid () in
        FStarC_Syntax_Syntax.lid_as_fv uu___3 FStar_Pervasives_Native.None in
      FStar_Pervasives.Inr uu___2 in
    extend_lb env uu___1 FStarC_Syntax_Syntax.tun failwith_ty false in
  match uu___ with | (g, uu___1, uu___2) -> g
