open Prims
type argument_tag =
  | Retain 
  | Omit 
let (uu___is_Retain : argument_tag -> Prims.bool) =
  fun projectee -> match projectee with | Retain -> true | uu___ -> false
let (uu___is_Omit : argument_tag -> Prims.bool) =
  fun projectee -> match projectee with | Omit -> true | uu___ -> false
type entry = argument_tag Prims.list
type env_t =
  {
  current_module: FStarC_Extraction_ML_Syntax.mlsymbol Prims.list ;
  tydef_map: entry FStarC_Compiler_Util.psmap }
let (__proj__Mkenv_t__item__current_module :
  env_t -> FStarC_Extraction_ML_Syntax.mlsymbol Prims.list) =
  fun projectee ->
    match projectee with | { current_module; tydef_map;_} -> current_module
let (__proj__Mkenv_t__item__tydef_map :
  env_t -> entry FStarC_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with | { current_module; tydef_map;_} -> tydef_map
let (initial_env : env_t) =
  let uu___ = FStarC_Compiler_Util.psmap_empty () in
  { current_module = []; tydef_map = uu___ }
type tydef =
  (FStarC_Extraction_ML_Syntax.mlsymbol *
    FStarC_Extraction_ML_Syntax.metadata *
    (FStarC_Extraction_ML_Syntax.mltyscheme, Prims.int)
    FStar_Pervasives.either)
let (extend_env :
  env_t -> FStarC_Extraction_ML_Syntax.mlsymbol -> entry -> env_t) =
  fun env ->
    fun i ->
      fun e ->
        let uu___ =
          let uu___1 =
            FStarC_Extraction_ML_Syntax.string_of_mlpath
              ((env.current_module), i) in
          FStarC_Compiler_Util.psmap_add env.tydef_map uu___1 e in
        { current_module = (env.current_module); tydef_map = uu___ }
let (lookup_tyname :
  env_t ->
    FStarC_Extraction_ML_Syntax.mlpath ->
      entry FStar_Pervasives_Native.option)
  =
  fun env ->
    fun name ->
      let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath name in
      FStarC_Compiler_Util.psmap_try_find env.tydef_map uu___
type var_set = FStarC_Extraction_ML_Syntax.mlident FStarC_Compiler_RBSet.t
let (empty_var_set : Prims.string FStarC_Compiler_RBSet.t) =
  Obj.magic
    (FStarC_Class_Setlike.empty ()
       (Obj.magic
          (FStarC_Compiler_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
       ())
let rec (freevars_of_mlty' :
  var_set -> FStarC_Extraction_ML_Syntax.mlty -> var_set) =
  fun uu___1 ->
    fun uu___ ->
      (fun vars ->
         fun t ->
           match t with
           | FStarC_Extraction_ML_Syntax.MLTY_Var i ->
               Obj.magic
                 (Obj.repr
                    (FStarC_Class_Setlike.add ()
                       (Obj.magic
                          (FStarC_Compiler_RBSet.setlike_rbset
                             FStarC_Class_Ord.ord_string)) i (Obj.magic vars)))
           | FStarC_Extraction_ML_Syntax.MLTY_Fun (t0, uu___, t1) ->
               Obj.magic
                 (Obj.repr
                    (let uu___1 = freevars_of_mlty' vars t0 in
                     freevars_of_mlty' uu___1 t1))
           | FStarC_Extraction_ML_Syntax.MLTY_Named (tys, uu___) ->
               Obj.magic
                 (Obj.repr
                    (FStarC_Compiler_List.fold_left freevars_of_mlty' vars
                       tys))
           | FStarC_Extraction_ML_Syntax.MLTY_Tuple tys ->
               Obj.magic
                 (Obj.repr
                    (FStarC_Compiler_List.fold_left freevars_of_mlty' vars
                       tys))
           | uu___ -> Obj.magic (Obj.repr vars)) uu___1 uu___
let (freevars_of_mlty : FStarC_Extraction_ML_Syntax.mlty -> var_set) =
  freevars_of_mlty' empty_var_set
let rec (elim_mlty :
  env_t ->
    FStarC_Extraction_ML_Syntax.mlty -> FStarC_Extraction_ML_Syntax.mlty)
  =
  fun env ->
    fun mlty ->
      match mlty with
      | FStarC_Extraction_ML_Syntax.MLTY_Var uu___ -> mlty
      | FStarC_Extraction_ML_Syntax.MLTY_Fun (t0, e, t1) ->
          let uu___ =
            let uu___1 = elim_mlty env t0 in
            let uu___2 = elim_mlty env t1 in (uu___1, e, uu___2) in
          FStarC_Extraction_ML_Syntax.MLTY_Fun uu___
      | FStarC_Extraction_ML_Syntax.MLTY_Named (args, name) ->
          let args1 = FStarC_Compiler_List.map (elim_mlty env) args in
          let uu___ = lookup_tyname env name in
          (match uu___ with
           | FStar_Pervasives_Native.None ->
               FStarC_Extraction_ML_Syntax.MLTY_Named (args1, name)
           | FStar_Pervasives_Native.Some entry1 ->
               (if
                  (FStarC_Compiler_List.length entry1) <>
                    (FStarC_Compiler_List.length args1)
                then
                  failwith
                    "Impossible: arity mismatch between definition and use"
                else ();
                (let args2 =
                   FStarC_Compiler_List.fold_right2
                     (fun arg ->
                        fun tag ->
                          fun out ->
                            match tag with
                            | Retain -> arg :: out
                            | uu___2 -> out) args1 entry1 [] in
                 FStarC_Extraction_ML_Syntax.MLTY_Named (args2, name))))
      | FStarC_Extraction_ML_Syntax.MLTY_Tuple tys ->
          let uu___ = FStarC_Compiler_List.map (elim_mlty env) tys in
          FStarC_Extraction_ML_Syntax.MLTY_Tuple uu___
      | FStarC_Extraction_ML_Syntax.MLTY_Top -> mlty
      | FStarC_Extraction_ML_Syntax.MLTY_Erased -> mlty
let rec (elim_mlexpr' :
  env_t ->
    FStarC_Extraction_ML_Syntax.mlexpr' ->
      FStarC_Extraction_ML_Syntax.mlexpr')
  =
  fun env ->
    fun e ->
      match e with
      | FStarC_Extraction_ML_Syntax.MLE_Const uu___ -> e
      | FStarC_Extraction_ML_Syntax.MLE_Var uu___ -> e
      | FStarC_Extraction_ML_Syntax.MLE_Name uu___ -> e
      | FStarC_Extraction_ML_Syntax.MLE_Let (lb, e1) ->
          let uu___ =
            let uu___1 = elim_letbinding env lb in
            let uu___2 = elim_mlexpr env e1 in (uu___1, uu___2) in
          FStarC_Extraction_ML_Syntax.MLE_Let uu___
      | FStarC_Extraction_ML_Syntax.MLE_App (e1, es) ->
          let uu___ =
            let uu___1 = elim_mlexpr env e1 in
            let uu___2 = FStarC_Compiler_List.map (elim_mlexpr env) es in
            (uu___1, uu___2) in
          FStarC_Extraction_ML_Syntax.MLE_App uu___
      | FStarC_Extraction_ML_Syntax.MLE_TApp (e1, tys) ->
          let uu___ =
            let uu___1 = FStarC_Compiler_List.map (elim_mlty env) tys in
            (e1, uu___1) in
          FStarC_Extraction_ML_Syntax.MLE_TApp uu___
      | FStarC_Extraction_ML_Syntax.MLE_Fun (bvs, e1) ->
          let uu___ =
            let uu___1 =
              FStarC_Compiler_List.map
                (fun b ->
                   let uu___2 =
                     elim_mlty env b.FStarC_Extraction_ML_Syntax.mlbinder_ty in
                   let uu___3 =
                     FStarC_Compiler_List.map (elim_mlexpr env)
                       b.FStarC_Extraction_ML_Syntax.mlbinder_attrs in
                   {
                     FStarC_Extraction_ML_Syntax.mlbinder_name =
                       (b.FStarC_Extraction_ML_Syntax.mlbinder_name);
                     FStarC_Extraction_ML_Syntax.mlbinder_ty = uu___2;
                     FStarC_Extraction_ML_Syntax.mlbinder_attrs = uu___3
                   }) bvs in
            let uu___2 = elim_mlexpr env e1 in (uu___1, uu___2) in
          FStarC_Extraction_ML_Syntax.MLE_Fun uu___
      | FStarC_Extraction_ML_Syntax.MLE_Match (e1, branches) ->
          let uu___ =
            let uu___1 = elim_mlexpr env e1 in
            let uu___2 = FStarC_Compiler_List.map (elim_branch env) branches in
            (uu___1, uu___2) in
          FStarC_Extraction_ML_Syntax.MLE_Match uu___
      | FStarC_Extraction_ML_Syntax.MLE_Coerce (e1, t0, t1) ->
          let uu___ =
            let uu___1 = elim_mlexpr env e1 in
            let uu___2 = elim_mlty env t0 in
            let uu___3 = elim_mlty env t1 in (uu___1, uu___2, uu___3) in
          FStarC_Extraction_ML_Syntax.MLE_Coerce uu___
      | FStarC_Extraction_ML_Syntax.MLE_CTor (l, es) ->
          let uu___ =
            let uu___1 = FStarC_Compiler_List.map (elim_mlexpr env) es in
            (l, uu___1) in
          FStarC_Extraction_ML_Syntax.MLE_CTor uu___
      | FStarC_Extraction_ML_Syntax.MLE_Seq es ->
          let uu___ = FStarC_Compiler_List.map (elim_mlexpr env) es in
          FStarC_Extraction_ML_Syntax.MLE_Seq uu___
      | FStarC_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu___ = FStarC_Compiler_List.map (elim_mlexpr env) es in
          FStarC_Extraction_ML_Syntax.MLE_Tuple uu___
      | FStarC_Extraction_ML_Syntax.MLE_Record (syms, nm, fields) ->
          let uu___ =
            let uu___1 =
              FStarC_Compiler_List.map
                (fun uu___2 ->
                   match uu___2 with
                   | (s, e1) ->
                       let uu___3 = elim_mlexpr env e1 in (s, uu___3)) fields in
            (syms, nm, uu___1) in
          FStarC_Extraction_ML_Syntax.MLE_Record uu___
      | FStarC_Extraction_ML_Syntax.MLE_Proj (e1, p) ->
          let uu___ = let uu___1 = elim_mlexpr env e1 in (uu___1, p) in
          FStarC_Extraction_ML_Syntax.MLE_Proj uu___
      | FStarC_Extraction_ML_Syntax.MLE_If (e1, e11, e2_opt) ->
          let uu___ =
            let uu___1 = elim_mlexpr env e1 in
            let uu___2 = elim_mlexpr env e11 in
            let uu___3 =
              FStarC_Compiler_Util.map_opt e2_opt (elim_mlexpr env) in
            (uu___1, uu___2, uu___3) in
          FStarC_Extraction_ML_Syntax.MLE_If uu___
      | FStarC_Extraction_ML_Syntax.MLE_Raise (p, es) ->
          let uu___ =
            let uu___1 = FStarC_Compiler_List.map (elim_mlexpr env) es in
            (p, uu___1) in
          FStarC_Extraction_ML_Syntax.MLE_Raise uu___
      | FStarC_Extraction_ML_Syntax.MLE_Try (e1, branches) ->
          let uu___ =
            let uu___1 = elim_mlexpr env e1 in
            let uu___2 = FStarC_Compiler_List.map (elim_branch env) branches in
            (uu___1, uu___2) in
          FStarC_Extraction_ML_Syntax.MLE_Try uu___
and (elim_letbinding :
  env_t ->
    (FStarC_Extraction_ML_Syntax.mlletflavor *
      FStarC_Extraction_ML_Syntax.mllb Prims.list) ->
      (FStarC_Extraction_ML_Syntax.mlletflavor *
        FStarC_Extraction_ML_Syntax.mllb Prims.list))
  =
  fun env ->
    fun uu___ ->
      match uu___ with
      | (flavor, lbs) ->
          let elim_one_lb lb =
            let ts =
              FStarC_Compiler_Util.map_opt
                lb.FStarC_Extraction_ML_Syntax.mllb_tysc
                (fun uu___1 ->
                   match uu___1 with
                   | (vars, t) ->
                       let uu___2 = elim_mlty env t in (vars, uu___2)) in
            let expr =
              elim_mlexpr env lb.FStarC_Extraction_ML_Syntax.mllb_def in
            {
              FStarC_Extraction_ML_Syntax.mllb_name =
                (lb.FStarC_Extraction_ML_Syntax.mllb_name);
              FStarC_Extraction_ML_Syntax.mllb_tysc = ts;
              FStarC_Extraction_ML_Syntax.mllb_add_unit =
                (lb.FStarC_Extraction_ML_Syntax.mllb_add_unit);
              FStarC_Extraction_ML_Syntax.mllb_def = expr;
              FStarC_Extraction_ML_Syntax.mllb_attrs =
                (lb.FStarC_Extraction_ML_Syntax.mllb_attrs);
              FStarC_Extraction_ML_Syntax.mllb_meta =
                (lb.FStarC_Extraction_ML_Syntax.mllb_meta);
              FStarC_Extraction_ML_Syntax.print_typ =
                (lb.FStarC_Extraction_ML_Syntax.print_typ)
            } in
          let uu___1 = FStarC_Compiler_List.map elim_one_lb lbs in
          (flavor, uu___1)
and (elim_branch :
  env_t ->
    (FStarC_Extraction_ML_Syntax.mlpattern *
      FStarC_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option *
      FStarC_Extraction_ML_Syntax.mlexpr) ->
      (FStarC_Extraction_ML_Syntax.mlpattern *
        FStarC_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option *
        FStarC_Extraction_ML_Syntax.mlexpr))
  =
  fun env ->
    fun uu___ ->
      match uu___ with
      | (pat, wopt, e) ->
          let uu___1 = FStarC_Compiler_Util.map_opt wopt (elim_mlexpr env) in
          let uu___2 = elim_mlexpr env e in (pat, uu___1, uu___2)
and (elim_mlexpr :
  env_t ->
    FStarC_Extraction_ML_Syntax.mlexpr -> FStarC_Extraction_ML_Syntax.mlexpr)
  =
  fun env ->
    fun e ->
      let uu___ = elim_mlexpr' env e.FStarC_Extraction_ML_Syntax.expr in
      let uu___1 = elim_mlty env e.FStarC_Extraction_ML_Syntax.mlty in
      {
        FStarC_Extraction_ML_Syntax.expr = uu___;
        FStarC_Extraction_ML_Syntax.mlty = uu___1;
        FStarC_Extraction_ML_Syntax.loc = (e.FStarC_Extraction_ML_Syntax.loc)
      }
exception Drop_tydef 
let (uu___is_Drop_tydef : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Drop_tydef -> true | uu___ -> false
let (elim_tydef :
  env_t ->
    Prims.string ->
      FStarC_Extraction_ML_Syntax.meta Prims.list ->
        FStarC_Extraction_ML_Syntax.ty_param Prims.list ->
          FStarC_Extraction_ML_Syntax.mlty ->
            (env_t * (Prims.string * FStarC_Extraction_ML_Syntax.meta
              Prims.list * FStarC_Extraction_ML_Syntax.ty_param Prims.list *
              FStarC_Extraction_ML_Syntax.mlty)))
  =
  fun env ->
    fun name ->
      fun metadata ->
        fun parameters ->
          fun mlty ->
            let val_decl_range =
              FStarC_Compiler_Util.find_map metadata
                (fun uu___ ->
                   match uu___ with
                   | FStarC_Extraction_ML_Syntax.HasValDecl r ->
                       FStar_Pervasives_Native.Some r
                   | uu___1 -> FStar_Pervasives_Native.None) in
            let remove_typars_list =
              FStarC_Compiler_Util.try_find
                (fun uu___ ->
                   match uu___ with
                   | FStarC_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                       uu___1 -> true
                   | uu___1 -> false) metadata in
            let range_of_tydef =
              match remove_typars_list with
              | FStar_Pervasives_Native.None ->
                  FStarC_Compiler_Range_Type.dummyRange
              | FStar_Pervasives_Native.Some
                  (FStarC_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                  (uu___, r)) -> r in
            let must_eliminate i =
              match remove_typars_list with
              | FStar_Pervasives_Native.Some
                  (FStarC_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                  (l, r)) -> FStarC_Compiler_List.contains i l
              | uu___ -> false in
            let can_eliminate i =
              match (val_decl_range, remove_typars_list) with
              | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
                  -> true
              | uu___ -> false in
            let mlty1 = elim_mlty env mlty in
            let freevars = freevars_of_mlty mlty1 in
            let uu___ =
              FStarC_Compiler_List.fold_left
                (fun uu___1 ->
                   fun param ->
                     match uu___1 with
                     | (i, params, entry1) ->
                         let p =
                           param.FStarC_Extraction_ML_Syntax.ty_param_name in
                         let uu___2 =
                           FStarC_Class_Setlike.mem ()
                             (Obj.magic
                                (FStarC_Compiler_RBSet.setlike_rbset
                                   FStarC_Class_Ord.ord_string)) p
                             (Obj.magic freevars) in
                         if uu___2
                         then
                           (if must_eliminate i
                            then
                              (let uu___4 =
                                 FStarC_Compiler_Util.format2
                                   "Expected parameter %s of %s to be unused in its definition and eliminated"
                                   p name in
                               FStarC_Errors.log_issue
                                 FStarC_Class_HasRange.hasRange_range
                                 range_of_tydef
                                 FStarC_Errors_Codes.Error_RemoveUnusedTypeParameter
                                 ()
                                 (Obj.magic
                                    FStarC_Errors_Msg.is_error_message_string)
                                 (Obj.magic uu___4))
                            else ();
                            ((i + Prims.int_one), (param :: params), (Retain
                              :: entry1)))
                         else
                           if (can_eliminate i) || (must_eliminate i)
                           then
                             ((i + Prims.int_one), params, (Omit :: entry1))
                           else
                             (let uu___5 =
                                let uu___6 = FStarC_Options.codegen () in
                                uu___6 =
                                  (FStar_Pervasives_Native.Some
                                     FStarC_Options.FSharp) in
                              if uu___5
                              then
                                let range =
                                  match val_decl_range with
                                  | FStar_Pervasives_Native.Some r -> r
                                  | uu___6 -> range_of_tydef in
                                ((let uu___7 =
                                    let uu___8 =
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_int i in
                                    let uu___9 =
                                      FStarC_Class_Show.show
                                        FStarC_Class_Show.showable_int i in
                                    FStarC_Compiler_Util.format3
                                      "Parameter %s of %s is unused and must be eliminated for F#; add `[@@ remove_unused_type_parameters [%s; ...]]` to the interface signature; \nThis type definition is being dropped"
                                      uu___8 name uu___9 in
                                  FStarC_Errors.log_issue
                                    FStarC_Class_HasRange.hasRange_range
                                    range
                                    FStarC_Errors_Codes.Error_RemoveUnusedTypeParameter
                                    ()
                                    (Obj.magic
                                       FStarC_Errors_Msg.is_error_message_string)
                                    (Obj.magic uu___7));
                                 FStarC_Compiler_Effect.raise Drop_tydef)
                              else
                                ((i + Prims.int_one), (param :: params),
                                  (Retain :: entry1))))
                (Prims.int_zero, [], []) parameters in
            match uu___ with
            | (uu___1, parameters1, entry1) ->
                let uu___2 =
                  extend_env env name (FStarC_Compiler_List.rev entry1) in
                (uu___2,
                  (name, metadata, (FStarC_Compiler_List.rev parameters1),
                    mlty1))
let (elim_tydef_or_decl : env_t -> tydef -> (env_t * tydef)) =
  fun env ->
    fun td ->
      match td with
      | (name, metadata, FStar_Pervasives.Inr arity) ->
          let remove_typars_list =
            FStarC_Compiler_Util.try_find
              (fun uu___ ->
                 match uu___ with
                 | FStarC_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                     uu___1 -> true
                 | uu___1 -> false) metadata in
          (match remove_typars_list with
           | FStar_Pervasives_Native.None -> (env, td)
           | FStar_Pervasives_Native.Some
               (FStarC_Extraction_ML_Syntax.RemoveUnusedTypeParameters
               (l, r)) ->
               let must_eliminate i = FStarC_Compiler_List.contains i l in
               let rec aux i =
                 if i = arity
                 then []
                 else
                   if must_eliminate i
                   then
                     (let uu___1 = aux (i + Prims.int_one) in Omit :: uu___1)
                   else
                     (let uu___2 = aux (i + Prims.int_one) in Retain ::
                        uu___2) in
               let entries = aux Prims.int_zero in
               let uu___ = extend_env env name entries in (uu___, td))
      | (name, metadata, FStar_Pervasives.Inl (parameters, mlty)) ->
          let uu___ = elim_tydef env name metadata parameters mlty in
          (match uu___ with
           | (env1, (name1, meta, params, mlty1)) ->
               (env1, (name1, meta, (FStar_Pervasives.Inl (params, mlty1)))))
let (elim_tydefs : env_t -> tydef Prims.list -> (env_t * tydef Prims.list)) =
  fun env ->
    fun tds ->
      let uu___ =
        let uu___1 = FStarC_Options.codegen () in
        uu___1 <> (FStar_Pervasives_Native.Some FStarC_Options.FSharp) in
      if uu___
      then (env, tds)
      else
        (let uu___2 =
           FStarC_Compiler_List.fold_left
             (fun uu___3 ->
                fun td ->
                  match uu___3 with
                  | (env1, out) ->
                      (try
                         (fun uu___4 ->
                            match () with
                            | () ->
                                let uu___5 = elim_tydef_or_decl env1 td in
                                (match uu___5 with
                                 | (env2, td1) -> (env2, (td1 :: out)))) ()
                       with | Drop_tydef -> (env1, out))) (env, []) tds in
         match uu___2 with
         | (env1, tds1) -> (env1, (FStarC_Compiler_List.rev tds1)))
let (elim_one_mltydecl :
  env_t ->
    FStarC_Extraction_ML_Syntax.one_mltydecl ->
      (env_t * FStarC_Extraction_ML_Syntax.one_mltydecl))
  =
  fun env ->
    fun td ->
      let uu___ = td in
      match uu___ with
      | { FStarC_Extraction_ML_Syntax.tydecl_assumed = uu___1;
          FStarC_Extraction_ML_Syntax.tydecl_name = name;
          FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___2;
          FStarC_Extraction_ML_Syntax.tydecl_parameters = parameters;
          FStarC_Extraction_ML_Syntax.tydecl_meta = meta;
          FStarC_Extraction_ML_Syntax.tydecl_defn = body;_} ->
          let elim_td td1 =
            match td1 with
            | FStarC_Extraction_ML_Syntax.MLTD_Abbrev mlty ->
                let uu___3 = elim_tydef env name meta parameters mlty in
                (match uu___3 with
                 | (env1, (name1, uu___4, parameters1, mlty1)) ->
                     (env1, parameters1,
                       (FStarC_Extraction_ML_Syntax.MLTD_Abbrev mlty1)))
            | FStarC_Extraction_ML_Syntax.MLTD_Record fields ->
                let uu___3 =
                  let uu___4 =
                    FStarC_Compiler_List.map
                      (fun uu___5 ->
                         match uu___5 with
                         | (name1, ty) ->
                             let uu___6 = elim_mlty env ty in (name1, uu___6))
                      fields in
                  FStarC_Extraction_ML_Syntax.MLTD_Record uu___4 in
                (env, parameters, uu___3)
            | FStarC_Extraction_ML_Syntax.MLTD_DType inductive ->
                let uu___3 =
                  let uu___4 =
                    FStarC_Compiler_List.map
                      (fun uu___5 ->
                         match uu___5 with
                         | (i, constrs) ->
                             let uu___6 =
                               FStarC_Compiler_List.map
                                 (fun uu___7 ->
                                    match uu___7 with
                                    | (constr, ty) ->
                                        let uu___8 = elim_mlty env ty in
                                        (constr, uu___8)) constrs in
                             (i, uu___6)) inductive in
                  FStarC_Extraction_ML_Syntax.MLTD_DType uu___4 in
                (env, parameters, uu___3) in
          let uu___3 =
            match body with
            | FStar_Pervasives_Native.None -> (env, parameters, body)
            | FStar_Pervasives_Native.Some td1 ->
                let uu___4 = elim_td td1 in
                (match uu___4 with
                 | (env1, parameters1, td2) ->
                     (env1, parameters1, (FStar_Pervasives_Native.Some td2))) in
          (match uu___3 with
           | (env1, parameters1, body1) ->
               (env1,
                 {
                   FStarC_Extraction_ML_Syntax.tydecl_assumed =
                     (td.FStarC_Extraction_ML_Syntax.tydecl_assumed);
                   FStarC_Extraction_ML_Syntax.tydecl_name =
                     (td.FStarC_Extraction_ML_Syntax.tydecl_name);
                   FStarC_Extraction_ML_Syntax.tydecl_ignored =
                     (td.FStarC_Extraction_ML_Syntax.tydecl_ignored);
                   FStarC_Extraction_ML_Syntax.tydecl_parameters =
                     parameters1;
                   FStarC_Extraction_ML_Syntax.tydecl_meta =
                     (td.FStarC_Extraction_ML_Syntax.tydecl_meta);
                   FStarC_Extraction_ML_Syntax.tydecl_defn = body1
                 }))
let (elim_module :
  env_t ->
    FStarC_Extraction_ML_Syntax.mlmodule1 Prims.list ->
      (env_t * FStarC_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env ->
    fun m ->
      let elim_module1 env1 m1 =
        match m1.FStarC_Extraction_ML_Syntax.mlmodule1_m with
        | FStarC_Extraction_ML_Syntax.MLM_Ty td ->
            let uu___ =
              FStarC_Compiler_Util.fold_map elim_one_mltydecl env1 td in
            (match uu___ with
             | (env2, td1) ->
                 (env2,
                   {
                     FStarC_Extraction_ML_Syntax.mlmodule1_m =
                       (FStarC_Extraction_ML_Syntax.MLM_Ty td1);
                     FStarC_Extraction_ML_Syntax.mlmodule1_attrs =
                       (m1.FStarC_Extraction_ML_Syntax.mlmodule1_attrs)
                   }))
        | FStarC_Extraction_ML_Syntax.MLM_Let lb ->
            let uu___ =
              let uu___1 =
                let uu___2 = elim_letbinding env1 lb in
                FStarC_Extraction_ML_Syntax.MLM_Let uu___2 in
              {
                FStarC_Extraction_ML_Syntax.mlmodule1_m = uu___1;
                FStarC_Extraction_ML_Syntax.mlmodule1_attrs =
                  (m1.FStarC_Extraction_ML_Syntax.mlmodule1_attrs)
              } in
            (env1, uu___)
        | FStarC_Extraction_ML_Syntax.MLM_Exn (name, sym_tys) ->
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    FStarC_Compiler_List.map
                      (fun uu___4 ->
                         match uu___4 with
                         | (s, t) ->
                             let uu___5 = elim_mlty env1 t in (s, uu___5))
                      sym_tys in
                  (name, uu___3) in
                FStarC_Extraction_ML_Syntax.MLM_Exn uu___2 in
              {
                FStarC_Extraction_ML_Syntax.mlmodule1_m = uu___1;
                FStarC_Extraction_ML_Syntax.mlmodule1_attrs =
                  (m1.FStarC_Extraction_ML_Syntax.mlmodule1_attrs)
              } in
            (env1, uu___)
        | FStarC_Extraction_ML_Syntax.MLM_Top e ->
            let uu___ =
              let uu___1 =
                let uu___2 = elim_mlexpr env1 e in
                FStarC_Extraction_ML_Syntax.MLM_Top uu___2 in
              {
                FStarC_Extraction_ML_Syntax.mlmodule1_m = uu___1;
                FStarC_Extraction_ML_Syntax.mlmodule1_attrs =
                  (m1.FStarC_Extraction_ML_Syntax.mlmodule1_attrs)
              } in
            (env1, uu___)
        | uu___ -> (env1, m1) in
      let uu___ =
        FStarC_Compiler_List.fold_left
          (fun uu___1 ->
             fun m1 ->
               match uu___1 with
               | (env1, out) ->
                   (try
                      (fun uu___2 ->
                         match () with
                         | () ->
                             let uu___3 = elim_module1 env1 m1 in
                             (match uu___3 with
                              | (env2, m2) -> (env2, (m2 :: out)))) ()
                    with | Drop_tydef -> (env1, out))) (env, []) m in
      match uu___ with | (env1, m1) -> (env1, (FStarC_Compiler_List.rev m1))
let (set_current_module :
  env_t -> FStarC_Extraction_ML_Syntax.mlpath -> env_t) =
  fun e ->
    fun n ->
      let curmod =
        FStarC_Compiler_List.op_At (FStar_Pervasives_Native.fst n)
          [FStar_Pervasives_Native.snd n] in
      { current_module = curmod; tydef_map = (e.tydef_map) }
let (elim_mllib :
  env_t ->
    FStarC_Extraction_ML_Syntax.mllib ->
      (env_t * FStarC_Extraction_ML_Syntax.mllib))
  =
  fun env ->
    fun m ->
      let uu___ =
        let uu___1 = FStarC_Options.codegen () in
        uu___1 <> (FStar_Pervasives_Native.Some FStarC_Options.FSharp) in
      if uu___
      then (env, m)
      else
        (let uu___2 = m in
         match uu___2 with
         | FStarC_Extraction_ML_Syntax.MLLib libs ->
             let elim_one_lib env1 lib =
               let uu___3 = lib in
               match uu___3 with
               | (name, sig_mod, _libs) ->
                   let env2 = set_current_module env1 name in
                   let uu___4 =
                     match sig_mod with
                     | FStar_Pervasives_Native.Some (sig_, mod_) ->
                         let uu___5 = elim_module env2 mod_ in
                         (match uu___5 with
                          | (env3, mod_1) ->
                              ((FStar_Pervasives_Native.Some (sig_, mod_1)),
                                env3))
                     | FStar_Pervasives_Native.None ->
                         (FStar_Pervasives_Native.None, env2) in
                   (match uu___4 with
                    | (sig_mod1, env3) -> (env3, (name, sig_mod1, _libs))) in
             let uu___3 = FStarC_Compiler_Util.fold_map elim_one_lib env libs in
             (match uu___3 with
              | (env1, libs1) ->
                  (env1, (FStarC_Extraction_ML_Syntax.MLLib libs1))))
let (elim_mllibs :
  FStarC_Extraction_ML_Syntax.mllib Prims.list ->
    FStarC_Extraction_ML_Syntax.mllib Prims.list)
  =
  fun l ->
    let uu___ = FStarC_Compiler_Util.fold_map elim_mllib initial_env l in
    FStar_Pervasives_Native.snd uu___