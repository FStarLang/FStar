open Prims
type argument_tag =
  | Retain 
  | Omit 
let (uu___is_Retain : argument_tag -> Prims.bool) =
  fun projectee -> match projectee with | Retain -> true | uu____7 -> false
let (uu___is_Omit : argument_tag -> Prims.bool) =
  fun projectee -> match projectee with | Omit -> true | uu____13 -> false
type entry = argument_tag Prims.list
type env_t =
  {
  current_module: FStar_Extraction_ML_Syntax.mlsymbol Prims.list ;
  tydef_map: entry FStar_Util.psmap }
let (__proj__Mkenv_t__item__current_module :
  env_t -> FStar_Extraction_ML_Syntax.mlsymbol Prims.list) =
  fun projectee ->
    match projectee with | { current_module; tydef_map;_} -> current_module
let (__proj__Mkenv_t__item__tydef_map : env_t -> entry FStar_Util.psmap) =
  fun projectee ->
    match projectee with | { current_module; tydef_map;_} -> tydef_map
let (initial_env : env_t) =
  let uu____60 = FStar_Util.psmap_empty () in
  { current_module = []; tydef_map = uu____60 }
let (extend_env :
  env_t -> FStar_Extraction_ML_Syntax.mlsymbol -> entry -> env_t) =
  fun env ->
    fun i ->
      fun e ->
        let uu___12_78 = env in
        let uu____79 =
          let uu____82 =
            FStar_Extraction_ML_Syntax.string_of_mlpath
              ((env.current_module), i) in
          FStar_Util.psmap_add env.tydef_map uu____82 e in
        { current_module = (uu___12_78.current_module); tydef_map = uu____79
        }
let (lookup_tyname :
  env_t ->
    FStar_Extraction_ML_Syntax.mlpath -> entry FStar_Pervasives_Native.option)
  =
  fun env ->
    fun name ->
      let uu____99 = FStar_Extraction_ML_Syntax.string_of_mlpath name in
      FStar_Util.psmap_try_find env.tydef_map uu____99
type var_set = FStar_Extraction_ML_Syntax.mlident FStar_Util.set
let (empty_var_set : Prims.string FStar_Util.set) =
  FStar_Util.new_set (fun x -> fun y -> FStar_String.compare x y)
let rec (freevars_of_mlty' :
  var_set -> FStar_Extraction_ML_Syntax.mlty -> var_set) =
  fun vars ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var i -> FStar_Util.set_add i vars
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____120, t1) ->
          let uu____122 = freevars_of_mlty' vars t0 in
          freevars_of_mlty' uu____122 t1
      | FStar_Extraction_ML_Syntax.MLTY_Named (tys, uu____124) ->
          FStar_List.fold_left freevars_of_mlty' vars tys
      | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
          FStar_List.fold_left freevars_of_mlty' vars tys
      | uu____132 -> vars
let (freevars_of_mlty : FStar_Extraction_ML_Syntax.mlty -> var_set) =
  freevars_of_mlty' empty_var_set
let rec (elim_mlty :
  env_t -> FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun env ->
    fun mlty ->
      match mlty with
      | FStar_Extraction_ML_Syntax.MLTY_Var uu____147 -> mlty
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t0, e, t1) ->
          let uu____151 =
            let uu____158 = elim_mlty env t0 in
            let uu____159 = elim_mlty env t1 in (uu____158, e, uu____159) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____151
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, name) ->
          let args1 = FStar_List.map (elim_mlty env) args in
          let uu____169 = lookup_tyname env name in
          (match uu____169 with
           | FStar_Pervasives_Native.None ->
               FStar_Extraction_ML_Syntax.MLTY_Named (args1, name)
           | FStar_Pervasives_Native.Some entry1 ->
               (if (FStar_List.length entry1) <> (FStar_List.length args1)
                then
                  failwith
                    "Impossible: arity mismatch between definition and use"
                else ();
                (let args2 =
                   FStar_List.fold_right2
                     (fun arg ->
                        fun tag ->
                          fun out ->
                            match tag with
                            | Retain -> arg :: out
                            | uu____192 -> out) args1 entry1 [] in
                 FStar_Extraction_ML_Syntax.MLTY_Named (args2, name))))
      | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
          let uu____198 = FStar_List.map (elim_mlty env) tys in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____198
      | FStar_Extraction_ML_Syntax.MLTY_Top -> mlty
      | FStar_Extraction_ML_Syntax.MLTY_Erased -> mlty
let rec (elim_mlexpr' :
  env_t ->
    FStar_Extraction_ML_Syntax.mlexpr' -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun env ->
    fun e ->
      match e with
      | FStar_Extraction_ML_Syntax.MLE_Const uu____263 -> e
      | FStar_Extraction_ML_Syntax.MLE_Var uu____264 -> e
      | FStar_Extraction_ML_Syntax.MLE_Name uu____265 -> e
      | FStar_Extraction_ML_Syntax.MLE_Let (lb, e1) ->
          let uu____280 =
            let uu____291 = elim_letbinding env lb in
            let uu____298 = elim_mlexpr env e1 in (uu____291, uu____298) in
          FStar_Extraction_ML_Syntax.MLE_Let uu____280
      | FStar_Extraction_ML_Syntax.MLE_App (e1, es) ->
          let uu____311 =
            let uu____318 = elim_mlexpr env e1 in
            let uu____319 = FStar_List.map (elim_mlexpr env) es in
            (uu____318, uu____319) in
          FStar_Extraction_ML_Syntax.MLE_App uu____311
      | FStar_Extraction_ML_Syntax.MLE_TApp (e1, tys) ->
          let uu____330 =
            let uu____337 = FStar_List.map (elim_mlty env) tys in
            (e1, uu____337) in
          FStar_Extraction_ML_Syntax.MLE_TApp uu____330
      | FStar_Extraction_ML_Syntax.MLE_Fun (bvs, e1) ->
          let uu____356 =
            let uu____367 =
              FStar_List.map
                (fun uu____386 ->
                   match uu____386 with
                   | (x, t) ->
                       let uu____397 = elim_mlty env t in (x, uu____397)) bvs in
            let uu____398 = elim_mlexpr env e1 in (uu____367, uu____398) in
          FStar_Extraction_ML_Syntax.MLE_Fun uu____356
      | FStar_Extraction_ML_Syntax.MLE_Match (e1, branches) ->
          let uu____427 =
            let uu____442 = elim_mlexpr env e1 in
            let uu____443 = FStar_List.map (elim_branch env) branches in
            (uu____442, uu____443) in
          FStar_Extraction_ML_Syntax.MLE_Match uu____427
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t0, t1) ->
          let uu____483 =
            let uu____490 = elim_mlexpr env e1 in
            let uu____491 = elim_mlty env t0 in
            let uu____492 = elim_mlty env t1 in
            (uu____490, uu____491, uu____492) in
          FStar_Extraction_ML_Syntax.MLE_Coerce uu____483
      | FStar_Extraction_ML_Syntax.MLE_CTor (l, es) ->
          let uu____499 =
            let uu____506 = FStar_List.map (elim_mlexpr env) es in
            (l, uu____506) in
          FStar_Extraction_ML_Syntax.MLE_CTor uu____499
      | FStar_Extraction_ML_Syntax.MLE_Seq es ->
          let uu____514 = FStar_List.map (elim_mlexpr env) es in
          FStar_Extraction_ML_Syntax.MLE_Seq uu____514
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____520 = FStar_List.map (elim_mlexpr env) es in
          FStar_Extraction_ML_Syntax.MLE_Tuple uu____520
      | FStar_Extraction_ML_Syntax.MLE_Record (syms, fields) ->
          let uu____541 =
            let uu____554 =
              FStar_List.map
                (fun uu____573 ->
                   match uu____573 with
                   | (s, e1) ->
                       let uu____584 = elim_mlexpr env e1 in (s, uu____584))
                fields in
            (syms, uu____554) in
          FStar_Extraction_ML_Syntax.MLE_Record uu____541
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1, p) ->
          let uu____595 =
            let uu____600 = elim_mlexpr env e1 in (uu____600, p) in
          FStar_Extraction_ML_Syntax.MLE_Proj uu____595
      | FStar_Extraction_ML_Syntax.MLE_If (e1, e11, e2_opt) ->
          let uu____608 =
            let uu____617 = elim_mlexpr env e1 in
            let uu____618 = elim_mlexpr env e11 in
            let uu____619 = FStar_Util.map_opt e2_opt (elim_mlexpr env) in
            (uu____617, uu____618, uu____619) in
          FStar_Extraction_ML_Syntax.MLE_If uu____608
      | FStar_Extraction_ML_Syntax.MLE_Raise (p, es) ->
          let uu____630 =
            let uu____637 = FStar_List.map (elim_mlexpr env) es in
            (p, uu____637) in
          FStar_Extraction_ML_Syntax.MLE_Raise uu____630
      | FStar_Extraction_ML_Syntax.MLE_Try (e1, branches) ->
          let uu____664 =
            let uu____679 = elim_mlexpr env e1 in
            let uu____680 = FStar_List.map (elim_branch env) branches in
            (uu____679, uu____680) in
          FStar_Extraction_ML_Syntax.MLE_Try uu____664
and (elim_letbinding :
  env_t ->
    (FStar_Extraction_ML_Syntax.mlletflavor * FStar_Extraction_ML_Syntax.mllb
      Prims.list) ->
      (FStar_Extraction_ML_Syntax.mlletflavor *
        FStar_Extraction_ML_Syntax.mllb Prims.list))
  =
  fun env ->
    fun uu____718 ->
      match uu____718 with
      | (flavor, lbs) ->
          let elim_one_lb lb =
            let ts =
              FStar_Util.map_opt lb.FStar_Extraction_ML_Syntax.mllb_tysc
                (fun uu____758 ->
                   match uu____758 with
                   | (vars, t) ->
                       let uu____765 = elim_mlty env t in (vars, uu____765)) in
            let expr = elim_mlexpr env lb.FStar_Extraction_ML_Syntax.mllb_def in
            let uu___141_767 = lb in
            {
              FStar_Extraction_ML_Syntax.mllb_name =
                (uu___141_767.FStar_Extraction_ML_Syntax.mllb_name);
              FStar_Extraction_ML_Syntax.mllb_tysc = ts;
              FStar_Extraction_ML_Syntax.mllb_add_unit =
                (uu___141_767.FStar_Extraction_ML_Syntax.mllb_add_unit);
              FStar_Extraction_ML_Syntax.mllb_def = expr;
              FStar_Extraction_ML_Syntax.mllb_meta =
                (uu___141_767.FStar_Extraction_ML_Syntax.mllb_meta);
              FStar_Extraction_ML_Syntax.print_typ =
                (uu___141_767.FStar_Extraction_ML_Syntax.print_typ)
            } in
          let uu____768 = FStar_List.map elim_one_lb lbs in
          (flavor, uu____768)
and (elim_branch :
  env_t ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) ->
      (FStar_Extraction_ML_Syntax.mlpattern *
        FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option *
        FStar_Extraction_ML_Syntax.mlexpr))
  =
  fun env ->
    fun uu____774 ->
      match uu____774 with
      | (pat, wopt, e) ->
          let uu____798 = FStar_Util.map_opt wopt (elim_mlexpr env) in
          let uu____801 = elim_mlexpr env e in (pat, uu____798, uu____801)
and (elim_mlexpr :
  env_t ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun env ->
    fun e ->
      let uu___150_806 = e in
      let uu____807 = elim_mlexpr' env e.FStar_Extraction_ML_Syntax.expr in
      let uu____808 = elim_mlty env e.FStar_Extraction_ML_Syntax.mlty in
      {
        FStar_Extraction_ML_Syntax.expr = uu____807;
        FStar_Extraction_ML_Syntax.mlty = uu____808;
        FStar_Extraction_ML_Syntax.loc =
          (uu___150_806.FStar_Extraction_ML_Syntax.loc)
      }
type tydef =
  (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.metadata
    * (FStar_Extraction_ML_Syntax.mltyscheme, Prims.int) FStar_Util.either)
let (elim_tydef :
  env_t ->
    Prims.string ->
      FStar_Extraction_ML_Syntax.meta Prims.list ->
        Prims.string Prims.list ->
          FStar_Extraction_ML_Syntax.mlty ->
            (env_t * (Prims.string * FStar_Extraction_ML_Syntax.meta
              Prims.list * Prims.string Prims.list *
              FStar_Extraction_ML_Syntax.mlty)))
  =
  fun env ->
    fun name ->
      fun metadata ->
        fun parameters ->
          fun mlty ->
            let val_decl_range =
              FStar_Util.find_map metadata
                (fun uu___0_873 ->
                   match uu___0_873 with
                   | FStar_Extraction_ML_Syntax.HasValDecl r ->
                       FStar_Pervasives_Native.Some r
                   | uu____877 -> FStar_Pervasives_Native.None) in
            let remove_typars_list =
              FStar_Util.try_find
                (fun uu___1_883 ->
                   match uu___1_883 with
                   | FStar_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                       uu____884 -> true
                   | uu____891 -> false) metadata in
            let range_of_tydef =
              match remove_typars_list with
              | FStar_Pervasives_Native.None -> FStar_Range.dummyRange
              | FStar_Pervasives_Native.Some
                  (FStar_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                  (uu____893, r)) -> r in
            let must_eliminate i =
              match remove_typars_list with
              | FStar_Pervasives_Native.Some
                  (FStar_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                  (l, r)) -> FStar_List.contains i l
              | uu____911 -> false in
            let can_eliminate i =
              match (val_decl_range, remove_typars_list) with
              | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
                  -> true
              | uu____928 -> false in
            let mlty1 = elim_mlty env mlty in
            let freevars = freevars_of_mlty mlty1 in
            let uu____939 =
              FStar_List.fold_left
                (fun uu____967 ->
                   fun p ->
                     match uu____967 with
                     | (i, params, entry1) ->
                         let uu____1000 = FStar_Util.set_mem p freevars in
                         if uu____1000
                         then
                           (if must_eliminate i
                            then
                              (let uu____1012 =
                                 let uu____1017 =
                                   FStar_Util.format2
                                     "Expected parameter %s of %s to be unused in its definition and eliminated"
                                     p name in
                                 (FStar_Errors.Error_RemoveUnusedTypeParameter,
                                   uu____1017) in
                               FStar_Errors.raise_error uu____1012
                                 range_of_tydef)
                            else ();
                            ((i + Prims.int_one), (p :: params), (Retain ::
                              entry1)))
                         else
                           if (can_eliminate i) || (must_eliminate i)
                           then
                             ((i + Prims.int_one), params, (Omit :: entry1))
                           else
                             (let uu____1039 =
                                let uu____1040 = FStar_Options.codegen () in
                                uu____1040 =
                                  (FStar_Pervasives_Native.Some
                                     FStar_Options.FSharp) in
                              if uu____1039
                              then
                                let range =
                                  match val_decl_range with
                                  | FStar_Pervasives_Native.Some r -> r
                                  | uu____1057 -> range_of_tydef in
                                let uu____1060 =
                                  let uu____1065 =
                                    let uu____1066 =
                                      FStar_Util.string_of_int i in
                                    let uu____1067 =
                                      FStar_Util.string_of_int i in
                                    FStar_Util.format3
                                      "Parameter %s of %s is unused and must be eliminated for F#; add `[@@ remove_unused_type_parameters [%s; ...]]` to the interface signature"
                                      uu____1066 name uu____1067 in
                                  (FStar_Errors.Error_RemoveUnusedTypeParameter,
                                    uu____1065) in
                                FStar_Errors.raise_error uu____1060 range
                              else
                                ((i + Prims.int_one), (p :: params), (Retain
                                  :: entry1)))) (Prims.int_zero, [], [])
                parameters in
            match uu____939 with
            | (uu____1103, parameters1, entry1) ->
                let uu____1114 = extend_env env name (FStar_List.rev entry1) in
                (uu____1114,
                  (name, metadata, (FStar_List.rev parameters1), mlty1))
let (elim_tydef_or_decl : env_t -> tydef -> (env_t * tydef)) =
  fun env ->
    fun td ->
      match td with
      | (name, metadata, FStar_Util.Inr arity) ->
          let remove_typars_list =
            FStar_Util.try_find
              (fun uu___2_1161 ->
                 match uu___2_1161 with
                 | FStar_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                     uu____1162 -> true
                 | uu____1169 -> false) metadata in
          (match remove_typars_list with
           | FStar_Pervasives_Native.None -> (env, td)
           | FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.RemoveUnusedTypeParameters 
               (l, r)) ->
               let must_eliminate i = FStar_List.contains i l in
               let rec aux i =
                 if i = arity
                 then []
                 else
                   if must_eliminate i
                   then
                     (let uu____1199 = aux (i + Prims.int_one) in Omit ::
                        uu____1199)
                   else
                     (let uu____1203 = aux (i + Prims.int_one) in Retain ::
                        uu____1203) in
               let entries = aux Prims.int_zero in
               let uu____1209 = extend_env env name entries in
               (uu____1209, td))
      | (name, metadata, FStar_Util.Inl (parameters, mlty)) ->
          let uu____1218 = elim_tydef env name metadata parameters mlty in
          (match uu____1218 with
           | (env1, (name1, meta, params, mlty1)) ->
               (env1, (name1, meta, (FStar_Util.Inl (params, mlty1)))))
let (elim_tydefs : env_t -> tydef Prims.list -> (env_t * tydef Prims.list)) =
  fun env -> fun tds -> FStar_Util.fold_map elim_tydef_or_decl env tds
let (elim_one_mltydecl :
  env_t ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      (env_t * FStar_Extraction_ML_Syntax.one_mltydecl))
  =
  fun env ->
    fun td ->
      let uu____1312 = td in
      match uu____1312 with
      | { FStar_Extraction_ML_Syntax.tydecl_assumed = uu____1317;
          FStar_Extraction_ML_Syntax.tydecl_name = name;
          FStar_Extraction_ML_Syntax.tydecl_ignored = uu____1319;
          FStar_Extraction_ML_Syntax.tydecl_parameters = parameters;
          FStar_Extraction_ML_Syntax.tydecl_meta = meta;
          FStar_Extraction_ML_Syntax.tydecl_defn = body;_} ->
          let elim_td td1 =
            match td1 with
            | FStar_Extraction_ML_Syntax.MLTD_Abbrev mlty ->
                let uu____1350 = elim_tydef env name meta parameters mlty in
                (match uu____1350 with
                 | (env1, (name1, uu____1377, parameters1, mlty1)) ->
                     (env1, parameters1,
                       (FStar_Extraction_ML_Syntax.MLTD_Abbrev mlty1)))
            | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                let uu____1409 =
                  let uu____1410 =
                    FStar_List.map
                      (fun uu____1429 ->
                         match uu____1429 with
                         | (name1, ty) ->
                             let uu____1440 = elim_mlty env ty in
                             (name1, uu____1440)) fields in
                  FStar_Extraction_ML_Syntax.MLTD_Record uu____1410 in
                (env, parameters, uu____1409)
            | FStar_Extraction_ML_Syntax.MLTD_DType inductive ->
                let uu____1456 =
                  let uu____1457 =
                    FStar_List.map
                      (fun uu____1494 ->
                         match uu____1494 with
                         | (i, constrs) ->
                             let uu____1529 =
                               FStar_List.map
                                 (fun uu____1548 ->
                                    match uu____1548 with
                                    | (constr, ty) ->
                                        let uu____1559 = elim_mlty env ty in
                                        (constr, uu____1559)) constrs in
                             (i, uu____1529)) inductive in
                  FStar_Extraction_ML_Syntax.MLTD_DType uu____1457 in
                (env, parameters, uu____1456) in
          let uu____1568 =
            match body with
            | FStar_Pervasives_Native.None -> (env, parameters, body)
            | FStar_Pervasives_Native.Some td1 ->
                let uu____1588 = elim_td td1 in
                (match uu____1588 with
                 | (env1, parameters1, td2) ->
                     (env1, parameters1, (FStar_Pervasives_Native.Some td2))) in
          (match uu____1568 with
           | (env1, parameters1, body1) ->
               (env1,
                 (let uu___295_1626 = td in
                  {
                    FStar_Extraction_ML_Syntax.tydecl_assumed =
                      (uu___295_1626.FStar_Extraction_ML_Syntax.tydecl_assumed);
                    FStar_Extraction_ML_Syntax.tydecl_name =
                      (uu___295_1626.FStar_Extraction_ML_Syntax.tydecl_name);
                    FStar_Extraction_ML_Syntax.tydecl_ignored =
                      (uu___295_1626.FStar_Extraction_ML_Syntax.tydecl_ignored);
                    FStar_Extraction_ML_Syntax.tydecl_parameters =
                      parameters1;
                    FStar_Extraction_ML_Syntax.tydecl_meta =
                      (uu___295_1626.FStar_Extraction_ML_Syntax.tydecl_meta);
                    FStar_Extraction_ML_Syntax.tydecl_defn = body1
                  })))
let (elim_module :
  env_t ->
    FStar_Extraction_ML_Syntax.mlmodule1 Prims.list ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env ->
    fun m ->
      let elim_module1 env1 m1 =
        match m1 with
        | FStar_Extraction_ML_Syntax.MLM_Ty td ->
            let uu____1667 = FStar_Util.fold_map elim_one_mltydecl env1 td in
            (match uu____1667 with
             | (env2, td1) -> (env2, (FStar_Extraction_ML_Syntax.MLM_Ty td1)))
        | FStar_Extraction_ML_Syntax.MLM_Let lb ->
            let uu____1685 =
              let uu____1686 = elim_letbinding env1 lb in
              FStar_Extraction_ML_Syntax.MLM_Let uu____1686 in
            (env1, uu____1685)
        | FStar_Extraction_ML_Syntax.MLM_Exn (name, sym_tys) ->
            let uu____1701 =
              let uu____1702 =
                let uu____1713 =
                  FStar_List.map
                    (fun uu____1732 ->
                       match uu____1732 with
                       | (s, t) ->
                           let uu____1743 = elim_mlty env1 t in
                           (s, uu____1743)) sym_tys in
                (name, uu____1713) in
              FStar_Extraction_ML_Syntax.MLM_Exn uu____1702 in
            (env1, uu____1701)
        | FStar_Extraction_ML_Syntax.MLM_Top e ->
            let uu____1751 =
              let uu____1752 = elim_mlexpr env1 e in
              FStar_Extraction_ML_Syntax.MLM_Top uu____1752 in
            (env1, uu____1751)
        | uu____1753 -> (env1, m1) in
      FStar_Util.fold_map elim_module1 env m
let (set_current_module :
  env_t -> FStar_Extraction_ML_Syntax.mlpath -> env_t) =
  fun e ->
    fun n ->
      let curmod =
        FStar_List.append (FStar_Pervasives_Native.fst n)
          [FStar_Pervasives_Native.snd n] in
      let uu___324_1771 = e in
      { current_module = curmod; tydef_map = (uu___324_1771.tydef_map) }
let (elim_mllib :
  env_t ->
    FStar_Extraction_ML_Syntax.mllib ->
      (env_t * FStar_Extraction_ML_Syntax.mllib))
  =
  fun env ->
    fun m ->
      let uu____1786 = m in
      match uu____1786 with
      | FStar_Extraction_ML_Syntax.MLLib libs ->
          let elim_one_lib env1 lib =
            let uu____1863 = lib in
            match uu____1863 with
            | (name, sig_mod, _libs) ->
                let env2 = set_current_module env1 name in
                let uu____1916 =
                  match sig_mod with
                  | FStar_Pervasives_Native.Some (sig_, mod_) ->
                      let uu____1953 = elim_module env2 mod_ in
                      (match uu____1953 with
                       | (env3, mod_1) ->
                           ((FStar_Pervasives_Native.Some (sig_, mod_1)),
                             env3))
                  | FStar_Pervasives_Native.None ->
                      (FStar_Pervasives_Native.None, env2) in
                (match uu____1916 with
                 | (sig_mod1, env3) -> (env3, (name, sig_mod1, _libs))) in
          let uu____2072 = FStar_Util.fold_map elim_one_lib env libs in
          (match uu____2072 with
           | (env1, libs1) ->
               (env1, (FStar_Extraction_ML_Syntax.MLLib libs1)))
let (elim_mllibs :
  FStar_Extraction_ML_Syntax.mllib Prims.list ->
    FStar_Extraction_ML_Syntax.mllib Prims.list)
  =
  fun l ->
    let uu____2170 = FStar_Util.fold_map elim_mllib initial_env l in
    FStar_Pervasives_Native.snd uu____2170