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
exception Drop_tydef 
let (uu___is_Drop_tydef : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Drop_tydef -> true | uu____824 -> false
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
                (fun uu___0_879 ->
                   match uu___0_879 with
                   | FStar_Extraction_ML_Syntax.HasValDecl r ->
                       FStar_Pervasives_Native.Some r
                   | uu____883 -> FStar_Pervasives_Native.None) in
            let remove_typars_list =
              FStar_Util.try_find
                (fun uu___1_889 ->
                   match uu___1_889 with
                   | FStar_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                       uu____890 -> true
                   | uu____897 -> false) metadata in
            let range_of_tydef =
              match remove_typars_list with
              | FStar_Pervasives_Native.None -> FStar_Range.dummyRange
              | FStar_Pervasives_Native.Some
                  (FStar_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                  (uu____899, r)) -> r in
            let must_eliminate i =
              match remove_typars_list with
              | FStar_Pervasives_Native.Some
                  (FStar_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                  (l, r)) -> FStar_List.contains i l
              | uu____917 -> false in
            let can_eliminate i =
              match (val_decl_range, remove_typars_list) with
              | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
                  -> true
              | uu____934 -> false in
            let mlty1 = elim_mlty env mlty in
            let freevars = freevars_of_mlty mlty1 in
            let uu____945 =
              FStar_List.fold_left
                (fun uu____973 ->
                   fun p ->
                     match uu____973 with
                     | (i, params, entry1) ->
                         let uu____1006 = FStar_Util.set_mem p freevars in
                         if uu____1006
                         then
                           (if must_eliminate i
                            then
                              (let uu____1018 =
                                 let uu____1023 =
                                   FStar_Util.format2
                                     "Expected parameter %s of %s to be unused in its definition and eliminated"
                                     p name in
                                 (FStar_Errors.Error_RemoveUnusedTypeParameter,
                                   uu____1023) in
                               FStar_Errors.log_issue range_of_tydef
                                 uu____1018)
                            else ();
                            ((i + Prims.int_one), (p :: params), (Retain ::
                              entry1)))
                         else
                           if (can_eliminate i) || (must_eliminate i)
                           then
                             ((i + Prims.int_one), params, (Omit :: entry1))
                           else
                             (let uu____1045 =
                                let uu____1046 = FStar_Options.codegen () in
                                uu____1046 =
                                  (FStar_Pervasives_Native.Some
                                     FStar_Options.FSharp) in
                              if uu____1045
                              then
                                let range =
                                  match val_decl_range with
                                  | FStar_Pervasives_Native.Some r -> r
                                  | uu____1063 -> range_of_tydef in
                                ((let uu____1067 =
                                    let uu____1072 =
                                      let uu____1073 =
                                        FStar_Util.string_of_int i in
                                      let uu____1074 =
                                        FStar_Util.string_of_int i in
                                      FStar_Util.format3
                                        "Parameter %s of %s is unused and must be eliminated for F#; add `[@@ remove_unused_type_parameters [%s; ...]]` to the interface signature; \nThis type definition is being dropped"
                                        uu____1073 name uu____1074 in
                                    (FStar_Errors.Error_RemoveUnusedTypeParameter,
                                      uu____1072) in
                                  FStar_Errors.log_issue range uu____1067);
                                 FStar_Exn.raise Drop_tydef)
                              else
                                ((i + Prims.int_one), (p :: params), (Retain
                                  :: entry1)))) (Prims.int_zero, [], [])
                parameters in
            match uu____945 with
            | (uu____1110, parameters1, entry1) ->
                let uu____1121 = extend_env env name (FStar_List.rev entry1) in
                (uu____1121,
                  (name, metadata, (FStar_List.rev parameters1), mlty1))
let (elim_tydef_or_decl : env_t -> tydef -> (env_t * tydef)) =
  fun env ->
    fun td ->
      match td with
      | (name, metadata, FStar_Util.Inr arity) ->
          let remove_typars_list =
            FStar_Util.try_find
              (fun uu___2_1168 ->
                 match uu___2_1168 with
                 | FStar_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                     uu____1169 -> true
                 | uu____1176 -> false) metadata in
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
                     (let uu____1206 = aux (i + Prims.int_one) in Omit ::
                        uu____1206)
                   else
                     (let uu____1210 = aux (i + Prims.int_one) in Retain ::
                        uu____1210) in
               let entries = aux Prims.int_zero in
               let uu____1216 = extend_env env name entries in
               (uu____1216, td))
      | (name, metadata, FStar_Util.Inl (parameters, mlty)) ->
          let uu____1225 = elim_tydef env name metadata parameters mlty in
          (match uu____1225 with
           | (env1, (name1, meta, params, mlty1)) ->
               (env1, (name1, meta, (FStar_Util.Inl (params, mlty1)))))
let (elim_tydefs : env_t -> tydef Prims.list -> (env_t * tydef Prims.list)) =
  fun env ->
    fun tds ->
      let uu____1301 =
        let uu____1302 = FStar_Options.codegen () in
        uu____1302 <> (FStar_Pervasives_Native.Some FStar_Options.FSharp) in
      if uu____1301
      then (env, tds)
      else
        (let uu____1316 =
           FStar_List.fold_left
             (fun uu____1333 ->
                fun td ->
                  match uu____1333 with
                  | (env1, out) ->
                      (try
                         (fun uu___258_1363 ->
                            match () with
                            | () ->
                                let uu____1370 = elim_tydef_or_decl env1 td in
                                (match uu____1370 with
                                 | (env2, td1) -> (env2, (td1 :: out)))) ()
                       with | Drop_tydef -> (env1, out))) (env, []) tds in
         match uu____1316 with
         | (env1, tds1) -> (env1, (FStar_List.rev tds1)))
let (elim_one_mltydecl :
  env_t ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      (env_t * FStar_Extraction_ML_Syntax.one_mltydecl))
  =
  fun env ->
    fun td ->
      let uu____1429 = td in
      match uu____1429 with
      | { FStar_Extraction_ML_Syntax.tydecl_assumed = uu____1434;
          FStar_Extraction_ML_Syntax.tydecl_name = name;
          FStar_Extraction_ML_Syntax.tydecl_ignored = uu____1436;
          FStar_Extraction_ML_Syntax.tydecl_parameters = parameters;
          FStar_Extraction_ML_Syntax.tydecl_meta = meta;
          FStar_Extraction_ML_Syntax.tydecl_defn = body;_} ->
          let elim_td td1 =
            match td1 with
            | FStar_Extraction_ML_Syntax.MLTD_Abbrev mlty ->
                let uu____1467 = elim_tydef env name meta parameters mlty in
                (match uu____1467 with
                 | (env1, (name1, uu____1494, parameters1, mlty1)) ->
                     (env1, parameters1,
                       (FStar_Extraction_ML_Syntax.MLTD_Abbrev mlty1)))
            | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                let uu____1526 =
                  let uu____1527 =
                    FStar_List.map
                      (fun uu____1546 ->
                         match uu____1546 with
                         | (name1, ty) ->
                             let uu____1557 = elim_mlty env ty in
                             (name1, uu____1557)) fields in
                  FStar_Extraction_ML_Syntax.MLTD_Record uu____1527 in
                (env, parameters, uu____1526)
            | FStar_Extraction_ML_Syntax.MLTD_DType inductive ->
                let uu____1573 =
                  let uu____1574 =
                    FStar_List.map
                      (fun uu____1611 ->
                         match uu____1611 with
                         | (i, constrs) ->
                             let uu____1646 =
                               FStar_List.map
                                 (fun uu____1665 ->
                                    match uu____1665 with
                                    | (constr, ty) ->
                                        let uu____1676 = elim_mlty env ty in
                                        (constr, uu____1676)) constrs in
                             (i, uu____1646)) inductive in
                  FStar_Extraction_ML_Syntax.MLTD_DType uu____1574 in
                (env, parameters, uu____1573) in
          let uu____1685 =
            match body with
            | FStar_Pervasives_Native.None -> (env, parameters, body)
            | FStar_Pervasives_Native.Some td1 ->
                let uu____1705 = elim_td td1 in
                (match uu____1705 with
                 | (env1, parameters1, td2) ->
                     (env1, parameters1, (FStar_Pervasives_Native.Some td2))) in
          (match uu____1685 with
           | (env1, parameters1, body1) ->
               (env1,
                 (let uu___313_1743 = td in
                  {
                    FStar_Extraction_ML_Syntax.tydecl_assumed =
                      (uu___313_1743.FStar_Extraction_ML_Syntax.tydecl_assumed);
                    FStar_Extraction_ML_Syntax.tydecl_name =
                      (uu___313_1743.FStar_Extraction_ML_Syntax.tydecl_name);
                    FStar_Extraction_ML_Syntax.tydecl_ignored =
                      (uu___313_1743.FStar_Extraction_ML_Syntax.tydecl_ignored);
                    FStar_Extraction_ML_Syntax.tydecl_parameters =
                      parameters1;
                    FStar_Extraction_ML_Syntax.tydecl_meta =
                      (uu___313_1743.FStar_Extraction_ML_Syntax.tydecl_meta);
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
            let uu____1784 = FStar_Util.fold_map elim_one_mltydecl env1 td in
            (match uu____1784 with
             | (env2, td1) -> (env2, (FStar_Extraction_ML_Syntax.MLM_Ty td1)))
        | FStar_Extraction_ML_Syntax.MLM_Let lb ->
            let uu____1802 =
              let uu____1803 = elim_letbinding env1 lb in
              FStar_Extraction_ML_Syntax.MLM_Let uu____1803 in
            (env1, uu____1802)
        | FStar_Extraction_ML_Syntax.MLM_Exn (name, sym_tys) ->
            let uu____1818 =
              let uu____1819 =
                let uu____1830 =
                  FStar_List.map
                    (fun uu____1849 ->
                       match uu____1849 with
                       | (s, t) ->
                           let uu____1860 = elim_mlty env1 t in
                           (s, uu____1860)) sym_tys in
                (name, uu____1830) in
              FStar_Extraction_ML_Syntax.MLM_Exn uu____1819 in
            (env1, uu____1818)
        | FStar_Extraction_ML_Syntax.MLM_Top e ->
            let uu____1868 =
              let uu____1869 = elim_mlexpr env1 e in
              FStar_Extraction_ML_Syntax.MLM_Top uu____1869 in
            (env1, uu____1868)
        | uu____1870 -> (env1, m1) in
      let uu____1871 =
        FStar_List.fold_left
          (fun uu____1888 ->
             fun m1 ->
               match uu____1888 with
               | (env1, out) ->
                   (try
                      (fun uu___342_1918 ->
                         match () with
                         | () ->
                             let uu____1925 = elim_module1 env1 m1 in
                             (match uu____1925 with
                              | (env2, m2) -> (env2, (m2 :: out)))) ()
                    with | Drop_tydef -> (env1, out))) (env, []) m in
      match uu____1871 with | (env1, m1) -> (env1, (FStar_List.rev m1))
let (set_current_module :
  env_t -> FStar_Extraction_ML_Syntax.mlpath -> env_t) =
  fun e ->
    fun n ->
      let curmod =
        FStar_List.append (FStar_Pervasives_Native.fst n)
          [FStar_Pervasives_Native.snd n] in
      let uu___358_1983 = e in
      { current_module = curmod; tydef_map = (uu___358_1983.tydef_map) }
let (elim_mllib :
  env_t ->
    FStar_Extraction_ML_Syntax.mllib ->
      (env_t * FStar_Extraction_ML_Syntax.mllib))
  =
  fun env ->
    fun m ->
      let uu____1998 =
        let uu____1999 = FStar_Options.codegen () in
        uu____1999 <> (FStar_Pervasives_Native.Some FStar_Options.FSharp) in
      if uu____1998
      then (env, m)
      else
        (let uu____2009 = m in
         match uu____2009 with
         | FStar_Extraction_ML_Syntax.MLLib libs ->
             let elim_one_lib env1 lib =
               let uu____2086 = lib in
               match uu____2086 with
               | (name, sig_mod, _libs) ->
                   let env2 = set_current_module env1 name in
                   let uu____2139 =
                     match sig_mod with
                     | FStar_Pervasives_Native.Some (sig_, mod_) ->
                         let uu____2176 = elim_module env2 mod_ in
                         (match uu____2176 with
                          | (env3, mod_1) ->
                              ((FStar_Pervasives_Native.Some (sig_, mod_1)),
                                env3))
                     | FStar_Pervasives_Native.None ->
                         (FStar_Pervasives_Native.None, env2) in
                   (match uu____2139 with
                    | (sig_mod1, env3) -> (env3, (name, sig_mod1, _libs))) in
             let uu____2295 = FStar_Util.fold_map elim_one_lib env libs in
             (match uu____2295 with
              | (env1, libs1) ->
                  (env1, (FStar_Extraction_ML_Syntax.MLLib libs1))))
let (elim_mllibs :
  FStar_Extraction_ML_Syntax.mllib Prims.list ->
    FStar_Extraction_ML_Syntax.mllib Prims.list)
  =
  fun l ->
    let uu____2393 = FStar_Util.fold_map elim_mllib initial_env l in
    FStar_Pervasives_Native.snd uu____2393