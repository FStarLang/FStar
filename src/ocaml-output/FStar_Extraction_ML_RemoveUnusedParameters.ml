open Prims
type argument_tag =
  | Retain 
  | Omit 
let (uu___is_Retain : argument_tag -> Prims.bool) =
  fun projectee -> match projectee with | Retain -> true | uu____10 -> false
let (uu___is_Omit : argument_tag -> Prims.bool) =
  fun projectee -> match projectee with | Omit -> true | uu____21 -> false
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
  let uu____77 = FStar_Util.psmap_empty () in
  { current_module = []; tydef_map = uu____77 }
let (extend_env :
  env_t -> FStar_Extraction_ML_Syntax.mlsymbol -> entry -> env_t) =
  fun env ->
    fun i ->
      fun e ->
        let uu___9_99 = env in
        let uu____100 =
          let uu____103 =
            FStar_Extraction_ML_Syntax.string_of_mlpath
              ((env.current_module), i) in
          FStar_Util.psmap_add env.tydef_map uu____103 e in
        { current_module = (uu___9_99.current_module); tydef_map = uu____100
        }
let (lookup_tyname :
  env_t ->
    FStar_Extraction_ML_Syntax.mlpath -> entry FStar_Pervasives_Native.option)
  =
  fun env ->
    fun name ->
      let uu____124 = FStar_Extraction_ML_Syntax.string_of_mlpath name in
      FStar_Util.psmap_try_find env.tydef_map uu____124
type var_set = FStar_Extraction_ML_Syntax.mlident FStar_Util.set
let (empty_var_set : Prims.string FStar_Util.set) =
  FStar_Util.new_set (fun x -> fun y -> FStar_String.compare x y)
let rec (freevars_of_mlty' :
  var_set -> FStar_Extraction_ML_Syntax.mlty -> var_set) =
  fun vars ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var i -> FStar_Util.set_add i vars
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____155, t1) ->
          let uu____157 = freevars_of_mlty' vars t0 in
          freevars_of_mlty' uu____157 t1
      | FStar_Extraction_ML_Syntax.MLTY_Named (tys, uu____159) ->
          FStar_List.fold_left freevars_of_mlty' vars tys
      | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
          FStar_List.fold_left freevars_of_mlty' vars tys
      | uu____167 -> vars
let (freevars_of_mlty : FStar_Extraction_ML_Syntax.mlty -> var_set) =
  freevars_of_mlty' empty_var_set
let rec (elim_mlty :
  env_t -> FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun env ->
    fun mlty ->
      match mlty with
      | FStar_Extraction_ML_Syntax.MLTY_Var uu____184 -> mlty
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t0, e, t1) ->
          let uu____189 =
            let uu____196 = elim_mlty env t0 in
            let uu____197 = elim_mlty env t1 in (uu____196, e, uu____197) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____189
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, name) ->
          let args1 = FStar_List.map (elim_mlty env) args in
          let uu____207 = lookup_tyname env name in
          (match uu____207 with
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
                            | uu____233 -> out) args1 entry1 [] in
                 FStar_Extraction_ML_Syntax.MLTY_Named (args2, name))))
      | FStar_Extraction_ML_Syntax.MLTY_Tuple tys ->
          let uu____239 = FStar_List.map (elim_mlty env) tys in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____239
      | FStar_Extraction_ML_Syntax.MLTY_Top -> mlty
      | FStar_Extraction_ML_Syntax.MLTY_Erased -> mlty
let rec (elim_mlexpr' :
  env_t ->
    FStar_Extraction_ML_Syntax.mlexpr' -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun env ->
    fun e ->
      match e with
      | FStar_Extraction_ML_Syntax.MLE_Const uu____305 -> e
      | FStar_Extraction_ML_Syntax.MLE_Var uu____306 -> e
      | FStar_Extraction_ML_Syntax.MLE_Name uu____308 -> e
      | FStar_Extraction_ML_Syntax.MLE_Let (lb, e1) ->
          let uu____323 =
            let uu____334 = elim_letbinding env lb in
            let uu____341 = elim_mlexpr env e1 in (uu____334, uu____341) in
          FStar_Extraction_ML_Syntax.MLE_Let uu____323
      | FStar_Extraction_ML_Syntax.MLE_App (e1, es) ->
          let uu____354 =
            let uu____361 = elim_mlexpr env e1 in
            let uu____362 = FStar_List.map (elim_mlexpr env) es in
            (uu____361, uu____362) in
          FStar_Extraction_ML_Syntax.MLE_App uu____354
      | FStar_Extraction_ML_Syntax.MLE_TApp (e1, tys) ->
          let uu____373 =
            let uu____380 = FStar_List.map (elim_mlty env) tys in
            (e1, uu____380) in
          FStar_Extraction_ML_Syntax.MLE_TApp uu____373
      | FStar_Extraction_ML_Syntax.MLE_Fun (bvs, e1) ->
          let uu____401 =
            let uu____413 =
              FStar_List.map
                (fun uu____435 ->
                   match uu____435 with
                   | (x, t) ->
                       let uu____450 = elim_mlty env t in (x, uu____450)) bvs in
            let uu____452 = elim_mlexpr env e1 in (uu____413, uu____452) in
          FStar_Extraction_ML_Syntax.MLE_Fun uu____401
      | FStar_Extraction_ML_Syntax.MLE_Match (e1, branches) ->
          let uu____482 =
            let uu____497 = elim_mlexpr env e1 in
            let uu____498 = FStar_List.map (elim_branch env) branches in
            (uu____497, uu____498) in
          FStar_Extraction_ML_Syntax.MLE_Match uu____482
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t0, t1) ->
          let uu____538 =
            let uu____545 = elim_mlexpr env e1 in
            let uu____546 = elim_mlty env t0 in
            let uu____547 = elim_mlty env t1 in
            (uu____545, uu____546, uu____547) in
          FStar_Extraction_ML_Syntax.MLE_Coerce uu____538
      | FStar_Extraction_ML_Syntax.MLE_CTor (l, es) ->
          let uu____554 =
            let uu____561 = FStar_List.map (elim_mlexpr env) es in
            (l, uu____561) in
          FStar_Extraction_ML_Syntax.MLE_CTor uu____554
      | FStar_Extraction_ML_Syntax.MLE_Seq es ->
          let uu____569 = FStar_List.map (elim_mlexpr env) es in
          FStar_Extraction_ML_Syntax.MLE_Seq uu____569
      | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
          let uu____575 = FStar_List.map (elim_mlexpr env) es in
          FStar_Extraction_ML_Syntax.MLE_Tuple uu____575
      | FStar_Extraction_ML_Syntax.MLE_Record (syms, fields) ->
          let uu____600 =
            let uu____615 =
              FStar_List.map
                (fun uu____637 ->
                   match uu____637 with
                   | (s, e1) ->
                       let uu____652 = elim_mlexpr env e1 in (s, uu____652))
                fields in
            (syms, uu____615) in
          FStar_Extraction_ML_Syntax.MLE_Record uu____600
      | FStar_Extraction_ML_Syntax.MLE_Proj (e1, p) ->
          let uu____666 =
            let uu____671 = elim_mlexpr env e1 in (uu____671, p) in
          FStar_Extraction_ML_Syntax.MLE_Proj uu____666
      | FStar_Extraction_ML_Syntax.MLE_If (e1, e11, e2_opt) ->
          let uu____679 =
            let uu____688 = elim_mlexpr env e1 in
            let uu____689 = elim_mlexpr env e11 in
            let uu____690 = FStar_Util.map_opt e2_opt (elim_mlexpr env) in
            (uu____688, uu____689, uu____690) in
          FStar_Extraction_ML_Syntax.MLE_If uu____679
      | FStar_Extraction_ML_Syntax.MLE_Raise (p, es) ->
          let uu____701 =
            let uu____708 = FStar_List.map (elim_mlexpr env) es in
            (p, uu____708) in
          FStar_Extraction_ML_Syntax.MLE_Raise uu____701
      | FStar_Extraction_ML_Syntax.MLE_Try (e1, branches) ->
          let uu____735 =
            let uu____750 = elim_mlexpr env e1 in
            let uu____751 = FStar_List.map (elim_branch env) branches in
            (uu____750, uu____751) in
          FStar_Extraction_ML_Syntax.MLE_Try uu____735
and (elim_letbinding :
  env_t ->
    (FStar_Extraction_ML_Syntax.mlletflavor * FStar_Extraction_ML_Syntax.mllb
      Prims.list) ->
      (FStar_Extraction_ML_Syntax.mlletflavor *
        FStar_Extraction_ML_Syntax.mllb Prims.list))
  =
  fun env ->
    fun uu____789 ->
      match uu____789 with
      | (flavor, lbs) ->
          let elim_one_lb lb =
            let ts =
              FStar_Util.map_opt lb.FStar_Extraction_ML_Syntax.mllb_tysc
                (fun uu____829 ->
                   match uu____829 with
                   | (vars, t) ->
                       let uu____836 = elim_mlty env t in (vars, uu____836)) in
            let expr = elim_mlexpr env lb.FStar_Extraction_ML_Syntax.mllb_def in
            let uu___138_838 = lb in
            {
              FStar_Extraction_ML_Syntax.mllb_name =
                (uu___138_838.FStar_Extraction_ML_Syntax.mllb_name);
              FStar_Extraction_ML_Syntax.mllb_tysc = ts;
              FStar_Extraction_ML_Syntax.mllb_add_unit =
                (uu___138_838.FStar_Extraction_ML_Syntax.mllb_add_unit);
              FStar_Extraction_ML_Syntax.mllb_def = expr;
              FStar_Extraction_ML_Syntax.mllb_meta =
                (uu___138_838.FStar_Extraction_ML_Syntax.mllb_meta);
              FStar_Extraction_ML_Syntax.print_typ =
                (uu___138_838.FStar_Extraction_ML_Syntax.print_typ)
            } in
          let uu____839 = FStar_List.map elim_one_lb lbs in
          (flavor, uu____839)
and (elim_branch :
  env_t ->
    (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr
      FStar_Pervasives_Native.option * FStar_Extraction_ML_Syntax.mlexpr) ->
      (FStar_Extraction_ML_Syntax.mlpattern *
        FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option *
        FStar_Extraction_ML_Syntax.mlexpr))
  =
  fun env ->
    fun uu____845 ->
      match uu____845 with
      | (pat, wopt, e) ->
          let uu____869 = FStar_Util.map_opt wopt (elim_mlexpr env) in
          let uu____872 = elim_mlexpr env e in (pat, uu____869, uu____872)
and (elim_mlexpr :
  env_t ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun env ->
    fun e ->
      let uu___147_877 = e in
      let uu____878 = elim_mlexpr' env e.FStar_Extraction_ML_Syntax.expr in
      let uu____879 = elim_mlty env e.FStar_Extraction_ML_Syntax.mlty in
      {
        FStar_Extraction_ML_Syntax.expr = uu____878;
        FStar_Extraction_ML_Syntax.mlty = uu____879;
        FStar_Extraction_ML_Syntax.loc =
          (uu___147_877.FStar_Extraction_ML_Syntax.loc)
      }
let (elim_one_mltydecl :
  env_t ->
    FStar_Extraction_ML_Syntax.one_mltydecl ->
      (env_t * FStar_Extraction_ML_Syntax.one_mltydecl))
  =
  fun env ->
    fun td ->
      let uu____899 = td in
      match uu____899 with
      | (_assumed, name, _ignored, parameters, _metadata, body) ->
          let elim_td td1 =
            match td1 with
            | FStar_Extraction_ML_Syntax.MLTD_Abbrev mlty ->
                let mlty1 = elim_mlty env mlty in
                let freevars = freevars_of_mlty mlty1 in
                let uu____951 =
                  FStar_List.fold_right
                    (fun p ->
                       fun uu____977 ->
                         match uu____977 with
                         | (params, entry1) ->
                             let uu____1009 = FStar_Util.set_mem p freevars in
                             if uu____1009
                             then ((p :: params), (Retain :: entry1))
                             else (params, (Omit :: entry1))) parameters
                    ([], []) in
                (match uu____951 with
                 | (parameters1, entry1) ->
                     let uu____1062 = extend_env env name entry1 in
                     (uu____1062, parameters1,
                       (FStar_Extraction_ML_Syntax.MLTD_Abbrev mlty1)))
            | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
                let uu____1074 =
                  let uu____1075 =
                    FStar_List.map
                      (fun uu____1097 ->
                         match uu____1097 with
                         | (name1, ty) ->
                             let uu____1112 = elim_mlty env ty in
                             (name1, uu____1112)) fields in
                  FStar_Extraction_ML_Syntax.MLTD_Record uu____1075 in
                (env, parameters, uu____1074)
            | FStar_Extraction_ML_Syntax.MLTD_DType inductive ->
                let uu____1132 =
                  let uu____1133 =
                    FStar_List.map
                      (fun uu____1176 ->
                         match uu____1176 with
                         | (i, constrs) ->
                             let uu____1219 =
                               FStar_List.map
                                 (fun uu____1241 ->
                                    match uu____1241 with
                                    | (constr, ty) ->
                                        let uu____1256 = elim_mlty env ty in
                                        (constr, uu____1256)) constrs in
                             (i, uu____1219)) inductive in
                  FStar_Extraction_ML_Syntax.MLTD_DType uu____1133 in
                (env, parameters, uu____1132) in
          let uu____1269 =
            match body with
            | FStar_Pervasives_Native.None -> (env, parameters, body)
            | FStar_Pervasives_Native.Some td1 ->
                let uu____1289 = elim_td td1 in
                (match uu____1289 with
                 | (env1, parameters1, td2) ->
                     (env1, parameters1, (FStar_Pervasives_Native.Some td2))) in
          (match uu____1269 with
           | (env1, parameters1, body1) ->
               (env1,
                 (_assumed, name, _ignored, parameters1, _metadata, body1)))
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
            let uu____1377 = FStar_Util.fold_map elim_one_mltydecl env1 td in
            (match uu____1377 with
             | (env2, td1) -> (env2, (FStar_Extraction_ML_Syntax.MLM_Ty td1)))
        | FStar_Extraction_ML_Syntax.MLM_Let lb ->
            let uu____1395 =
              let uu____1396 = elim_letbinding env1 lb in
              FStar_Extraction_ML_Syntax.MLM_Let uu____1396 in
            (env1, uu____1395)
        | FStar_Extraction_ML_Syntax.MLM_Exn (name, sym_tys) ->
            let uu____1415 =
              let uu____1416 =
                let uu____1429 =
                  FStar_List.map
                    (fun uu____1451 ->
                       match uu____1451 with
                       | (s, t) ->
                           let uu____1466 = elim_mlty env1 t in
                           (s, uu____1466)) sym_tys in
                (name, uu____1429) in
              FStar_Extraction_ML_Syntax.MLM_Exn uu____1416 in
            (env1, uu____1415)
        | FStar_Extraction_ML_Syntax.MLM_Top e ->
            let uu____1477 =
              let uu____1478 = elim_mlexpr env1 e in
              FStar_Extraction_ML_Syntax.MLM_Top uu____1478 in
            (env1, uu____1477)
        | uu____1479 -> (env1, m1) in
      FStar_Util.fold_map elim_module1 env m
let (elim_mllib :
  env_t ->
    FStar_Extraction_ML_Syntax.mllib ->
      (env_t * FStar_Extraction_ML_Syntax.mllib))
  =
  fun env ->
    fun m ->
      let uu____1495 = m in
      match uu____1495 with
      | FStar_Extraction_ML_Syntax.MLLib libs ->
          let elim_one_lib env1 lib =
            let uu____1596 = lib in
            match uu____1596 with
            | (name, sig_mod, _libs) ->
                let env2 =
                  let uu___229_1681 = env1 in
                  {
                    current_module =
                      (FStar_List.append (FStar_Pervasives_Native.fst name)
                         [FStar_Pervasives_Native.snd name]);
                    tydef_map = (uu___229_1681.tydef_map)
                  } in
                let uu____1693 =
                  match sig_mod with
                  | FStar_Pervasives_Native.Some (sig_, mod_) ->
                      let uu____1730 = elim_module env2 mod_ in
                      (match uu____1730 with
                       | (env3, mod_1) ->
                           ((FStar_Pervasives_Native.Some (sig_, mod_1)),
                             env3))
                  | FStar_Pervasives_Native.None ->
                      (FStar_Pervasives_Native.None, env2) in
                (match uu____1693 with
                 | (sig_mod1, env3) -> (env3, (name, sig_mod1, _libs))) in
          let uu____1873 = FStar_Util.fold_map elim_one_lib env libs in
          (match uu____1873 with
           | (env1, libs1) ->
               (env1, (FStar_Extraction_ML_Syntax.MLLib libs1)))
let (elim_mllibs :
  FStar_Extraction_ML_Syntax.mllib Prims.list ->
    FStar_Extraction_ML_Syntax.mllib Prims.list)
  =
  fun l ->
    let uu____2004 = FStar_Util.fold_map elim_mllib initial_env l in
    FStar_Pervasives_Native.snd uu____2004