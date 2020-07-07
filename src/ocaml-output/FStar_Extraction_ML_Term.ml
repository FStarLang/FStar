open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Un_extractable -> true | uu____8 -> false
let (type_leq :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Extraction_ML_Util.type_leq
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
let (type_leq_c :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr
            FStar_Pervasives_Native.option))
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Extraction_ML_Util.type_leq_c
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
let (eraseTypeDeep :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t ->
      FStar_Extraction_ML_Util.eraseTypeDeep
        (FStar_Extraction_ML_Util.udelta_unfold g) t
let fail :
  'uuuuuu77 .
    FStar_Range.range -> (FStar_Errors.raw_error * Prims.string) -> 'uuuuuu77
  = fun r -> fun err -> FStar_Errors.raise_error err r
let err_ill_typed_application :
  'uuuuuu113 'uuuuuu114 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'uuuuuu113) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'uuuuuu114
  =
  fun env ->
    fun t ->
      fun mlhead ->
        fun args ->
          fun ty ->
            let uu____152 =
              let uu____158 =
                let uu____160 = FStar_Syntax_Print.term_to_string t in
                let uu____162 =
                  let uu____164 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env in
                  FStar_Extraction_ML_Code.string_of_mlexpr uu____164 mlhead in
                let uu____165 =
                  let uu____167 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env in
                  FStar_Extraction_ML_Code.string_of_mlty uu____167 ty in
                let uu____168 =
                  let uu____170 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____191 ->
                            match uu____191 with
                            | (x, uu____198) ->
                                FStar_Syntax_Print.term_to_string x)) in
                  FStar_All.pipe_right uu____170 (FStar_String.concat " ") in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____160 uu____162 uu____165 uu____168 in
              (FStar_Errors.Fatal_IllTyped, uu____158) in
            fail t.FStar_Syntax_Syntax.pos uu____152
let err_ill_typed_erasure :
  'uuuuuu215 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'uuuuuu215
  =
  fun env ->
    fun pos ->
      fun ty ->
        let uu____231 =
          let uu____237 =
            let uu____239 =
              let uu____241 =
                FStar_Extraction_ML_UEnv.current_module_of_uenv env in
              FStar_Extraction_ML_Code.string_of_mlty uu____241 ty in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____239 in
          (FStar_Errors.Fatal_IllTyped, uu____237) in
        fail pos uu____231
let err_value_restriction :
  'uuuuuu249 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'uuuuuu249
  =
  fun t ->
    let uu____259 =
      let uu____265 =
        let uu____267 = FStar_Syntax_Print.tag_of_term t in
        let uu____269 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____267 uu____269 in
      (FStar_Errors.Fatal_ValueRestriction, uu____265) in
    fail t.FStar_Syntax_Syntax.pos uu____259
let (err_unexpected_eff :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.e_tag ->
          FStar_Extraction_ML_Syntax.e_tag -> unit)
  =
  fun env ->
    fun t ->
      fun ty ->
        fun f0 ->
          fun f1 ->
            let uu____303 =
              let uu____309 =
                let uu____311 = FStar_Syntax_Print.term_to_string t in
                let uu____313 =
                  let uu____315 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env in
                  FStar_Extraction_ML_Code.string_of_mlty uu____315 ty in
                let uu____316 = FStar_Extraction_ML_Util.eff_to_string f0 in
                let uu____318 = FStar_Extraction_ML_Util.eff_to_string f1 in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____311 uu____313 uu____316 uu____318 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____309) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____303
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.of_int (20)) in
  let rec delta_norm_eff g l =
    let uu____346 =
      let uu____349 = FStar_Ident.string_of_lid l in
      FStar_Util.smap_try_find cache uu____349 in
    match uu____346 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None ->
        let res =
          let uu____353 =
            let uu____360 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
            FStar_TypeChecker_Env.lookup_effect_abbrev uu____360
              [FStar_Syntax_Syntax.U_zero] l in
          match uu____353 with
          | FStar_Pervasives_Native.None -> l
          | FStar_Pervasives_Native.Some (uu____365, c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c) in
        ((let uu____372 = FStar_Ident.string_of_lid l in
          FStar_Util.smap_add cache uu____372 res);
         res) in
  fun g ->
    fun l ->
      let l1 = delta_norm_eff g l in
      let uu____377 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid in
      if uu____377
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____382 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid in
         if uu____382
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              let uu____396 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
              FStar_TypeChecker_Env.effect_decl_opt uu____396 l1 in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                let uu____409 =
                  let uu____411 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                  FStar_TypeChecker_Env.is_reifiable_effect uu____411
                    ed.FStar_Syntax_Syntax.mname in
                if uu____409
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____434 =
        let uu____435 = FStar_Syntax_Subst.compress t1 in
        uu____435.FStar_Syntax_Syntax.n in
      match uu____434 with
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____441 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____458 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____487 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____497 = FStar_Syntax_Util.unfold_lazy i in
          is_arity env uu____497
      | FStar_Syntax_Syntax.Tm_uvar uu____498 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____512 -> false
      | FStar_Syntax_Syntax.Tm_name uu____514 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____516 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____524 -> false
      | FStar_Syntax_Syntax.Tm_type uu____526 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____528, c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let topt =
            let uu____558 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] uu____558
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match topt with
           | FStar_Pervasives_Native.None -> false
           | FStar_Pervasives_Native.Some (uu____565, t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____571 ->
          let uu____588 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____588 with | (head, uu____607) -> is_arity env head)
      | FStar_Syntax_Syntax.Tm_uinst (head, uu____633) -> is_arity env head
      | FStar_Syntax_Syntax.Tm_refine (x, uu____639) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____644, body, uu____646) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____671, body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____691, branches) ->
          (match branches with
           | (uu____730, uu____731, e)::uu____733 -> is_arity env e
           | uu____780 -> false)
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____812 ->
          let uu____827 =
            let uu____829 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____829 in
          failwith uu____827
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____833 =
            let uu____835 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____835 in
          failwith uu____833
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____840 = FStar_Syntax_Util.unfold_lazy i in
          is_type_aux env uu____840
      | FStar_Syntax_Syntax.Tm_constant uu____841 -> false
      | FStar_Syntax_Syntax.Tm_type uu____843 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____845 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____853 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____872;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____873;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____874;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____876;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____877;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____878;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____879;_},
           s)
          ->
          let uu____924 = FStar_Syntax_Subst.subst' s t2 in
          is_arity env uu____924
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____925;
            FStar_Syntax_Syntax.index = uu____926;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____931;
            FStar_Syntax_Syntax.index = uu____932;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____938, uu____939) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____981) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____988) ->
          let uu____1013 = FStar_Syntax_Subst.open_term bs body in
          (match uu____1013 with
           | (uu____1019, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
          let uu____1039 =
            let uu____1044 =
              let uu____1045 = FStar_Syntax_Syntax.mk_binder x in
              [uu____1045] in
            FStar_Syntax_Subst.open_term uu____1044 body in
          (match uu____1039 with
           | (uu____1065, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1067, lbs), body) ->
          let uu____1087 = FStar_Syntax_Subst.open_let_rec lbs body in
          (match uu____1087 with
           | (uu____1095, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1101, branches) ->
          (match branches with
           | b::uu____1141 ->
               let uu____1186 = FStar_Syntax_Subst.open_branch b in
               (match uu____1186 with
                | (uu____1188, uu____1189, e) -> is_type_aux env e)
           | uu____1207 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1225 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2, uu____1234) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head, uu____1240) -> is_type_aux env head
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1281 ->
           let uu____1282 = FStar_Syntax_Print.tag_of_term t in
           let uu____1284 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1282
             uu____1284);
      (let b = is_type_aux env t in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1293 ->
            if b
            then
              let uu____1295 = FStar_Syntax_Print.term_to_string t in
              let uu____1297 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1295
                uu____1297
            else
              (let uu____1302 = FStar_Syntax_Print.term_to_string t in
               let uu____1304 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1302 uu____1304));
       b)
let is_type_binder :
  'uuuuuu1314 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu1314) -> Prims.bool
  =
  fun env ->
    fun x ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1341 =
      let uu____1342 = FStar_Syntax_Subst.compress t in
      uu____1342.FStar_Syntax_Syntax.n in
    match uu____1341 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1346;
          FStar_Syntax_Syntax.fv_delta = uu____1347;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor);_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1349;
          FStar_Syntax_Syntax.fv_delta = uu____1350;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1351);_}
        -> true
    | uu____1359 -> false
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1368 =
      let uu____1369 = FStar_Syntax_Subst.compress t in
      uu____1369.FStar_Syntax_Syntax.n in
    match uu____1368 with
    | FStar_Syntax_Syntax.Tm_constant uu____1373 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1375 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1377 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1379 -> true
    | FStar_Syntax_Syntax.Tm_app (head, args) ->
        let uu____1425 = is_constructor head in
        if uu____1425
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1447 ->
                  match uu____1447 with
                  | (te, uu____1456) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1, uu____1465) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1471, uu____1472) ->
        is_fstar_value t1
    | uu____1513 -> false
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1523 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1525 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1528 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1530 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1543, exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1552, fields) ->
        FStar_Util.for_all
          (fun uu____1582 ->
             match uu____1582 with | (uu____1589, e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h, uu____1594) -> is_ml_value h
    | uu____1599 -> false
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0 ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1681 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____1683 = FStar_Syntax_Util.is_fun e' in
          if uu____1683
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 FStar_Pervasives_Native.None
let (unit_binder : unit -> FStar_Syntax_Syntax.binder) =
  fun uu____1701 ->
    let uu____1702 =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.t_unit in
    FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1702
let (check_pats_for_ite :
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list ->
    (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option))
  =
  fun l ->
    let def =
      (false, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) in
    if (FStar_List.length l) <> (Prims.of_int (2))
    then def
    else
      (let uu____1793 = FStar_List.hd l in
       match uu____1793 with
       | (p1, w1, e1) ->
           let uu____1828 =
             let uu____1837 = FStar_List.tl l in FStar_List.hd uu____1837 in
           (match uu____1828 with
            | (p2, w2, e2) ->
                (match (w1, w2, (p1.FStar_Syntax_Syntax.v),
                         (p2.FStar_Syntax_Syntax.v))
                 with
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None,
                    FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool
                    (true)), FStar_Syntax_Syntax.Pat_constant
                    (FStar_Const.Const_bool (false))) ->
                     (true, (FStar_Pervasives_Native.Some e1),
                       (FStar_Pervasives_Native.Some e2))
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None,
                    FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool
                    (false)), FStar_Syntax_Syntax.Pat_constant
                    (FStar_Const.Const_bool (true))) ->
                     (true, (FStar_Pervasives_Native.Some e2),
                       (FStar_Pervasives_Native.Some e1))
                 | uu____1921 -> def)))
let (instantiate_tyscheme :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  = fun s -> fun args -> FStar_Extraction_ML_Util.subst s args
let (fresh_mlidents :
  FStar_Extraction_ML_Syntax.mlty Prims.list ->
    FStar_Extraction_ML_UEnv.uenv ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun ts ->
    fun g ->
      let uu____1986 =
        FStar_List.fold_right
          (fun t ->
             fun uu____2017 ->
               match uu____2017 with
               | (uenv, vs) ->
                   let uu____2056 = FStar_Extraction_ML_UEnv.new_mlident uenv in
                   (match uu____2056 with
                    | (uenv1, v) -> (uenv1, ((v, t) :: vs)))) ts (g, []) in
      match uu____1986 with | (g1, vs_ts) -> (vs_ts, g1)
let (instantiate_maybe_partial :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        FStar_Extraction_ML_Syntax.mlty Prims.list ->
          (FStar_Extraction_ML_Syntax.mlexpr *
            FStar_Extraction_ML_Syntax.e_tag *
            FStar_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun e ->
      fun s ->
        fun tyargs ->
          let uu____2173 = s in
          match uu____2173 with
          | (vars, t) ->
              let n_vars = FStar_List.length vars in
              let n_args = FStar_List.length tyargs in
              if n_args = n_vars
              then
                (if n_args = Prims.int_zero
                 then (e, FStar_Extraction_ML_Syntax.E_PURE, t)
                 else
                   (let ts = instantiate_tyscheme (vars, t) tyargs in
                    let tapp =
                      let uu___372_2205 = e in
                      {
                        FStar_Extraction_ML_Syntax.expr =
                          (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                        FStar_Extraction_ML_Syntax.mlty = ts;
                        FStar_Extraction_ML_Syntax.loc =
                          (uu___372_2205.FStar_Extraction_ML_Syntax.loc)
                      } in
                    (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
              else
                if n_args < n_vars
                then
                  (let extra_tyargs =
                     let uu____2220 = FStar_Util.first_N n_args vars in
                     match uu____2220 with
                     | (uu____2234, rest_vars) ->
                         FStar_All.pipe_right rest_vars
                           (FStar_List.map
                              (fun uu____2255 ->
                                 FStar_Extraction_ML_Syntax.MLTY_Erased)) in
                   let tyargs1 = FStar_List.append tyargs extra_tyargs in
                   let ts = instantiate_tyscheme (vars, t) tyargs1 in
                   let tapp =
                     let uu___383_2262 = e in
                     {
                       FStar_Extraction_ML_Syntax.expr =
                         (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                       FStar_Extraction_ML_Syntax.mlty = ts;
                       FStar_Extraction_ML_Syntax.loc =
                         (uu___383_2262.FStar_Extraction_ML_Syntax.loc)
                     } in
                   let t1 =
                     FStar_List.fold_left
                       (fun out ->
                          fun t1 ->
                            FStar_Extraction_ML_Syntax.MLTY_Fun
                              (t1, FStar_Extraction_ML_Syntax.E_PURE, out))
                       ts extra_tyargs in
                   let uu____2270 = fresh_mlidents extra_tyargs g in
                   match uu____2270 with
                   | (vs_ts, g1) ->
                       let f =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty t1)
                           (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, tapp)) in
                       (f, FStar_Extraction_ML_Syntax.E_PURE, t1))
                else
                  failwith
                    "Impossible: instantiate_maybe_partial called with too many arguments"
let (eta_expand :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun t ->
      fun e ->
        let uu____2337 = FStar_Extraction_ML_Util.doms_and_cod t in
        match uu____2337 with
        | (ts, r) ->
            if ts = []
            then e
            else
              (let uu____2355 = fresh_mlidents ts g in
               match uu____2355 with
               | (vs_ts, g1) ->
                   let vs_es =
                     FStar_List.map
                       (fun uu____2394 ->
                          match uu____2394 with
                          | (v, t1) ->
                              FStar_Extraction_ML_Syntax.with_ty t1
                                (FStar_Extraction_ML_Syntax.MLE_Var v)) vs_ts in
                   let body =
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty r)
                       (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es)) in
                   FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
                     (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
let (default_value_for_ty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun t ->
      let uu____2425 = FStar_Extraction_ML_Util.doms_and_cod t in
      match uu____2425 with
      | (ts, r) ->
          let body r1 =
            let r2 =
              let uu____2445 = FStar_Extraction_ML_Util.udelta_unfold g r1 in
              match uu____2445 with
              | FStar_Pervasives_Native.None -> r1
              | FStar_Pervasives_Native.Some r2 -> r2 in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2449 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2)) in
          if ts = []
          then body r
          else
            (let uu____2455 = fresh_mlidents ts g in
             match uu____2455 with
             | (vs_ts, g1) ->
                 let uu____2483 =
                   let uu____2484 =
                     let uu____2496 = body r in (vs_ts, uu____2496) in
                   FStar_Extraction_ML_Syntax.MLE_Fun uu____2484 in
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
                   uu____2483)
let (maybe_eta_expand :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun expect ->
      fun e ->
        let uu____2520 =
          (FStar_Options.ml_no_eta_expand_coertions ()) ||
            (let uu____2523 = FStar_Options.codegen () in
             uu____2523 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin)) in
        if uu____2520 then e else eta_expand g expect e
let (apply_coercion :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun e ->
      fun ty ->
        fun expect ->
          let mk_fun binder body =
            match body.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_Fun (binders, body1) ->
                FStar_Extraction_ML_Syntax.MLE_Fun
                  ((binder :: binders), body1)
            | uu____2601 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body) in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____2656 =
              match uu____2656 with
              | (pat, w, b) ->
                  let uu____2680 = aux b ty1 expect1 in (pat, w, uu____2680) in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun (arg::rest, body),
               FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____2687, t1),
               FStar_Extraction_ML_Syntax.MLTY_Fun (s0, uu____2690, s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____2722 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body)) in
                let body2 = aux body1 t1 s1 in
                let uu____2738 = type_leq g s0 t0 in
                if uu____2738
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____2744 =
                       let uu____2745 =
                         let uu____2746 =
                           let uu____2753 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg)) in
                           (uu____2753, s0, t0) in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____2746 in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____2745 in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____2744;
                       FStar_Extraction_ML_Syntax.mllb_meta = [];
                       FStar_Extraction_ML_Syntax.print_typ = false
                     } in
                   let body3 =
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty s1)
                       (FStar_Extraction_ML_Syntax.MLE_Let
                          ((FStar_Extraction_ML_Syntax.NonRec, [lb]), body2)) in
                   FStar_Extraction_ML_Syntax.with_ty expect1
                     (mk_fun ((FStar_Pervasives_Native.fst arg), s0) body3))
            | (FStar_Extraction_ML_Syntax.MLE_Let (lbs, body), uu____2772,
               uu____2773) ->
                let uu____2786 =
                  let uu____2787 =
                    let uu____2798 = aux body ty1 expect1 in
                    (lbs, uu____2798) in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____2787 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2786
            | (FStar_Extraction_ML_Syntax.MLE_Match (s, branches),
               uu____2807, uu____2808) ->
                let uu____2829 =
                  let uu____2830 =
                    let uu____2845 = FStar_List.map coerce_branch branches in
                    (s, uu____2845) in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____2830 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2829
            | (FStar_Extraction_ML_Syntax.MLE_If (s, b1, b2_opt), uu____2885,
               uu____2886) ->
                let uu____2891 =
                  let uu____2892 =
                    let uu____2901 = aux b1 ty1 expect1 in
                    let uu____2902 =
                      FStar_Util.map_opt b2_opt
                        (fun b2 -> aux b2 ty1 expect1) in
                    (s, uu____2901, uu____2902) in
                  FStar_Extraction_ML_Syntax.MLE_If uu____2892 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2891
            | (FStar_Extraction_ML_Syntax.MLE_Seq es, uu____2910, uu____2911)
                ->
                let uu____2914 = FStar_Util.prefix es in
                (match uu____2914 with
                 | (prefix, last) ->
                     let uu____2927 =
                       let uu____2928 =
                         let uu____2931 =
                           let uu____2934 = aux last ty1 expect1 in
                           [uu____2934] in
                         FStar_List.append prefix uu____2931 in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____2928 in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____2927)
            | (FStar_Extraction_ML_Syntax.MLE_Try (s, branches), uu____2937,
               uu____2938) ->
                let uu____2959 =
                  let uu____2960 =
                    let uu____2975 = FStar_List.map coerce_branch branches in
                    (s, uu____2975) in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____2960 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2959
            | uu____3012 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1)) in
          aux e ty expect
let maybe_coerce :
  'uuuuuu3032 .
    'uuuuuu3032 ->
      FStar_Extraction_ML_UEnv.uenv ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          FStar_Extraction_ML_Syntax.mlty ->
            FStar_Extraction_ML_Syntax.mlty ->
              FStar_Extraction_ML_Syntax.mlexpr
  =
  fun pos ->
    fun g ->
      fun e ->
        fun ty ->
          fun expect ->
            let ty1 = eraseTypeDeep g ty in
            let uu____3059 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect in
            match uu____3059 with
            | (true, FStar_Pervasives_Native.Some e') -> e'
            | uu____3072 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                     default_value_for_ty g expect
                 | uu____3080 ->
                     let uu____3081 =
                       let uu____3083 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1 in
                       let uu____3084 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect in
                       type_leq g uu____3083 uu____3084 in
                     if uu____3081
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3090 ->
                             let uu____3091 =
                               let uu____3093 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3093 e in
                             let uu____3094 =
                               let uu____3096 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3096 ty1 in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____3091 uu____3094);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3105 ->
                             let uu____3106 =
                               let uu____3108 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3108 e in
                             let uu____3109 =
                               let uu____3111 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3111 ty1 in
                             let uu____3112 =
                               let uu____3114 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3114 expect in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____3106 uu____3109 uu____3112);
                        (let uu____3116 = apply_coercion g e ty1 expect in
                         maybe_eta_expand g expect uu____3116)))
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun bv ->
      let uu____3128 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____3128 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____3130 -> FStar_Extraction_ML_Syntax.MLTY_Top
let (extraction_norm_steps_core : FStar_TypeChecker_Env.step Prims.list) =
  [FStar_TypeChecker_Env.AllowUnboundUniverses;
  FStar_TypeChecker_Env.EraseUniverses;
  FStar_TypeChecker_Env.Inlining;
  FStar_TypeChecker_Env.Eager_unfolding;
  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
  FStar_TypeChecker_Env.Primops;
  FStar_TypeChecker_Env.Unascribe;
  FStar_TypeChecker_Env.ForExtraction]
let (extraction_norm_steps_nbe : FStar_TypeChecker_Env.step Prims.list) =
  FStar_TypeChecker_Env.NBE :: extraction_norm_steps_core
let (extraction_norm_steps : unit -> FStar_TypeChecker_Env.step Prims.list) =
  fun uu____3144 ->
    let uu____3145 = FStar_Options.use_nbe_for_extraction () in
    if uu____3145
    then extraction_norm_steps_nbe
    else extraction_norm_steps_core
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____3166 -> c
    | FStar_Syntax_Syntax.GTotal uu____3175 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____3211 ->
               match uu____3211 with
               | (uu____3226, aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args in
        let ct1 =
          let uu___550_3239 = ct in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___550_3239.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___550_3239.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___550_3239.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___550_3239.FStar_Syntax_Syntax.flags)
          } in
        let c1 =
          let uu___553_3243 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___553_3243.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___553_3243.FStar_Syntax_Syntax.vars)
          } in
        c1
let maybe_reify_comp :
  'uuuuuu3255 .
    'uuuuuu3255 ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun g ->
    fun env ->
      fun c ->
        let c1 = comp_no_args c in
        let uu____3274 =
          let uu____3276 =
            let uu____3277 =
              FStar_All.pipe_right c1 FStar_Syntax_Util.comp_effect_name in
            FStar_All.pipe_right uu____3277
              (FStar_TypeChecker_Env.norm_eff_name env) in
          FStar_All.pipe_right uu____3276
            (FStar_TypeChecker_Env.is_reifiable_effect env) in
        if uu____3274
        then
          FStar_TypeChecker_Env.reify_comp env c1
            FStar_Syntax_Syntax.U_unknown
        else FStar_Syntax_Util.comp_result c1
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t0 ->
      let arg_as_mlty g1 uu____3330 =
        match uu____3330 with
        | (a, uu____3338) ->
            let uu____3343 = is_type g1 a in
            if uu____3343
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_Syntax.MLTY_Erased in
      let fv_app_as_mlty g1 fv args =
        let uu____3364 =
          let uu____3366 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv in
          Prims.op_Negation uu____3366 in
        if uu____3364
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____3371 =
             let uu____3378 =
               let uu____3387 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
               FStar_TypeChecker_Env.lookup_lid uu____3387
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             match uu____3378 with
             | ((uu____3394, fvty), uu____3396) ->
                 let fvty1 =
                   let uu____3402 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant] uu____3402 fvty in
                 FStar_Syntax_Util.arrow_formals fvty1 in
           match uu____3371 with
           | (formals, uu____3404) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args in
               let mlargs1 =
                 let n_args = FStar_List.length args in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3441 = FStar_Util.first_N n_args formals in
                   match uu____3441 with
                   | (uu____3470, rest) ->
                       let uu____3504 =
                         FStar_List.map
                           (fun uu____3514 ->
                              FStar_Extraction_ML_Syntax.MLTY_Erased) rest in
                       FStar_List.append mlargs uu____3504
                 else mlargs in
               let nm =
                 FStar_Extraction_ML_UEnv.mlpath_of_lident g1
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)) in
      let aux env t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_type uu____3538 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3539 ->
            let uu____3540 =
              let uu____3542 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3542 in
            failwith uu____3540
        | FStar_Syntax_Syntax.Tm_delayed uu____3545 ->
            let uu____3560 =
              let uu____3562 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3562 in
            failwith uu____3560
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu____3565 =
              let uu____3567 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3567 in
            failwith uu____3565
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3571 = FStar_Syntax_Util.unfold_lazy i in
            translate_term_to_mlty env uu____3571
        | FStar_Syntax_Syntax.Tm_constant uu____3572 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_quoted uu____3573 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_uvar uu____3580 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_meta (t2, uu____3594) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3599;
               FStar_Syntax_Syntax.index = uu____3600;
               FStar_Syntax_Syntax.sort = t2;_},
             uu____3602)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2, uu____3611) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3617, uu____3618) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let uu____3691 = FStar_Syntax_Subst.open_comp bs c in
            (match uu____3691 with
             | (bs1, c1) ->
                 let uu____3698 = binders_as_ml_binders env bs1 in
                 (match uu____3698 with
                  | (mlbs, env1) ->
                      let t_ret =
                        let uu____3727 =
                          let uu____3728 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv env1 in
                          maybe_reify_comp env1 uu____3728 c1 in
                        translate_term_to_mlty env1 uu____3727 in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____3730 =
                        FStar_List.fold_right
                          (fun uu____3750 ->
                             fun uu____3751 ->
                               match (uu____3750, uu____3751) with
                               | ((uu____3774, t2), (tag, t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret) in
                      (match uu____3730 with | (uu____3789, t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head, args) ->
            let res =
              let uu____3818 =
                let uu____3819 = FStar_Syntax_Util.un_uinst head in
                uu____3819.FStar_Syntax_Syntax.n in
              match uu____3818 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head1, args') ->
                  let uu____3850 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head1, (FStar_List.append args' args)))
                      t1.FStar_Syntax_Syntax.pos in
                  translate_term_to_mlty env uu____3850
              | uu____3871 -> FStar_Extraction_ML_Syntax.MLTY_Top in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____3874) ->
            let uu____3899 = FStar_Syntax_Subst.open_term bs ty in
            (match uu____3899 with
             | (bs1, ty1) ->
                 let uu____3906 = binders_as_ml_binders env bs1 in
                 (match uu____3906 with
                  | (bts, env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____3934 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_match uu____3948 ->
            FStar_Extraction_ML_Syntax.MLTY_Top in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____3980 ->
            let uu____3987 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____3987 with
             | FStar_Pervasives_Native.None -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____3993 -> false in
      let uu____3995 =
        let uu____3997 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
        FStar_TypeChecker_Util.must_erase_for_extraction uu____3997 t0 in
      if uu____3995
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0 in
         let uu____4002 = is_top_ty mlt in
         if uu____4002 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)
and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g ->
    fun bs ->
      let uu____4020 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____4077 ->
                fun b ->
                  match uu____4077 with
                  | (ml_bs, env) ->
                      let uu____4123 = is_type_binder g b in
                      if uu____4123
                      then
                        let b1 = FStar_Pervasives_Native.fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1 true in
                        let ml_b =
                          let uu____4146 =
                            FStar_Extraction_ML_UEnv.lookup_ty env1 b1 in
                          uu____4146.FStar_Extraction_ML_UEnv.ty_b_name in
                        let ml_b1 =
                          (ml_b, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b1 :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort in
                         let uu____4172 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false in
                         match uu____4172 with
                         | (env1, b2, uu____4196) ->
                             let ml_b = (b2, t) in ((ml_b :: ml_bs), env1)))
             ([], g)) in
      match uu____4020 with | (ml_bs, env) -> ((FStar_List.rev ml_bs), env)
let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t0 ->
      let t =
        let uu____4281 = extraction_norm_steps () in
        let uu____4282 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
        FStar_TypeChecker_Normalize.normalize uu____4281 uu____4282 t0 in
      translate_term_to_mlty g t
let (mk_MLE_Seq :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun e1 ->
    fun e2 ->
      match ((e1.FStar_Extraction_ML_Syntax.expr),
              (e2.FStar_Extraction_ML_Syntax.expr))
      with
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,
         FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 es2)
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1, uu____4301) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4304, FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4308 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
let (mk_MLE_Let :
  Prims.bool ->
    FStar_Extraction_ML_Syntax.mlletbinding ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun top_level ->
    fun lbs ->
      fun body ->
        match lbs with
        | (FStar_Extraction_ML_Syntax.NonRec, lb::[]) when
            Prims.op_Negation top_level ->
            (match lb.FStar_Extraction_ML_Syntax.mllb_tysc with
             | FStar_Pervasives_Native.Some ([], t) when
                 t = FStar_Extraction_ML_Syntax.ml_unit_ty ->
                 if
                   body.FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                 then
                   (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                 else
                   (match body.FStar_Extraction_ML_Syntax.expr with
                    | FStar_Extraction_ML_Syntax.MLE_Var x when
                        x = lb.FStar_Extraction_ML_Syntax.mllb_name ->
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                    | uu____4342 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4343 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4344 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4353 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
let record_fields :
  'a .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Ident.lident ->
        FStar_Ident.ident Prims.list ->
          'a Prims.list ->
            (FStar_Extraction_ML_Syntax.mlsymbol * 'a) Prims.list
  =
  fun g ->
    fun ty ->
      fun fns ->
        fun xs ->
          let fns1 =
            FStar_List.map
              (fun x ->
                 FStar_Extraction_ML_UEnv.lookup_record_field_name g (ty, x))
              fns in
          FStar_List.map2
            (fun uu____4429 ->
               fun x -> match uu____4429 with | (p, s) -> (s, x)) fns1 xs
let (resugar_pat :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlpattern ->
        FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun g ->
    fun q ->
      fun p ->
        match p with
        | FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) ->
            let uu____4481 = FStar_Extraction_ML_Util.is_xtuple d in
            (match uu____4481 with
             | FStar_Pervasives_Native.Some n ->
                 FStar_Extraction_ML_Syntax.MLP_Tuple pats
             | uu____4488 ->
                 (match q with
                  | FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor (ty, fns)) ->
                      let path =
                        let uu____4502 = FStar_Ident.ns_of_lid ty in
                        FStar_List.map FStar_Ident.string_of_id uu____4502 in
                      let fs = record_fields g ty fns pats in
                      FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                  | uu____4524 -> p))
        | uu____4527 -> p
let rec (extract_one_pat :
  Prims.bool ->
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.pat ->
        FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option ->
          (FStar_Extraction_ML_UEnv.uenv ->
             FStar_Syntax_Syntax.term ->
               (FStar_Extraction_ML_Syntax.mlexpr *
                 FStar_Extraction_ML_Syntax.e_tag *
                 FStar_Extraction_ML_Syntax.mlty))
            ->
            (FStar_Extraction_ML_UEnv.uenv *
              (FStar_Extraction_ML_Syntax.mlpattern *
              FStar_Extraction_ML_Syntax.mlexpr Prims.list)
              FStar_Pervasives_Native.option * Prims.bool))
  =
  fun imp ->
    fun g ->
      fun p ->
        fun expected_topt ->
          fun term_as_mlexpr ->
            let ok t =
              match expected_topt with
              | FStar_Pervasives_Native.None -> true
              | FStar_Pervasives_Native.Some t' ->
                  let ok = type_leq g t t' in
                  (if Prims.op_Negation ok
                   then
                     FStar_Extraction_ML_UEnv.debug g
                       (fun uu____4629 ->
                          let uu____4630 =
                            let uu____4632 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4632 t' in
                          let uu____4633 =
                            let uu____4635 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4635 t in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4630 uu____4633)
                   else ();
                   ok) in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c, swopt)) when
                let uu____4670 = FStar_Options.codegen () in
                uu____4670 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4675 =
                  match swopt with
                  | FStar_Pervasives_Native.None ->
                      let uu____4688 =
                        let uu____4689 =
                          let uu____4690 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None)) in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4690 in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4689 in
                      (uu____4688, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        let uu____4712 =
                          let uu____4713 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                          uu____4713.FStar_TypeChecker_Env.dsenv in
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          uu____4712 c sw FStar_Range.dummyRange in
                      let uu____4714 = term_as_mlexpr g source_term in
                      (match uu____4714 with
                       | (mlterm, uu____4726, mlty) -> (mlterm, mlty)) in
                (match uu____4675 with
                 | (mlc, ml_ty) ->
                     let uu____4745 = FStar_Extraction_ML_UEnv.new_mlident g in
                     (match uu____4745 with
                      | (g1, x) ->
                          let when_clause =
                            let uu____4771 =
                              let uu____4772 =
                                let uu____4779 =
                                  let uu____4782 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         ml_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Var x) in
                                  [uu____4782; mlc] in
                                (FStar_Extraction_ML_Util.prims_op_equality,
                                  uu____4779) in
                              FStar_Extraction_ML_Syntax.MLE_App uu____4772 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_bool_ty)
                              uu____4771 in
                          let uu____4785 = ok ml_ty in
                          (g1,
                            (FStar_Pervasives_Native.Some
                               ((FStar_Extraction_ML_Syntax.MLP_Var x),
                                 [when_clause])), uu____4785)))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  let uu____4806 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                  FStar_TypeChecker_TcTerm.tc_constant uu____4806
                    FStar_Range.dummyRange s in
                let mlty = term_as_mlty g t in
                let uu____4808 =
                  let uu____4817 =
                    let uu____4824 =
                      let uu____4825 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4825 in
                    (uu____4824, []) in
                  FStar_Pervasives_Native.Some uu____4817 in
                let uu____4834 = ok mlty in (g, uu____4808, uu____4834)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____4847 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false imp in
                (match uu____4847 with
                 | (g1, x1, uu____4874) ->
                     let uu____4877 = ok mlty in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4877))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____4915 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false imp in
                (match uu____4915 with
                 | (g1, x1, uu____4942) ->
                     let uu____4945 = ok mlty in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4945))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4981 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f, pats) ->
                let uu____5024 =
                  let uu____5033 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                  match uu____5033 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____5042;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n;
                          FStar_Extraction_ML_Syntax.mlty = uu____5044;
                          FStar_Extraction_ML_Syntax.loc = uu____5045;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;_} ->
                      (n, ttys)
                  | uu____5052 -> failwith "Expected a constructor" in
                (match uu____5024 with
                 | (d, tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys) in
                     let uu____5089 = FStar_Util.first_N nTyVars pats in
                     (match uu____5089 with
                      | (tysVarPats, restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___852_5193 ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____5224 ->
                                               match uu____5224 with
                                               | (p1, uu____5231) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5234, t) ->
                                                        term_as_mlty g t
                                                    | uu____5240 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5244 ->
                                                              let uu____5245
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5245);
                                                         FStar_Exn.raise
                                                           Un_extractable)))) in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args in
                                     let uu____5249 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty in
                                     FStar_Pervasives_Native.Some uu____5249)
                                ()
                            with
                            | Un_extractable -> FStar_Pervasives_Native.None in
                          let uu____5278 =
                            FStar_Util.fold_map
                              (fun g1 ->
                                 fun uu____5315 ->
                                   match uu____5315 with
                                   | (p1, imp1) ->
                                       let uu____5337 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr in
                                       (match uu____5337 with
                                        | (g2, p2, uu____5368) -> (g2, p2)))
                              g tysVarPats in
                          (match uu____5278 with
                           | (g1, tyMLPats) ->
                               let uu____5432 =
                                 FStar_Util.fold_map
                                   (fun uu____5497 ->
                                      fun uu____5498 ->
                                        match (uu____5497, uu____5498) with
                                        | ((g2, f_ty_opt1), (p1, imp1)) ->
                                            let uu____5596 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd::rest, res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd))
                                              | uu____5656 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None) in
                                            (match uu____5596 with
                                             | (f_ty_opt2, expected_ty) ->
                                                 let uu____5727 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr in
                                                 (match uu____5727 with
                                                  | (g3, p2, uu____5770) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats in
                               (match uu____5432 with
                                | ((g2, f_ty_opt1), restMLPats) ->
                                    let uu____5891 =
                                      let uu____5902 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5953 ->
                                                match uu___0_5953 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____5995 -> [])) in
                                      FStar_All.pipe_right uu____5902
                                        FStar_List.split in
                                    (match uu____5891 with
                                     | (mlPats, when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([], t) -> ok t
                                           | uu____6071 -> false in
                                         let uu____6081 =
                                           let uu____6090 =
                                             let uu____6097 =
                                               resugar_pat g2
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats)) in
                                             let uu____6100 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten in
                                             (uu____6097, uu____6100) in
                                           FStar_Pervasives_Native.Some
                                             uu____6090 in
                                         (g2, uu____6081, pat_ty_compat))))))
let (extract_pat :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.pat ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_UEnv.uenv ->
           FStar_Syntax_Syntax.term ->
             (FStar_Extraction_ML_Syntax.mlexpr *
               FStar_Extraction_ML_Syntax.e_tag *
               FStar_Extraction_ML_Syntax.mlty))
          ->
          (FStar_Extraction_ML_UEnv.uenv *
            (FStar_Extraction_ML_Syntax.mlpattern *
            FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option)
            Prims.list * Prims.bool))
  =
  fun g ->
    fun p ->
      fun expected_t ->
        fun term_as_mlexpr ->
          let extract_one_pat1 g1 p1 expected_t1 =
            let uu____6232 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr in
            match uu____6232 with
            | (g2, FStar_Pervasives_Native.Some (x, v), b) -> (g2, (x, v), b)
            | uu____6295 ->
                failwith "Impossible: Unable to translate pattern" in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd::tl ->
                let uu____6343 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl in
                FStar_Pervasives_Native.Some uu____6343 in
          let uu____6344 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t) in
          match uu____6344 with
          | (g1, (p1, whens), b) ->
              let when_clause = mk_when_clause whens in
              (g1, [(p1, when_clause)], b)
let (maybe_eta_data_and_project_record :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun qual ->
      fun residualType ->
        fun mlAppExpr ->
          let rec eta_args g1 more_args t =
            match t with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____6509, t1) ->
                let uu____6511 = FStar_Extraction_ML_UEnv.new_mlident g1 in
                (match uu____6511 with
                 | (g2, x) ->
                     let uu____6536 =
                       let uu____6548 =
                         let uu____6558 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty t0)
                             (FStar_Extraction_ML_Syntax.MLE_Var x) in
                         ((x, t0), uu____6558) in
                       uu____6548 :: more_args in
                     eta_args g2 uu____6536 t1)
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6574, uu____6575)
                -> ((FStar_List.rev more_args), t)
            | uu____6600 ->
                let uu____6601 =
                  let uu____6603 =
                    let uu____6605 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1 in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu____6605
                      mlAppExpr in
                  let uu____6606 =
                    let uu____6608 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1 in
                    FStar_Extraction_ML_Code.string_of_mlty uu____6608 t in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6603 uu____6606 in
                failwith uu____6601 in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____6642, args),
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
               (tyname, fields))) ->
                let path =
                  let uu____6660 = FStar_Ident.ns_of_lid tyname in
                  FStar_List.map FStar_Ident.string_of_id uu____6660 in
                let fields1 = record_fields g tyname fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6682 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____6704 = eta_args g [] residualType in
            match uu____6704 with
            | (eargs, tres) ->
                (match eargs with
                 | [] ->
                     let uu____6762 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____6762
                 | uu____6763 ->
                     let uu____6775 = FStar_List.unzip eargs in
                     (match uu____6775 with
                      | (binders, eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head, args)
                               ->
                               let body =
                                 let uu____6821 =
                                   let uu____6822 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6822 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6821 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6832 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6836, FStar_Pervasives_Native.None) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6840;
                FStar_Extraction_ML_Syntax.loc = uu____6841;_},
              mle::args),
             FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname, f))) ->
              let fn =
                let uu____6853 =
                  let uu____6858 =
                    let uu____6859 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6859
                      constrname in
                  (uu____6858, f) in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6853 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____6862 ->
                    let uu____6865 =
                      let uu____6872 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____6872, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6865 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6876;
                     FStar_Extraction_ML_Syntax.loc = uu____6877;_},
                   uu____6878);
                FStar_Extraction_ML_Syntax.mlty = uu____6879;
                FStar_Extraction_ML_Syntax.loc = uu____6880;_},
              mle::args),
             FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname, f))) ->
              let fn =
                let uu____6896 =
                  let uu____6901 =
                    let uu____6902 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6902
                      constrname in
                  (uu____6901, f) in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6896 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____6905 ->
                    let uu____6908 =
                      let uu____6915 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____6915, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6908 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6919;
                FStar_Extraction_ML_Syntax.loc = uu____6920;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____6928 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6928
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6932;
                FStar_Extraction_ML_Syntax.loc = uu____6933;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____6935)) ->
              let uu____6948 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6948
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6952;
                     FStar_Extraction_ML_Syntax.loc = uu____6953;_},
                   uu____6954);
                FStar_Extraction_ML_Syntax.mlty = uu____6955;
                FStar_Extraction_ML_Syntax.loc = uu____6956;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____6968 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6968
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6972;
                     FStar_Extraction_ML_Syntax.loc = uu____6973;_},
                   uu____6974);
                FStar_Extraction_ML_Syntax.mlty = uu____6975;
                FStar_Extraction_ML_Syntax.loc = uu____6976;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____6978)) ->
              let uu____6995 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6995
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____7001 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7001
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____7005)) ->
              let uu____7014 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7014
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7018;
                FStar_Extraction_ML_Syntax.loc = uu____7019;_},
              uu____7020),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____7027 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7027
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7031;
                FStar_Extraction_ML_Syntax.loc = uu____7032;_},
              uu____7033),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____7034)) ->
              let uu____7047 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7047
          | uu____7050 -> mlAppExpr
let (maybe_promote_effect :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_Syntax.mlexpr *
          FStar_Extraction_ML_Syntax.e_tag))
  =
  fun ml_e ->
    fun tag ->
      fun t ->
        match (tag, t) with
        | (FStar_Extraction_ML_Syntax.E_GHOST,
           FStar_Extraction_ML_Syntax.MLTY_Erased) ->
            (FStar_Extraction_ML_Syntax.ml_unit,
              FStar_Extraction_ML_Syntax.E_PURE)
        | (FStar_Extraction_ML_Syntax.E_PURE,
           FStar_Extraction_ML_Syntax.MLTY_Erased) ->
            (FStar_Extraction_ML_Syntax.ml_unit,
              FStar_Extraction_ML_Syntax.E_PURE)
        | uu____7081 -> (ml_e, tag)
let (extract_lb_sig :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.letbindings ->
      (FStar_Syntax_Syntax.lbname * FStar_Extraction_ML_Syntax.e_tag *
        (FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.binders *
        FStar_Extraction_ML_Syntax.mltyscheme)) * Prims.bool *
        FStar_Syntax_Syntax.term) Prims.list)
  =
  fun g ->
    fun lbs ->
      let maybe_generalize uu____7142 =
        match uu____7142 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____7163;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____7168;_} ->
            let f_e = effect_as_etag g lbeff in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp in
            let no_gen uu____7249 =
              let expected_t = term_as_mlty g lbtyp1 in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef) in
            let uu____7326 =
              let uu____7328 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
              FStar_TypeChecker_Util.must_erase_for_extraction uu____7328
                lbtyp1 in
            if uu____7326
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                   let uu____7413 = FStar_List.hd bs in
                   FStar_All.pipe_right uu____7413 (is_type_binder g) ->
                   let uu____7435 = FStar_Syntax_Subst.open_comp bs c in
                   (match uu____7435 with
                    | (bs1, c1) ->
                        let uu____7461 =
                          let uu____7474 =
                            FStar_Util.prefix_until
                              (fun x ->
                                 let uu____7520 = is_type_binder g x in
                                 Prims.op_Negation uu____7520) bs1 in
                          match uu____7474 with
                          | FStar_Pervasives_Native.None ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2, b, rest) ->
                              let uu____7647 =
                                FStar_Syntax_Util.arrow (b :: rest) c1 in
                              (bs2, uu____7647) in
                        (match uu____7461 with
                         | (tbinders, tbody) ->
                             let n_tbinders = FStar_List.length tbinders in
                             let lbdef1 =
                               let uu____7709 = normalize_abs lbdef in
                               FStar_All.pipe_right uu____7709
                                 FStar_Syntax_Util.unmeta in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2, body, copt)
                                  ->
                                  let uu____7758 =
                                    FStar_Syntax_Subst.open_term bs2 body in
                                  (match uu____7758 with
                                   | (bs3, body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7810 =
                                           FStar_Util.first_N n_tbinders bs3 in
                                         (match uu____7810 with
                                          | (targs, rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7913 ->
                                                       fun uu____7914 ->
                                                         match (uu____7913,
                                                                 uu____7914)
                                                         with
                                                         | ((x, uu____7940),
                                                            (y, uu____7942))
                                                             ->
                                                             let uu____7963 =
                                                               let uu____7970
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y in
                                                               (x,
                                                                 uu____7970) in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7963)
                                                    tbinders targs in
                                                FStar_Syntax_Subst.subst s
                                                  tbody in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env ->
                                                     fun uu____7987 ->
                                                       match uu____7987 with
                                                       | (a, uu____7995) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a false) g
                                                  targs in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty in
                                              let polytype =
                                                let uu____8007 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____8027 ->
                                                          match uu____8027
                                                          with
                                                          | (x, uu____8036)
                                                              ->
                                                              let uu____8041
                                                                =
                                                                FStar_Extraction_ML_UEnv.lookup_ty
                                                                  env x in
                                                              uu____8041.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                                (uu____8007, expected_t) in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____8053 =
                                                       is_fstar_value body1 in
                                                     Prims.op_Negation
                                                       uu____8053)
                                                      ||
                                                      (let uu____8056 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1 in
                                                       Prims.op_Negation
                                                         uu____8056)
                                                | uu____8058 -> false in
                                              let rest_args1 =
                                                if add_unit
                                                then
                                                  let uu____8070 =
                                                    unit_binder () in
                                                  uu____8070 :: rest_args
                                                else rest_args in
                                              let polytype1 =
                                                if add_unit
                                                then
                                                  FStar_Extraction_ML_Syntax.push_unit
                                                    polytype
                                                else polytype in
                                              let body2 =
                                                FStar_Syntax_Util.abs
                                                  rest_args1 body1 copt in
                                              (lbname_, f_e,
                                                (lbtyp1, (targs, polytype1)),
                                                add_unit, body2))
                                       else
                                         failwith "Not enough type binders")
                              | FStar_Syntax_Syntax.Tm_uinst uu____8127 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env ->
                                         fun uu____8146 ->
                                           match uu____8146 with
                                           | (a, uu____8154) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu____8166 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8186 ->
                                              match uu____8186 with
                                              | (x, uu____8195) ->
                                                  let uu____8200 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x in
                                                  uu____8200.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                    (uu____8166, expected_t) in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8240 ->
                                            match uu____8240 with
                                            | (bv, uu____8248) ->
                                                let uu____8253 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_All.pipe_right
                                                  uu____8253
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | FStar_Syntax_Syntax.Tm_fvar uu____8283 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env ->
                                         fun uu____8296 ->
                                           match uu____8296 with
                                           | (a, uu____8304) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu____8316 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8336 ->
                                              match uu____8336 with
                                              | (x, uu____8345) ->
                                                  let uu____8350 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x in
                                                  uu____8350.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                    (uu____8316, expected_t) in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8390 ->
                                            match uu____8390 with
                                            | (bv, uu____8398) ->
                                                let uu____8403 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_All.pipe_right
                                                  uu____8403
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | FStar_Syntax_Syntax.Tm_name uu____8433 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env ->
                                         fun uu____8446 ->
                                           match uu____8446 with
                                           | (a, uu____8454) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu____8466 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8486 ->
                                              match uu____8486 with
                                              | (x, uu____8495) ->
                                                  let uu____8500 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x in
                                                  uu____8500.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                    (uu____8466, expected_t) in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8540 ->
                                            match uu____8540 with
                                            | (bv, uu____8548) ->
                                                let uu____8553 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_All.pipe_right
                                                  uu____8553
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | uu____8583 -> err_value_restriction lbdef1)))
               | uu____8603 -> no_gen ()) in
      FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
        (FStar_List.map maybe_generalize)
let (extract_lb_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.letbindings ->
      (FStar_Extraction_ML_UEnv.uenv * (FStar_Syntax_Syntax.fv *
        FStar_Extraction_ML_UEnv.exp_binding) Prims.list))
  =
  fun g ->
    fun lbs ->
      let is_top =
        FStar_Syntax_Syntax.is_top_level (FStar_Pervasives_Native.snd lbs) in
      let is_rec =
        (Prims.op_Negation is_top) && (FStar_Pervasives_Native.fst lbs) in
      let lbs1 = extract_lb_sig g lbs in
      FStar_Util.fold_map
        (fun env ->
           fun uu____8754 ->
             match uu____8754 with
             | (lbname, e_tag, (typ, (binders, mltyscheme)), add_unit, _body)
                 ->
                 let uu____8815 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit in
                 (match uu____8815 with
                  | (env1, uu____8832, exp_binding) ->
                      let uu____8836 =
                        let uu____8841 = FStar_Util.right lbname in
                        (uu____8841, exp_binding) in
                      (env1, uu____8836))) g lbs1
let rec (check_term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr *
            FStar_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun e ->
      fun f ->
        fun ty ->
          FStar_Extraction_ML_UEnv.debug g
            (fun uu____8908 ->
               let uu____8909 = FStar_Syntax_Print.term_to_string e in
               let uu____8911 =
                 let uu____8913 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g in
                 FStar_Extraction_ML_Code.string_of_mlty uu____8913 ty in
               let uu____8914 = FStar_Extraction_ML_Util.eff_to_string f in
               FStar_Util.print3 "Checking %s at type %s and eff %s\n"
                 uu____8909 uu____8911 uu____8914);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST, uu____8921) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE,
              FStar_Extraction_ML_Syntax.MLTY_Erased) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8922 ->
               let uu____8927 = term_as_mlexpr g e in
               (match uu____8927 with
                | (ml_e, tag, t) ->
                    let uu____8941 = FStar_Extraction_ML_Util.eff_leq tag f in
                    if uu____8941
                    then
                      let uu____8948 =
                        maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t ty in
                      (uu____8948, ty)
                    else
                      (match (tag, f, ty) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST,
                          FStar_Extraction_ML_Syntax.E_PURE,
                          FStar_Extraction_ML_Syntax.MLTY_Erased) ->
                           let uu____8955 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t
                               ty in
                           (uu____8955, ty)
                       | uu____8956 ->
                           (err_unexpected_eff g e ty f tag;
                            (let uu____8964 =
                               maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e
                                 t ty in
                             (uu____8964, ty))))))
and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun e ->
      let uu____8973 = term_as_mlexpr' g e in
      match uu____8973 with
      | (e1, f, t) ->
          let uu____8989 = maybe_promote_effect e1 f t in
          (match uu____8989 with | (e2, f1) -> (e2, f1, t))
and (term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun top ->
      let top1 = FStar_Syntax_Subst.compress top in
      FStar_Extraction_ML_UEnv.debug g
        (fun u ->
           let uu____9015 =
             let uu____9017 =
               FStar_Range.string_of_range top1.FStar_Syntax_Syntax.pos in
             let uu____9019 = FStar_Syntax_Print.tag_of_term top1 in
             let uu____9021 = FStar_Syntax_Print.term_to_string top1 in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____9017 uu____9019 uu____9021 in
           FStar_Util.print_string uu____9015);
      (let is_match t =
         let uu____9031 =
           let uu____9032 =
             let uu____9035 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress in
             FStar_All.pipe_right uu____9035 FStar_Syntax_Util.unascribe in
           uu____9032.FStar_Syntax_Syntax.n in
         match uu____9031 with
         | FStar_Syntax_Syntax.Tm_match uu____9039 -> true
         | uu____9063 -> false in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____9082 ->
              match uu____9082 with
              | (t, uu____9091) ->
                  let uu____9096 =
                    let uu____9097 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress in
                    uu____9097.FStar_Syntax_Syntax.n in
                  (match uu____9096 with
                   | FStar_Syntax_Syntax.Tm_name uu____9103 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____9105 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____9107 -> true
                   | uu____9109 -> false)) in
       let apply_to_match_branches head args =
         let uu____9148 =
           let uu____9149 =
             let uu____9152 =
               FStar_All.pipe_right head FStar_Syntax_Subst.compress in
             FStar_All.pipe_right uu____9152 FStar_Syntax_Util.unascribe in
           uu____9149.FStar_Syntax_Syntax.n in
         match uu____9148 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee, branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____9276 ->
                       match uu____9276 with
                       | (pat, when_opt, body) ->
                           (pat, when_opt,
                             (let uu___1319_9333 = body in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1319_9333.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1319_9333.FStar_Syntax_Syntax.vars)
                              })))) in
             let uu___1322_9348 = head in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1322_9348.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1322_9348.FStar_Syntax_Syntax.vars)
             }
         | uu____9369 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match" in
       let t = FStar_Syntax_Subst.compress top1 in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu____9380 =
             let uu____9382 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9382 in
           failwith uu____9380
       | FStar_Syntax_Syntax.Tm_delayed uu____9391 ->
           let uu____9406 =
             let uu____9408 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9408 in
           failwith uu____9406
       | FStar_Syntax_Syntax.Tm_uvar uu____9417 ->
           let uu____9430 =
             let uu____9432 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9432 in
           failwith uu____9430
       | FStar_Syntax_Syntax.Tm_bvar uu____9441 ->
           let uu____9442 =
             let uu____9444 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9444 in
           failwith uu____9442
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9454 = FStar_Syntax_Util.unfold_lazy i in
           term_as_mlexpr g uu____9454
       | FStar_Syntax_Syntax.Tm_type uu____9455 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9456 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9463 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
              FStar_Syntax_Syntax.antiquotes = uu____9479;_})
           ->
           let uu____9492 =
             let uu____9493 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9493 in
           (match uu____9492 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9500;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9502;_} ->
                let uu____9504 =
                  let uu____9505 =
                    let uu____9506 =
                      let uu____9513 =
                        let uu____9516 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime")) in
                        [uu____9516] in
                      (fw, uu____9513) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9506 in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9505 in
                (uu____9504, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
              FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9534 = FStar_Reflection_Basic.inspect_ln qt in
           (match uu____9534 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9542 = FStar_Syntax_Syntax.lookup_aq bv aqs in
                (match uu____9542 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None ->
                     let tv =
                       let uu____9553 =
                         let uu____9560 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs in
                         FStar_Syntax_Embeddings.embed uu____9560
                           (FStar_Reflection_Data.Tv_Var bv) in
                       uu____9553 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb in
                     let t1 =
                       let uu____9568 =
                         let uu____9579 = FStar_Syntax_Syntax.as_arg tv in
                         [uu____9579] in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9568 in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9606 =
                    let uu____9613 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs in
                    FStar_Syntax_Embeddings.embed uu____9613 tv in
                  uu____9606 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb in
                let t1 =
                  let uu____9621 =
                    let uu____9632 = FStar_Syntax_Syntax.as_arg tv1 in
                    [uu____9632] in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9621 in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____9659)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9692 =
                  let uu____9699 =
                    let uu____9708 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Env.effect_decl_opt uu____9708 m in
                  FStar_Util.must uu____9699 in
                (match uu____9692 with
                 | (ed, qualifiers) ->
                     let uu____9727 =
                       let uu____9729 =
                         let uu____9731 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                         FStar_TypeChecker_Env.is_reifiable_effect uu____9731
                           ed.FStar_Syntax_Syntax.mname in
                       Prims.op_Negation uu____9729 in
                     if uu____9727
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9748 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1, uu____9750) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1, uu____9756) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9762 =
             let uu____9769 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
             FStar_TypeChecker_TcTerm.type_of_tot_term uu____9769 t in
           (match uu____9762 with
            | (uu____9776, ty, uu____9778) ->
                let ml_ty = term_as_mlty g ty in
                let uu____9780 =
                  let uu____9781 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9781 in
                (uu____9780, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9782 ->
           let uu____9783 = is_type g t in
           if uu____9783
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9794 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____9794 with
              | (FStar_Util.Inl uu____9807, uu____9808) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9813;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_},
                 qual) ->
                  (match mltys with
                   | ([], t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([], t1) ->
                       let uu____9832 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____9832, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9833 -> instantiate_maybe_partial g x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9835 = is_type g t in
           if uu____9835
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9846 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv in
              match uu____9846 with
              | FStar_Pervasives_Native.None ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9855;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9864 ->
                        let uu____9865 = FStar_Syntax_Print.fv_to_string fv in
                        let uu____9867 =
                          let uu____9869 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g in
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            uu____9869 x in
                        let uu____9870 =
                          let uu____9872 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g in
                          FStar_Extraction_ML_Code.string_of_mlty uu____9872
                            (FStar_Pervasives_Native.snd mltys) in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9865 uu____9867 uu____9870);
                   (match mltys with
                    | ([], t1) when
                        t1 = FStar_Extraction_ML_Syntax.ml_unit_ty ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([], t1) ->
                        let uu____9884 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x in
                        (uu____9884, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9885 -> instantiate_maybe_partial g x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs, body, rcopt) ->
           let uu____9913 = FStar_Syntax_Subst.open_term bs body in
           (match uu____9913 with
            | (bs1, body1) ->
                let uu____9926 = binders_as_ml_binders g bs1 in
                (match uu____9926 with
                 | (ml_bs, env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9962 =
                             let uu____9964 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
                             FStar_TypeChecker_Env.is_reifiable_rc uu____9964
                               rc in
                           if uu____9962
                           then
                             let uu____9966 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
                             FStar_TypeChecker_Util.reify_body uu____9966
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Unascribe] body1
                           else body1
                       | FStar_Pervasives_Native.None ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9972 ->
                                 let uu____9973 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9973);
                            body1) in
                     let uu____9976 = term_as_mlexpr env body2 in
                     (match uu____9976 with
                      | (ml_body, f, t1) ->
                          let uu____9992 =
                            FStar_List.fold_right
                              (fun uu____10012 ->
                                 fun uu____10013 ->
                                   match (uu____10012, uu____10013) with
                                   | ((uu____10036, targ), (f1, t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____9992 with
                           | (f1, tfun) ->
                               let uu____10059 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____10059, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____10067;
              FStar_Syntax_Syntax.vars = uu____10068;_},
            (a1, uu____10070)::[])
           ->
           let ty =
             let uu____10110 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
             term_as_mlty g uu____10110 in
           let uu____10111 =
             let uu____10112 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____10112 in
           (uu____10111, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____10113;
              FStar_Syntax_Syntax.vars = uu____10114;_},
            (t1, uu____10116)::(r, uu____10118)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____10173);
              FStar_Syntax_Syntax.pos = uu____10174;
              FStar_Syntax_Syntax.vars = uu____10175;_},
            uu____10176)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head, args) when
           (is_match head) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____10235 =
             FStar_All.pipe_right args (apply_to_match_branches head) in
           FStar_All.pipe_right uu____10235 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head, args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_10289 ->
                        match uu___1_10289 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | uu____10292 -> false))) in
           let uu____10294 =
             let uu____10295 =
               let uu____10298 =
                 FStar_All.pipe_right head FStar_Syntax_Subst.compress in
               FStar_All.pipe_right uu____10298 FStar_Syntax_Util.unascribe in
             uu____10295.FStar_Syntax_Syntax.n in
           (match uu____10294 with
            | FStar_Syntax_Syntax.Tm_abs (bs, uu____10308, _rc) ->
                let uu____10334 =
                  let uu____10335 =
                    let uu____10340 =
                      FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses]
                      uu____10340 in
                  FStar_All.pipe_right t uu____10335 in
                FStar_All.pipe_right uu____10334 (term_as_mlexpr g)
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
                let e =
                  let uu____10348 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                  let uu____10349 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg uu____10348
                    [FStar_TypeChecker_Env.Inlining;
                    FStar_TypeChecker_Env.Unascribe] head uu____10349 in
                let tm =
                  let uu____10359 = FStar_TypeChecker_Util.remove_reify e in
                  let uu____10360 = FStar_List.tl args in
                  FStar_Syntax_Syntax.mk_Tm_app uu____10359 uu____10360
                    t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr g tm
            | uu____10369 ->
                let rec extract_app is_data uu____10418 uu____10419 restArgs
                  =
                  match (uu____10418, uu____10419) with
                  | ((mlhead, mlargs_f), (f, t1)) ->
                      let mk_head uu____10500 =
                        let mlargs =
                          FStar_All.pipe_right (FStar_List.rev mlargs_f)
                            (FStar_List.map FStar_Pervasives_Native.fst) in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty t1)
                          (FStar_Extraction_ML_Syntax.MLE_App
                             (mlhead, mlargs)) in
                      (FStar_Extraction_ML_UEnv.debug g
                         (fun uu____10527 ->
                            let uu____10528 =
                              let uu____10530 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g in
                              let uu____10531 = mk_head () in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____10530 uu____10531 in
                            let uu____10532 =
                              let uu____10534 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g in
                              FStar_Extraction_ML_Code.string_of_mlty
                                uu____10534 t1 in
                            let uu____10535 =
                              match restArgs with
                              | [] -> "none"
                              | (hd, uu____10546)::uu____10547 ->
                                  FStar_Syntax_Print.term_to_string hd in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10528 uu____10532 uu____10535);
                       (match (restArgs, t1) with
                        | ([], uu____10581) ->
                            let app =
                              let uu____10597 = mk_head () in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10597 in
                            (app, f, t1)
                        | ((arg, uu____10599)::rest,
                           FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t, f', t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10630 =
                              let uu____10635 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f' in
                              (uu____10635, t2) in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10630 rest
                        | ((e0, uu____10647)::rest,
                           FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected, f', t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos in
                            let expected_effect =
                              let uu____10680 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head) in
                              if uu____10680
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE in
                            let uu____10685 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected in
                            (match uu____10685 with
                             | (e01, tInferred) ->
                                 let uu____10698 =
                                   let uu____10703 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f'] in
                                   (uu____10703, t2) in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10698 rest)
                        | uu____10714 ->
                            let uu____10727 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1 in
                            (match uu____10727 with
                             | FStar_Pervasives_Native.Some t2 ->
                                 extract_app is_data (mlhead, mlargs_f)
                                   (f, t2) restArgs
                             | FStar_Pervasives_Native.None ->
                                 (match t1 with
                                  | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                                      (FStar_Extraction_ML_Syntax.ml_unit,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        t1)
                                  | FStar_Extraction_ML_Syntax.MLTY_Top ->
                                      let t2 =
                                        FStar_List.fold_right
                                          (fun t2 ->
                                             fun out ->
                                               FStar_Extraction_ML_Syntax.MLTY_Fun
                                                 (FStar_Extraction_ML_Syntax.MLTY_Top,
                                                   FStar_Extraction_ML_Syntax.E_PURE,
                                                   out)) restArgs
                                          FStar_Extraction_ML_Syntax.MLTY_Top in
                                      let mlhead1 =
                                        let mlargs =
                                          FStar_All.pipe_right
                                            (FStar_List.rev mlargs_f)
                                            (FStar_List.map
                                               FStar_Pervasives_Native.fst) in
                                        let head1 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.MLTY_Top)
                                            (FStar_Extraction_ML_Syntax.MLE_App
                                               (mlhead, mlargs)) in
                                        maybe_coerce
                                          top1.FStar_Syntax_Syntax.pos g
                                          head1
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t2 in
                                      extract_app is_data (mlhead1, [])
                                        (f, t2) restArgs
                                  | uu____10799 ->
                                      let mlhead1 =
                                        let mlargs =
                                          FStar_All.pipe_right
                                            (FStar_List.rev mlargs_f)
                                            (FStar_List.map
                                               FStar_Pervasives_Native.fst) in
                                        let head1 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.MLTY_Top)
                                            (FStar_Extraction_ML_Syntax.MLE_App
                                               (mlhead, mlargs)) in
                                        maybe_coerce
                                          top1.FStar_Syntax_Syntax.pos g
                                          head1
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t1 in
                                      err_ill_typed_application g top1
                                        mlhead1 restArgs t1)))) in
                let extract_app_maybe_projector is_data mlhead uu____10870
                  args1 =
                  match uu____10870 with
                  | (f, t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10900)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10984))::args3,
                                FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____10986, f', t3)) ->
                                 let uu____11024 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____11024 t3
                             | uu____11025 -> (args2, f1, t2) in
                           let uu____11050 = remove_implicits args1 f t1 in
                           (match uu____11050 with
                            | (args2, f1, t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____11106 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let extract_app_with_instantiations uu____11130 =
                  let head1 = FStar_Syntax_Util.un_uinst head in
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____11138 ->
                      let uu____11139 =
                        let uu____11154 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1 in
                        match uu____11154 with
                        | (FStar_Util.Inr exp_b, q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11186 ->
                                  let uu____11187 =
                                    FStar_Syntax_Print.term_to_string head1 in
                                  let uu____11189 =
                                    let uu____11191 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11191
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr in
                                  let uu____11192 =
                                    let uu____11194 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11194
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme) in
                                  FStar_Util.print3
                                    "@@@looked up %s: got %s at %s\n"
                                    uu____11187 uu____11189 uu____11192);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu____11210 -> failwith "FIXME Ty" in
                      (match uu____11139 with
                       | ((head_ml, (vars, t1)), qual) ->
                           let has_typ_apps =
                             match args with
                             | (a, uu____11262)::uu____11263 -> is_type g a
                             | uu____11290 -> false in
                           let uu____11302 =
                             let n = FStar_List.length vars in
                             let uu____11319 =
                               if (FStar_List.length args) <= n
                               then
                                 let uu____11357 =
                                   FStar_List.map
                                     (fun uu____11369 ->
                                        match uu____11369 with
                                        | (x, uu____11377) ->
                                            term_as_mlty g x) args in
                                 (uu____11357, [])
                               else
                                 (let uu____11400 = FStar_Util.first_N n args in
                                  match uu____11400 with
                                  | (prefix, rest) ->
                                      let uu____11489 =
                                        FStar_List.map
                                          (fun uu____11501 ->
                                             match uu____11501 with
                                             | (x, uu____11509) ->
                                                 term_as_mlty g x) prefix in
                                      (uu____11489, rest)) in
                             match uu____11319 with
                             | (provided_type_args, rest) ->
                                 let uu____11560 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu____11569 ->
                                       let uu____11570 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu____11570 with
                                        | (head2, uu____11582, t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu____11584 ->
                                       let uu____11586 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu____11586 with
                                        | (head2, uu____11598, t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head2,
                                        {
                                          FStar_Extraction_ML_Syntax.expr =
                                            FStar_Extraction_ML_Syntax.MLE_Const
                                            (FStar_Extraction_ML_Syntax.MLC_Unit);
                                          FStar_Extraction_ML_Syntax.mlty =
                                            uu____11601;
                                          FStar_Extraction_ML_Syntax.loc =
                                            uu____11602;_}::[])
                                       ->
                                       let uu____11605 =
                                         instantiate_maybe_partial g head2
                                           (vars, t1) provided_type_args in
                                       (match uu____11605 with
                                        | (head3, uu____11617, t2) ->
                                            let uu____11619 =
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head3,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2) in
                                            (uu____11619, t2))
                                   | uu____11622 ->
                                       failwith
                                         "Impossible: Unexpected head term" in
                                 (match uu____11560 with
                                  | (head2, t2) -> (head2, t2, rest)) in
                           (match uu____11302 with
                            | (head_ml1, head_t, args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11689 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1 in
                                     (uu____11689,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11690 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11699 ->
                      let uu____11700 =
                        let uu____11715 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1 in
                        match uu____11715 with
                        | (FStar_Util.Inr exp_b, q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11747 ->
                                  let uu____11748 =
                                    FStar_Syntax_Print.term_to_string head1 in
                                  let uu____11750 =
                                    let uu____11752 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11752
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr in
                                  let uu____11753 =
                                    let uu____11755 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11755
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme) in
                                  FStar_Util.print3
                                    "@@@looked up %s: got %s at %s\n"
                                    uu____11748 uu____11750 uu____11753);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu____11771 -> failwith "FIXME Ty" in
                      (match uu____11700 with
                       | ((head_ml, (vars, t1)), qual) ->
                           let has_typ_apps =
                             match args with
                             | (a, uu____11823)::uu____11824 -> is_type g a
                             | uu____11851 -> false in
                           let uu____11863 =
                             let n = FStar_List.length vars in
                             let uu____11880 =
                               if (FStar_List.length args) <= n
                               then
                                 let uu____11918 =
                                   FStar_List.map
                                     (fun uu____11930 ->
                                        match uu____11930 with
                                        | (x, uu____11938) ->
                                            term_as_mlty g x) args in
                                 (uu____11918, [])
                               else
                                 (let uu____11961 = FStar_Util.first_N n args in
                                  match uu____11961 with
                                  | (prefix, rest) ->
                                      let uu____12050 =
                                        FStar_List.map
                                          (fun uu____12062 ->
                                             match uu____12062 with
                                             | (x, uu____12070) ->
                                                 term_as_mlty g x) prefix in
                                      (uu____12050, rest)) in
                             match uu____11880 with
                             | (provided_type_args, rest) ->
                                 let uu____12121 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu____12130 ->
                                       let uu____12131 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu____12131 with
                                        | (head2, uu____12143, t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu____12145 ->
                                       let uu____12147 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu____12147 with
                                        | (head2, uu____12159, t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head2,
                                        {
                                          FStar_Extraction_ML_Syntax.expr =
                                            FStar_Extraction_ML_Syntax.MLE_Const
                                            (FStar_Extraction_ML_Syntax.MLC_Unit);
                                          FStar_Extraction_ML_Syntax.mlty =
                                            uu____12162;
                                          FStar_Extraction_ML_Syntax.loc =
                                            uu____12163;_}::[])
                                       ->
                                       let uu____12166 =
                                         instantiate_maybe_partial g head2
                                           (vars, t1) provided_type_args in
                                       (match uu____12166 with
                                        | (head3, uu____12178, t2) ->
                                            let uu____12180 =
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head3,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2) in
                                            (uu____12180, t2))
                                   | uu____12183 ->
                                       failwith
                                         "Impossible: Unexpected head term" in
                                 (match uu____12121 with
                                  | (head2, t2) -> (head2, t2, rest)) in
                           (match uu____11863 with
                            | (head_ml1, head_t, args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12250 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1 in
                                     (uu____12250,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12251 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12260 ->
                      let uu____12261 = term_as_mlexpr g head1 in
                      (match uu____12261 with
                       | (head2, f, t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head2 (f, t1) args) in
                let uu____12277 = is_type g t in
                if uu____12277
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12288 =
                     let uu____12289 = FStar_Syntax_Util.un_uinst head in
                     uu____12289.FStar_Syntax_Syntax.n in
                   match uu____12288 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12299 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv in
                       (match uu____12299 with
                        | FStar_Pervasives_Native.None ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12308 -> extract_app_with_instantiations ())
                   | uu____12311 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____12314), f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12379 =
                   let uu____12380 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                   maybe_reify_comp g uu____12380 c in
                 term_as_mlty g uu____12379 in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l in
           let uu____12384 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____12384 with | (e, t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e') when
           (let uu____12416 = FStar_Syntax_Syntax.is_top_level [lb] in
            Prims.op_Negation uu____12416) &&
             (let uu____12419 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs in
              FStar_Util.is_some uu____12419)
           ->
           let b =
             let uu____12429 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
             (uu____12429, FStar_Pervasives_Native.None) in
           let uu____12432 = FStar_Syntax_Subst.open_term_1 b e' in
           (match uu____12432 with
            | ((x, uu____12444), body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str, uu____12459)::[]) ->
                      let uu____12484 =
                        let uu____12485 = FStar_Syntax_Subst.compress str in
                        uu____12485.FStar_Syntax_Syntax.n in
                      (match uu____12484 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s, uu____12491)) ->
                           let id =
                             let uu____12495 =
                               let uu____12501 =
                                 FStar_Syntax_Syntax.range_of_bv x in
                               (s, uu____12501) in
                             FStar_Ident.mk_ident uu____12495 in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             } in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv in
                           FStar_Pervasives_Native.Some bv1
                       | uu____12506 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____12507 ->
                      (FStar_Errors.log_issue top1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `rename_let`");
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None in
                let remove_attr attrs =
                  let uu____12527 =
                    FStar_List.partition
                      (fun attr ->
                         let uu____12539 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr] in
                         FStar_Util.is_some uu____12539)
                      lb.FStar_Syntax_Syntax.lbattrs in
                  match uu____12527 with
                  | (uu____12544, other_attrs) -> other_attrs in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1774_12572 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1774_12572.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1774_12572.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1774_12572.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1774_12572.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1774_12572.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1774_12572.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs in
                      let rename =
                        let uu____12580 =
                          let uu____12581 =
                            let uu____12588 =
                              FStar_Syntax_Syntax.bv_to_name y in
                            (x, uu____12588) in
                          FStar_Syntax_Syntax.NT uu____12581 in
                        [uu____12580] in
                      let body1 =
                        let uu____12594 =
                          FStar_Syntax_Subst.subst rename body in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____12594 in
                      let lb1 =
                        let uu___1781_12610 = lb in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1781_12610.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1781_12610.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1781_12610.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1781_12610.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1781_12610.FStar_Syntax_Syntax.lbpos)
                        } in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1) in
                let top2 =
                  let uu___1785_12627 = top1 in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1785_12627.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1785_12627.FStar_Syntax_Syntax.vars)
                  } in
                term_as_mlexpr' g top2)
       | FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____12650 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12666 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____12666
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____12681 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____12681 in
                   let lb1 =
                     let uu___1799_12683 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1799_12683.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1799_12683.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1799_12683.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1799_12683.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1799_12683.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1799_12683.FStar_Syntax_Syntax.lbpos)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e' in
                   ([lb1], e'1))) in
           (match uu____12650 with
            | (lbs1, e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____12708 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                      let uu____12709 =
                        let uu____12710 =
                          let uu____12711 =
                            let uu____12715 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g in
                            FStar_Pervasives_Native.fst uu____12715 in
                          let uu____12728 =
                            let uu____12732 =
                              let uu____12734 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g in
                              FStar_Pervasives_Native.snd uu____12734 in
                            [uu____12732] in
                          FStar_List.append uu____12711 uu____12728 in
                        FStar_Ident.lid_of_path uu____12710
                          FStar_Range.dummyRange in
                      FStar_TypeChecker_Env.set_current_module uu____12708
                        uu____12709 in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb ->
                            let lbdef =
                              let uu____12761 = FStar_Options.ml_ish () in
                              if uu____12761
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____12773 =
                                   let uu____12774 =
                                     let uu____12775 =
                                       let uu____12778 =
                                         extraction_norm_steps () in
                                       FStar_TypeChecker_Env.Reify ::
                                         uu____12778 in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____12775 in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____12774 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef in
                                 let uu____12781 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm")) in
                                 if uu____12781
                                 then
                                   ((let uu____12791 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____12791);
                                    (let a =
                                       let uu____12797 =
                                         let uu____12799 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____12799 in
                                       FStar_Util.measure_execution_time
                                         uu____12797 norm_call in
                                     a))
                                 else norm_call ()) in
                            let uu___1816_12806 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1816_12806.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1816_12806.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1816_12806.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1816_12806.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1816_12806.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1816_12806.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1 in
                let check_lb env uu____12859 =
                  match uu____12859 with
                  | (nm, (_lbname, f, (_t, (targs, polytype)), add_unit, e))
                      ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1 ->
                             fun uu____13015 ->
                               match uu____13015 with
                               | (a, uu____13023) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     false) env targs in
                      let expected_t = FStar_Pervasives_Native.snd polytype in
                      let uu____13030 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____13030 with
                       | (e1, ty) ->
                           let uu____13041 =
                             maybe_promote_effect e1 f expected_t in
                           (match uu____13041 with
                            | (e2, f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE,
                                     FStar_Extraction_ML_Syntax.MLTY_Erased)
                                      -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST,
                                     FStar_Extraction_ML_Syntax.MLTY_Erased)
                                      -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____13053 -> [] in
                                (f1,
                                  {
                                    FStar_Extraction_ML_Syntax.mllb_name = nm;
                                    FStar_Extraction_ML_Syntax.mllb_tysc =
                                      (FStar_Pervasives_Native.Some polytype);
                                    FStar_Extraction_ML_Syntax.mllb_add_unit
                                      = add_unit;
                                    FStar_Extraction_ML_Syntax.mllb_def = e2;
                                    FStar_Extraction_ML_Syntax.mllb_meta =
                                      meta;
                                    FStar_Extraction_ML_Syntax.print_typ =
                                      true
                                  }))) in
                let lbs3 = extract_lb_sig g (is_rec, lbs2) in
                let uu____13084 =
                  FStar_List.fold_right
                    (fun lb ->
                       fun uu____13181 ->
                         match uu____13181 with
                         | (env, lbs4) ->
                             let uu____13315 = lb in
                             (match uu____13315 with
                              | (lbname, uu____13366,
                                 (t1, (uu____13368, polytype)), add_unit,
                                 uu____13371) ->
                                  let uu____13386 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit in
                                  (match uu____13386 with
                                   | (env1, nm, uu____13426) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, []) in
                (match uu____13084 with
                 | (env_body, lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____13705 = term_as_mlexpr env_body e'1 in
                     (match uu____13705 with
                      | (e'2, f', t') ->
                          let f =
                            let uu____13722 =
                              let uu____13725 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5 in
                              f' :: uu____13725 in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13722 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____13738 =
                            let uu____13739 =
                              let uu____13740 =
                                let uu____13741 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5 in
                                (is_rec1, uu____13741) in
                              mk_MLE_Let top_level uu____13740 e'2 in
                            let uu____13750 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13739 uu____13750 in
                          (uu____13738, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee, pats) ->
           let uu____13789 = term_as_mlexpr g scrutinee in
           (match uu____13789 with
            | (e, f_e, t_e) ->
                let uu____13805 = check_pats_for_ite pats in
                (match uu____13805 with
                 | (b, then_e, else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some then_e1,
                           FStar_Pervasives_Native.Some else_e1) ->
                            let uu____13870 = term_as_mlexpr g then_e1 in
                            (match uu____13870 with
                             | (then_mle, f_then, t_then) ->
                                 let uu____13886 = term_as_mlexpr g else_e1 in
                                 (match uu____13886 with
                                  | (else_mle, f_else, t_else) ->
                                      let uu____13902 =
                                        let uu____13913 =
                                          type_leq g t_then t_else in
                                        if uu____13913
                                        then (t_else, no_lift)
                                        else
                                          (let uu____13934 =
                                             type_leq g t_else t_then in
                                           if uu____13934
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____13902 with
                                       | (t_branch, maybe_lift) ->
                                           let uu____13981 =
                                             let uu____13982 =
                                               let uu____13983 =
                                                 let uu____13992 =
                                                   maybe_lift then_mle t_then in
                                                 let uu____13993 =
                                                   let uu____13996 =
                                                     maybe_lift else_mle
                                                       t_else in
                                                   FStar_Pervasives_Native.Some
                                                     uu____13996 in
                                                 (e, uu____13992,
                                                   uu____13993) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____13983 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____13982 in
                                           let uu____13999 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____13981, uu____13999,
                                             t_branch))))
                        | uu____14000 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____14018 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat ->
                                  fun br ->
                                    let uu____14117 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____14117 with
                                    | (pat, when_opt, branch) ->
                                        let uu____14162 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr in
                                        (match uu____14162 with
                                         | (env, p, pat_t_compat) ->
                                             let uu____14224 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let w_pos =
                                                     w.FStar_Syntax_Syntax.pos in
                                                   let uu____14247 =
                                                     term_as_mlexpr env w in
                                                   (match uu____14247 with
                                                    | (w1, f_w, t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w)) in
                                             (match uu____14224 with
                                              | (when_opt1, f_when) ->
                                                  let uu____14297 =
                                                    term_as_mlexpr env branch in
                                                  (match uu____14297 with
                                                   | (mlbranch, f_branch,
                                                      t_branch) ->
                                                       let uu____14332 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14409
                                                                 ->
                                                                 match uu____14409
                                                                 with
                                                                 | (p1, wopt)
                                                                    ->
                                                                    let when_clause
                                                                    =
                                                                    FStar_Extraction_ML_Util.conjoin_opt
                                                                    wopt
                                                                    when_opt1 in
                                                                    (p1,
                                                                    (when_clause,
                                                                    f_when),
                                                                    (mlbranch,
                                                                    f_branch,
                                                                    t_branch)))) in
                                                       ((compat &&
                                                           pat_t_compat),
                                                         uu____14332)))))
                               true) in
                        match uu____14018 with
                        | (pat_t_compat, mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14580 ->
                                      let uu____14581 =
                                        let uu____14583 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu____14583 e in
                                      let uu____14584 =
                                        let uu____14586 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu____14586 t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14581 uu____14584);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14612 =
                                   let uu____14613 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14613 in
                                 (match uu____14612 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14620;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14622;_}
                                      ->
                                      let uu____14624 =
                                        let uu____14625 =
                                          let uu____14626 =
                                            let uu____14633 =
                                              let uu____14636 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____14636] in
                                            (fw, uu____14633) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14626 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14625 in
                                      (uu____14624,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14640, uu____14641,
                                (uu____14642, f_first, t_first))::rest ->
                                 let uu____14702 =
                                   FStar_List.fold_left
                                     (fun uu____14744 ->
                                        fun uu____14745 ->
                                          match (uu____14744, uu____14745)
                                          with
                                          | ((topt, f),
                                             (uu____14802, uu____14803,
                                              (uu____14804, f_branch,
                                               t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top1.FStar_Syntax_Syntax.pos
                                                  f f_branch in
                                              let topt1 =
                                                match topt with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    t1 ->
                                                    let uu____14860 =
                                                      type_leq g t1 t_branch in
                                                    if uu____14860
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____14867 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____14867
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           t1
                                                       else
                                                         FStar_Pervasives_Native.None) in
                                              (topt1, f1))
                                     ((FStar_Pervasives_Native.Some t_first),
                                       f_first) rest in
                                 (match uu____14702 with
                                  | (topt, f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____14965 ->
                                                match uu____14965 with
                                                | (p, (wopt, uu____14994),
                                                   (b1, uu____14996, t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____15015 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | FStar_Pervasives_Native.Some t1 ->
                                            t1 in
                                      let uu____15020 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____15020, f_match, t_match)))))))
let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env ->
    fun discName ->
      fun constrName ->
        let uu____15047 =
          let uu____15052 =
            let uu____15061 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
            FStar_TypeChecker_Env.lookup_lid uu____15061 discName in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15052 in
        match uu____15047 with
        | (uu____15078, fstar_disc_type) ->
            let uu____15080 =
              let uu____15092 =
                let uu____15093 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____15093.FStar_Syntax_Syntax.n in
              match uu____15092 with
              | FStar_Syntax_Syntax.Tm_arrow (binders, uu____15108) ->
                  let binders1 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_15163 ->
                            match uu___2_15163 with
                            | (uu____15171, FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15172)) ->
                                true
                            | uu____15177 -> false)) in
                  FStar_List.fold_right
                    (fun uu____15209 ->
                       fun uu____15210 ->
                         match uu____15210 with
                         | (g, vs) ->
                             let uu____15255 =
                               FStar_Extraction_ML_UEnv.new_mlident g in
                             (match uu____15255 with
                              | (g1, v) ->
                                  (g1,
                                    ((v, FStar_Extraction_ML_Syntax.MLTY_Top)
                                    :: vs)))) binders1 (env, [])
              | uu____15301 -> failwith "Discriminator must be a function" in
            (match uu____15080 with
             | (g, wildcards) ->
                 let uu____15330 = FStar_Extraction_ML_UEnv.new_mlident g in
                 (match uu____15330 with
                  | (g1, mlid) ->
                      let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
                      let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
                      let discrBody =
                        let uu____15343 =
                          let uu____15344 =
                            let uu____15356 =
                              let uu____15357 =
                                let uu____15358 =
                                  let uu____15373 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         targ)
                                      (FStar_Extraction_ML_Syntax.MLE_Name
                                         ([], mlid)) in
                                  let uu____15379 =
                                    let uu____15390 =
                                      let uu____15399 =
                                        let uu____15400 =
                                          let uu____15407 =
                                            FStar_Extraction_ML_UEnv.mlpath_of_lident
                                              g1 constrName in
                                          (uu____15407,
                                            [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                                        FStar_Extraction_ML_Syntax.MLP_CTor
                                          uu____15400 in
                                      let uu____15410 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_bool_ty)
                                          (FStar_Extraction_ML_Syntax.MLE_Const
                                             (FStar_Extraction_ML_Syntax.MLC_Bool
                                                true)) in
                                      (uu____15399,
                                        FStar_Pervasives_Native.None,
                                        uu____15410) in
                                    let uu____15414 =
                                      let uu____15425 =
                                        let uu____15434 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.ml_bool_ty)
                                            (FStar_Extraction_ML_Syntax.MLE_Const
                                               (FStar_Extraction_ML_Syntax.MLC_Bool
                                                  false)) in
                                        (FStar_Extraction_ML_Syntax.MLP_Wild,
                                          FStar_Pervasives_Native.None,
                                          uu____15434) in
                                      [uu____15425] in
                                    uu____15390 :: uu____15414 in
                                  (uu____15373, uu____15379) in
                                FStar_Extraction_ML_Syntax.MLE_Match
                                  uu____15358 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                uu____15357 in
                            ((FStar_List.append wildcards [(mlid, targ)]),
                              uu____15356) in
                          FStar_Extraction_ML_Syntax.MLE_Fun uu____15344 in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty disc_ty)
                          uu____15343 in
                      let uu____15495 =
                        FStar_Extraction_ML_UEnv.mlpath_of_lident env
                          discName in
                      (match uu____15495 with
                       | (uu____15496, name) ->
                           FStar_Extraction_ML_Syntax.MLM_Let
                             (FStar_Extraction_ML_Syntax.NonRec,
                               [{
                                  FStar_Extraction_ML_Syntax.mllb_name = name;
                                  FStar_Extraction_ML_Syntax.mllb_tysc =
                                    FStar_Pervasives_Native.None;
                                  FStar_Extraction_ML_Syntax.mllb_add_unit =
                                    false;
                                  FStar_Extraction_ML_Syntax.mllb_def =
                                    discrBody;
                                  FStar_Extraction_ML_Syntax.mllb_meta = [];
                                  FStar_Extraction_ML_Syntax.print_typ =
                                    false
                                }]))))