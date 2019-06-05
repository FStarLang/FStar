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
let record_fields :
  'Auu____77 .
    FStar_Ident.ident Prims.list ->
      'Auu____77 Prims.list -> (Prims.string * 'Auu____77) Prims.list
  =
  fun fs ->
    fun vs ->
      FStar_List.map2 (fun f -> fun e -> ((f.FStar_Ident.idText), e)) fs vs
let fail :
  'Auu____120 .
    FStar_Range.range ->
      (FStar_Errors.raw_error * Prims.string) -> 'Auu____120
  = fun r -> fun err -> FStar_Errors.raise_error err r
let err_ill_typed_application :
  'Auu____156 'Auu____157 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'Auu____156) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'Auu____157
  =
  fun env ->
    fun t ->
      fun mlhead ->
        fun args ->
          fun ty ->
            let uu____195 =
              let uu____201 =
                let uu____203 = FStar_Syntax_Print.term_to_string t in
                let uu____205 =
                  FStar_Extraction_ML_Code.string_of_mlexpr
                    env.FStar_Extraction_ML_UEnv.currentModule mlhead in
                let uu____207 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty in
                let uu____209 =
                  let uu____211 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____232 ->
                            match uu____232 with
                            | (x, uu____239) ->
                                FStar_Syntax_Print.term_to_string x)) in
                  FStar_All.pipe_right uu____211 (FStar_String.concat " ") in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____203 uu____205 uu____207 uu____209 in
              (FStar_Errors.Fatal_IllTyped, uu____201) in
            fail t.FStar_Syntax_Syntax.pos uu____195
let err_ill_typed_erasure :
  'Auu____256 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____256
  =
  fun env ->
    fun pos ->
      fun ty ->
        let uu____272 =
          let uu____278 =
            let uu____280 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____280 in
          (FStar_Errors.Fatal_IllTyped, uu____278) in
        fail pos uu____272
let err_value_restriction :
  'Auu____289 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____289
  =
  fun t ->
    let uu____299 =
      let uu____305 =
        let uu____307 = FStar_Syntax_Print.tag_of_term t in
        let uu____309 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____307 uu____309 in
      (FStar_Errors.Fatal_ValueRestriction, uu____305) in
    fail t.FStar_Syntax_Syntax.pos uu____299
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
            let uu____343 =
              let uu____349 =
                let uu____351 = FStar_Syntax_Print.term_to_string t in
                let uu____353 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty in
                let uu____355 = FStar_Extraction_ML_Util.eff_to_string f0 in
                let uu____357 = FStar_Extraction_ML_Util.eff_to_string f1 in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____351 uu____353 uu____355 uu____357 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____349) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____343
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  let rec delta_norm_eff g l =
    let uu____385 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
    match uu____385 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None ->
        let res =
          let uu____390 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.env_tcenv
              [FStar_Syntax_Syntax.U_zero] l in
          match uu____390 with
          | FStar_Pervasives_Native.None -> l
          | FStar_Pervasives_Native.Some (uu____401, c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c) in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res) in
  fun g ->
    fun l ->
      let l1 = delta_norm_eff g l in
      let uu____411 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid in
      if uu____411
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____416 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid in
         if uu____416
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.env_tcenv l1 in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                let uu____442 =
                  FStar_TypeChecker_Env.is_reifiable_effect
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    ed.FStar_Syntax_Syntax.mname in
                if uu____442
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____466 =
        let uu____467 = FStar_Syntax_Subst.compress t1 in
        uu____467.FStar_Syntax_Syntax.n in
      match uu____466 with
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____473 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____498 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____527 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____537 = FStar_Syntax_Util.unfold_lazy i in
          is_arity env uu____537
      | FStar_Syntax_Syntax.Tm_uvar uu____538 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____552 -> false
      | FStar_Syntax_Syntax.Tm_name uu____554 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____556 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____564 -> false
      | FStar_Syntax_Syntax.Tm_type uu____566 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____568, c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let topt =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant]
              env.FStar_Extraction_ML_UEnv.env_tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match topt with
           | FStar_Pervasives_Native.None -> false
           | FStar_Pervasives_Native.Some (uu____604, t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____610 ->
          let uu____627 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____627 with | (head1, uu____646) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1, uu____672) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x, uu____678) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____683, body, uu____685) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____710, body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____730, branches) ->
          (match branches with
           | (uu____769, uu____770, e)::uu____772 -> is_arity env e
           | uu____819 -> false)
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____851 ->
          let uu____874 =
            let uu____876 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____876 in
          failwith uu____874
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____880 =
            let uu____882 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____882 in
          failwith uu____880
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____887 = FStar_Syntax_Util.unfold_lazy i in
          is_type_aux env uu____887
      | FStar_Syntax_Syntax.Tm_constant uu____888 -> false
      | FStar_Syntax_Syntax.Tm_type uu____890 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____892 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____900 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____919;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____920;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____921;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____923;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____924;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____925;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____926;_},
           s)
          ->
          let uu____975 = FStar_Syntax_Subst.subst' s t2 in
          is_arity env uu____975
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____976;
            FStar_Syntax_Syntax.index = uu____977;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____982;
            FStar_Syntax_Syntax.index = uu____983;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____989, uu____990) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____1032) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____1039) ->
          let uu____1064 = FStar_Syntax_Subst.open_term bs body in
          (match uu____1064 with
           | (uu____1070, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
          let uu____1090 =
            let uu____1095 =
              let uu____1096 = FStar_Syntax_Syntax.mk_binder x in
              [uu____1096] in
            FStar_Syntax_Subst.open_term uu____1095 body in
          (match uu____1090 with
           | (uu____1116, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1118, lbs), body) ->
          let uu____1138 = FStar_Syntax_Subst.open_let_rec lbs body in
          (match uu____1138 with
           | (uu____1146, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1152, branches) ->
          (match branches with
           | b::uu____1192 ->
               let uu____1237 = FStar_Syntax_Subst.open_branch b in
               (match uu____1237 with
                | (uu____1239, uu____1240, e) -> is_type_aux env e)
           | uu____1258 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1276 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2, uu____1285) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1, uu____1291) ->
          is_type_aux env head1
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1332 ->
           let uu____1333 = FStar_Syntax_Print.tag_of_term t in
           let uu____1335 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1333
             uu____1335);
      (let b = is_type_aux env t in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1344 ->
            if b
            then
              let uu____1346 = FStar_Syntax_Print.term_to_string t in
              let uu____1348 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1346
                uu____1348
            else
              (let uu____1353 = FStar_Syntax_Print.term_to_string t in
               let uu____1355 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1353 uu____1355));
       b)
let is_type_binder :
  'Auu____1365 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____1365) -> Prims.bool
  =
  fun env ->
    fun x ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1392 =
      let uu____1393 = FStar_Syntax_Subst.compress t in
      uu____1393.FStar_Syntax_Syntax.n in
    match uu____1392 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1397;
          FStar_Syntax_Syntax.fv_delta = uu____1398;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor);_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1400;
          FStar_Syntax_Syntax.fv_delta = uu____1401;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1402);_}
        -> true
    | uu____1410 -> false
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1419 =
      let uu____1420 = FStar_Syntax_Subst.compress t in
      uu____1420.FStar_Syntax_Syntax.n in
    match uu____1419 with
    | FStar_Syntax_Syntax.Tm_constant uu____1424 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1426 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1428 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1430 -> true
    | FStar_Syntax_Syntax.Tm_app (head1, args) ->
        let uu____1476 = is_constructor head1 in
        if uu____1476
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1498 ->
                  match uu____1498 with
                  | (te, uu____1507) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1, uu____1516) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1522, uu____1523) ->
        is_fstar_value t1
    | uu____1564 -> false
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1574 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1576 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1579 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1581 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1594, exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1603, fields) ->
        FStar_Util.for_all
          (fun uu____1633 ->
             match uu____1633 with | (uu____1640, e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h, uu____1645) -> is_ml_value h
    | uu____1650 -> false
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x ->
    FStar_Util.incr c;
    (let uu____1668 =
       let uu____1670 = FStar_ST.op_Bang c in
       FStar_Util.string_of_int uu____1670 in
     Prims.op_Hat x uu____1668)
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0 ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1773 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____1775 = FStar_Syntax_Util.is_fun e' in
          if uu____1775
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 FStar_Pervasives_Native.None
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1789 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1789
let (check_pats_for_ite :
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list ->
    (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option))
  =
  fun l ->
    let def =
      (false, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) in
    if (FStar_List.length l) <> (Prims.parse_int "2")
    then def
    else
      (let uu____1880 = FStar_List.hd l in
       match uu____1880 with
       | (p1, w1, e1) ->
           let uu____1915 =
             let uu____1924 = FStar_List.tl l in FStar_List.hd uu____1924 in
           (match uu____1915 with
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
                 | uu____2008 -> def)))
let (instantiate_tyscheme :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  = fun s -> fun args -> FStar_Extraction_ML_Util.subst s args
let (instantiate_maybe_partial :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mltyscheme ->
      FStar_Extraction_ML_Syntax.mlty Prims.list ->
        (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag
          * FStar_Extraction_ML_Syntax.mlty))
  =
  fun e ->
    fun s ->
      fun tyargs ->
        let uu____2068 = s in
        match uu____2068 with
        | (vars, t) ->
            let n_vars = FStar_List.length vars in
            let n_args = FStar_List.length tyargs in
            if n_args = n_vars
            then
              (if n_args = (Prims.parse_int "0")
               then (e, FStar_Extraction_ML_Syntax.E_PURE, t)
               else
                 (let ts = instantiate_tyscheme (vars, t) tyargs in
                  let tapp =
                    let uu___365_2100 = e in
                    {
                      FStar_Extraction_ML_Syntax.expr =
                        (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                      FStar_Extraction_ML_Syntax.mlty = ts;
                      FStar_Extraction_ML_Syntax.loc =
                        (uu___365_2100.FStar_Extraction_ML_Syntax.loc)
                    } in
                  (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
            else
              if n_args < n_vars
              then
                (let extra_tyargs =
                   let uu____2115 = FStar_Util.first_N n_args vars in
                   match uu____2115 with
                   | (uu____2129, rest_vars) ->
                       FStar_All.pipe_right rest_vars
                         (FStar_List.map
                            (fun uu____2150 ->
                               FStar_Extraction_ML_Syntax.MLTY_Erased)) in
                 let tyargs1 = FStar_List.append tyargs extra_tyargs in
                 let ts = instantiate_tyscheme (vars, t) tyargs1 in
                 let tapp =
                   let uu___376_2157 = e in
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                     FStar_Extraction_ML_Syntax.mlty = ts;
                     FStar_Extraction_ML_Syntax.loc =
                       (uu___376_2157.FStar_Extraction_ML_Syntax.loc)
                   } in
                 let t1 =
                   FStar_List.fold_left
                     (fun out ->
                        fun t1 ->
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                            (t1, FStar_Extraction_ML_Syntax.E_PURE, out)) ts
                     extra_tyargs in
                 let f =
                   let vs_ts =
                     FStar_List.map
                       (fun t2 ->
                          let uu____2182 = fresh "t" in (uu____2182, t2))
                       extra_tyargs in
                   FStar_All.pipe_left
                     (FStar_Extraction_ML_Syntax.with_ty t1)
                     (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, tapp)) in
                 (f, FStar_Extraction_ML_Syntax.E_PURE, t1))
              else
                failwith
                  "Impossible: instantiate_maybe_partial called with too many arguments"
let (eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun t ->
    fun e ->
      let uu____2213 = FStar_Extraction_ML_Util.doms_and_cod t in
      match uu____2213 with
      | (ts, r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____2237 -> fresh "a") ts in
             let vs_ts = FStar_List.zip vs ts in
             let vs_es =
               let uu____2251 = FStar_List.zip vs ts in
               FStar_List.map
                 (fun uu____2268 ->
                    match uu____2268 with
                    | (v1, t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____2251 in
             let body =
               FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r)
                 (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es)) in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
let (default_value_for_ty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun t ->
      let uu____2299 = FStar_Extraction_ML_Util.doms_and_cod t in
      match uu____2299 with
      | (ts, r) ->
          let body r1 =
            let r2 =
              let uu____2319 = FStar_Extraction_ML_Util.udelta_unfold g r1 in
              match uu____2319 with
              | FStar_Pervasives_Native.None -> r1
              | FStar_Pervasives_Native.Some r2 -> r2 in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2323 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2)) in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____2335 -> fresh "a") ts in
             let vs_ts = FStar_List.zip vs ts in
             let uu____2346 =
               let uu____2347 =
                 let uu____2359 = body r in (vs_ts, uu____2359) in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____2347 in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____2346)
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect ->
    fun e ->
      let uu____2378 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____2381 = FStar_Options.codegen () in
           uu____2381 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)) in
      if uu____2378 then e else eta_expand expect e
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
            | uu____2459 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body) in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____2514 =
              match uu____2514 with
              | (pat, w, b) ->
                  let uu____2538 = aux b ty1 expect1 in (pat, w, uu____2538) in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun (arg::rest, body),
               FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____2545, t1),
               FStar_Extraction_ML_Syntax.MLTY_Fun (s0, uu____2548, s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____2580 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body)) in
                let body2 = aux body1 t1 s1 in
                let uu____2596 = type_leq g s0 t0 in
                if uu____2596
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____2602 =
                       let uu____2603 =
                         let uu____2604 =
                           let uu____2611 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg)) in
                           (uu____2611, s0, t0) in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____2604 in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____2603 in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____2602;
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
            | (FStar_Extraction_ML_Syntax.MLE_Let (lbs, body), uu____2630,
               uu____2631) ->
                let uu____2644 =
                  let uu____2645 =
                    let uu____2656 = aux body ty1 expect1 in
                    (lbs, uu____2656) in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____2645 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2644
            | (FStar_Extraction_ML_Syntax.MLE_Match (s, branches),
               uu____2665, uu____2666) ->
                let uu____2687 =
                  let uu____2688 =
                    let uu____2703 = FStar_List.map coerce_branch branches in
                    (s, uu____2703) in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____2688 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2687
            | (FStar_Extraction_ML_Syntax.MLE_If (s, b1, b2_opt), uu____2743,
               uu____2744) ->
                let uu____2749 =
                  let uu____2750 =
                    let uu____2759 = aux b1 ty1 expect1 in
                    let uu____2760 =
                      FStar_Util.map_opt b2_opt
                        (fun b2 -> aux b2 ty1 expect1) in
                    (s, uu____2759, uu____2760) in
                  FStar_Extraction_ML_Syntax.MLE_If uu____2750 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2749
            | (FStar_Extraction_ML_Syntax.MLE_Seq es, uu____2768, uu____2769)
                ->
                let uu____2772 = FStar_Util.prefix es in
                (match uu____2772 with
                 | (prefix1, last1) ->
                     let uu____2785 =
                       let uu____2786 =
                         let uu____2789 =
                           let uu____2792 = aux last1 ty1 expect1 in
                           [uu____2792] in
                         FStar_List.append prefix1 uu____2789 in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____2786 in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____2785)
            | (FStar_Extraction_ML_Syntax.MLE_Try (s, branches), uu____2795,
               uu____2796) ->
                let uu____2817 =
                  let uu____2818 =
                    let uu____2833 = FStar_List.map coerce_branch branches in
                    (s, uu____2833) in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____2818 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2817
            | uu____2870 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1)) in
          aux e ty expect
let maybe_coerce :
  'Auu____2890 .
    'Auu____2890 ->
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
            let uu____2917 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect in
            match uu____2917 with
            | (true, FStar_Pervasives_Native.Some e') -> e'
            | uu____2930 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                     default_value_for_ty g expect
                 | uu____2938 ->
                     let uu____2939 =
                       let uu____2941 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1 in
                       let uu____2942 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect in
                       type_leq g uu____2941 uu____2942 in
                     if uu____2939
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____2948 ->
                             let uu____2949 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e in
                             let uu____2951 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____2949 uu____2951);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____2961 ->
                             let uu____2962 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e in
                             let uu____2964 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                             let uu____2966 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule
                                 expect in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____2962 uu____2964 uu____2966);
                        (let uu____2969 = apply_coercion g e ty1 expect in
                         maybe_eta_expand expect uu____2969)))
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun bv ->
      let uu____2981 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____2981 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____2983 -> FStar_Extraction_ML_Syntax.MLTY_Top
let (extraction_norm_steps : FStar_TypeChecker_Env.step Prims.list) =
  [FStar_TypeChecker_Env.AllowUnboundUniverses;
  FStar_TypeChecker_Env.EraseUniverses;
  FStar_TypeChecker_Env.Inlining;
  FStar_TypeChecker_Env.Eager_unfolding;
  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
  FStar_TypeChecker_Env.Primops;
  FStar_TypeChecker_Env.Unascribe;
  FStar_TypeChecker_Env.ForExtraction]
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____3001 -> c
    | FStar_Syntax_Syntax.GTotal uu____3010 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____3046 ->
               match uu____3046 with
               | (uu____3061, aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args in
        let ct1 =
          let uu___538_3074 = ct in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___538_3074.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___538_3074.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___538_3074.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___538_3074.FStar_Syntax_Syntax.flags)
          } in
        let c1 =
          let uu___541_3078 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___541_3078.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___541_3078.FStar_Syntax_Syntax.vars)
          } in
        c1
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t0 ->
      let arg_as_mlty g1 uu____3127 =
        match uu____3127 with
        | (a, uu____3135) ->
            let uu____3140 = is_type g1 a in
            if uu____3140
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent in
      let fv_app_as_mlty g1 fv args =
        let uu____3161 =
          let uu____3163 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv in
          Prims.op_Negation uu____3163 in
        if uu____3161
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____3168 =
             let uu____3183 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.env_tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             match uu____3183 with
             | ((uu____3206, fvty), uu____3208) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant]
                     g1.FStar_Extraction_ML_UEnv.env_tcenv fvty in
                 FStar_Syntax_Util.arrow_formals fvty1 in
           match uu____3168 with
           | (formals, uu____3215) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args in
               let mlargs1 =
                 let n_args = FStar_List.length args in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3268 = FStar_Util.first_N n_args formals in
                   match uu____3268 with
                   | (uu____3297, rest) ->
                       let uu____3331 =
                         FStar_List.map
                           (fun uu____3341 ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest in
                       FStar_List.append mlargs uu____3331
                 else mlargs in
               let nm =
                 let uu____3351 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv in
                 match uu____3351 with
                 | FStar_Pervasives_Native.Some p -> p
                 | FStar_Pervasives_Native.None ->
                     FStar_Extraction_ML_Syntax.mlpath_of_lident
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)) in
      let aux env t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_type uu____3369 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3370 ->
            let uu____3371 =
              let uu____3373 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3373 in
            failwith uu____3371
        | FStar_Syntax_Syntax.Tm_delayed uu____3376 ->
            let uu____3399 =
              let uu____3401 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3401 in
            failwith uu____3399
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu____3404 =
              let uu____3406 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3406 in
            failwith uu____3404
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3410 = FStar_Syntax_Util.unfold_lazy i in
            translate_term_to_mlty env uu____3410
        | FStar_Syntax_Syntax.Tm_constant uu____3411 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____3412 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____3419 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2, uu____3433) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3438;
               FStar_Syntax_Syntax.index = uu____3439;
               FStar_Syntax_Syntax.sort = t2;_},
             uu____3441)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2, uu____3450) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3456, uu____3457) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let uu____3530 = FStar_Syntax_Subst.open_comp bs c in
            (match uu____3530 with
             | (bs1, c1) ->
                 let uu____3537 = binders_as_ml_binders env bs1 in
                 (match uu____3537 with
                  | (mlbs, env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.env_tcenv
                            (FStar_Syntax_Util.comp_effect_name c1) in
                        let c2 = comp_no_args c1 in
                        let uu____3570 =
                          let uu____3577 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.env_tcenv eff in
                          FStar_Util.must uu____3577 in
                        match uu____3570 with
                        | (ed, qualifiers) ->
                            let uu____3598 =
                              FStar_TypeChecker_Env.is_reifiable_effect
                                g.FStar_Extraction_ML_UEnv.env_tcenv
                                ed.FStar_Syntax_Syntax.mname in
                            if uu____3598
                            then
                              let t2 =
                                FStar_TypeChecker_Env.reify_comp
                                  env1.FStar_Extraction_ML_UEnv.env_tcenv c2
                                  FStar_Syntax_Syntax.U_unknown in
                              (FStar_Extraction_ML_UEnv.debug env1
                                 (fun uu____3606 ->
                                    let uu____3607 =
                                      FStar_Syntax_Print.comp_to_string c2 in
                                    let uu____3609 =
                                      FStar_Syntax_Print.term_to_string t2 in
                                    FStar_Util.print2
                                      "Translating comp type %s as %s\n"
                                      uu____3607 uu____3609);
                               (let res = translate_term_to_mlty env1 t2 in
                                FStar_Extraction_ML_UEnv.debug env1
                                  (fun uu____3618 ->
                                     let uu____3619 =
                                       FStar_Syntax_Print.comp_to_string c2 in
                                     let uu____3621 =
                                       FStar_Syntax_Print.term_to_string t2 in
                                     let uu____3623 =
                                       FStar_Extraction_ML_Code.string_of_mlty
                                         env1.FStar_Extraction_ML_UEnv.currentModule
                                         res in
                                     FStar_Util.print3
                                       "Translated comp type %s as %s ... to %s\n"
                                       uu____3619 uu____3621 uu____3623);
                                res))
                            else
                              translate_term_to_mlty env1
                                (FStar_Syntax_Util.comp_result c2) in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____3629 =
                        FStar_List.fold_right
                          (fun uu____3649 ->
                             fun uu____3650 ->
                               match (uu____3649, uu____3650) with
                               | ((uu____3673, t2), (tag, t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret) in
                      (match uu____3629 with | (uu____3688, t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1, args) ->
            let res =
              let uu____3717 =
                let uu____3718 = FStar_Syntax_Util.un_uinst head1 in
                uu____3718.FStar_Syntax_Syntax.n in
              match uu____3717 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2, args') ->
                  let uu____3749 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
                  translate_term_to_mlty env uu____3749
              | uu____3770 -> FStar_Extraction_ML_UEnv.unknownType in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____3773) ->
            let uu____3798 = FStar_Syntax_Subst.open_term bs ty in
            (match uu____3798 with
             | (bs1, ty1) ->
                 let uu____3805 = binders_as_ml_binders env bs1 in
                 (match uu____3805 with
                  | (bts, env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____3833 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____3847 ->
            FStar_Extraction_ML_UEnv.unknownType in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____3879 ->
            let uu____3886 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____3886 with
             | FStar_Pervasives_Native.None -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____3892 -> false in
      let uu____3894 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.env_tcenv t0 in
      if uu____3894
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0 in
         let uu____3900 = is_top_ty mlt in
         if uu____3900 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)
and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g ->
    fun bs ->
      let uu____3918 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____3974 ->
                fun b ->
                  match uu____3974 with
                  | (ml_bs, env) ->
                      let uu____4020 = is_type_binder g b in
                      if uu____4020
                      then
                        let b1 = FStar_Pervasives_Native.fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____4046 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____4046, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort in
                         let uu____4067 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____4067 with
                         | (env1, b2, uu____4092) ->
                             let ml_b =
                               let uu____4101 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____4101, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____3918 with | (ml_bs, env) -> ((FStar_List.rev ml_bs), env)
let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t0 ->
      let t =
        FStar_TypeChecker_Normalize.normalize extraction_norm_steps
          g.FStar_Extraction_ML_UEnv.env_tcenv t0 in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1, uu____4197) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4200, FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4204 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                    | uu____4238 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4239 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4240 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4249 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q ->
    fun p ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) ->
          let uu____4277 = FStar_Extraction_ML_Util.is_xtuple d in
          (match uu____4277 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____4284 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty, fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____4317 -> p))
      | uu____4320 -> p
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
                       (fun uu____4422 ->
                          let uu____4423 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t' in
                          let uu____4425 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4423 uu____4425)
                   else ();
                   ok) in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c, swopt)) when
                let uu____4461 = FStar_Options.codegen () in
                uu____4461 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4466 =
                  match swopt with
                  | FStar_Pervasives_Native.None ->
                      let uu____4479 =
                        let uu____4480 =
                          let uu____4481 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None)) in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4481 in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4480 in
                      (uu____4479, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange in
                      let uu____4503 = term_as_mlexpr g source_term in
                      (match uu____4503 with
                       | (mlterm, uu____4515, mlty) -> (mlterm, mlty)) in
                (match uu____4466 with
                 | (mlc, ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym () in
                     let when_clause =
                       let uu____4537 =
                         let uu____4538 =
                           let uu____4545 =
                             let uu____4548 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x) in
                             [uu____4548; mlc] in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____4545) in
                         FStar_Extraction_ML_Syntax.MLE_App uu____4538 in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____4537 in
                     let uu____4551 = ok ml_ty in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____4551))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    FStar_Range.dummyRange s in
                let mlty = term_as_mlty g t in
                let uu____4573 =
                  let uu____4582 =
                    let uu____4589 =
                      let uu____4590 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4590 in
                    (uu____4589, []) in
                  FStar_Pervasives_Native.Some uu____4582 in
                let uu____4599 = ok mlty in (g, uu____4573, uu____4599)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____4612 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                (match uu____4612 with
                 | (g1, x1, uu____4640) ->
                     let uu____4643 = ok mlty in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4643))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____4681 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                (match uu____4681 with
                 | (g1, x1, uu____4709) ->
                     let uu____4712 = ok mlty in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4712))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4748 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f, pats) ->
                let uu____4791 =
                  let uu____4800 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                  match uu____4800 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____4809;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____4811;
                          FStar_Extraction_ML_Syntax.loc = uu____4812;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____4814;_}
                      -> (n1, ttys)
                  | uu____4821 -> failwith "Expected a constructor" in
                (match uu____4791 with
                 | (d, tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys) in
                     let uu____4858 = FStar_Util.first_N nTyVars pats in
                     (match uu____4858 with
                      | (tysVarPats, restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___836_4962 ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____4993 ->
                                               match uu____4993 with
                                               | (p1, uu____5000) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5003, t) ->
                                                        term_as_mlty g t
                                                    | uu____5009 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5013 ->
                                                              let uu____5014
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5014);
                                                         FStar_Exn.raise
                                                           Un_extractable)))) in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args in
                                     let uu____5018 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty in
                                     FStar_Pervasives_Native.Some uu____5018)
                                ()
                            with
                            | Un_extractable -> FStar_Pervasives_Native.None in
                          let uu____5047 =
                            FStar_Util.fold_map
                              (fun g1 ->
                                 fun uu____5084 ->
                                   match uu____5084 with
                                   | (p1, imp1) ->
                                       let uu____5106 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr in
                                       (match uu____5106 with
                                        | (g2, p2, uu____5137) -> (g2, p2)))
                              g tysVarPats in
                          (match uu____5047 with
                           | (g1, tyMLPats) ->
                               let uu____5201 =
                                 FStar_Util.fold_map
                                   (fun uu____5266 ->
                                      fun uu____5267 ->
                                        match (uu____5266, uu____5267) with
                                        | ((g2, f_ty_opt1), (p1, imp1)) ->
                                            let uu____5365 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest, res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____5425 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None) in
                                            (match uu____5365 with
                                             | (f_ty_opt2, expected_ty) ->
                                                 let uu____5496 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr in
                                                 (match uu____5496 with
                                                  | (g3, p2, uu____5539) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats in
                               (match uu____5201 with
                                | ((g2, f_ty_opt1), restMLPats) ->
                                    let uu____5660 =
                                      let uu____5671 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5722 ->
                                                match uu___0_5722 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____5764 -> [])) in
                                      FStar_All.pipe_right uu____5671
                                        FStar_List.split in
                                    (match uu____5660 with
                                     | (mlPats, when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([], t) -> ok t
                                           | uu____5840 -> false in
                                         let uu____5850 =
                                           let uu____5859 =
                                             let uu____5866 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats)) in
                                             let uu____5869 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten in
                                             (uu____5866, uu____5869) in
                                           FStar_Pervasives_Native.Some
                                             uu____5859 in
                                         (g2, uu____5850, pat_ty_compat))))))
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
            let uu____6001 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr in
            match uu____6001 with
            | (g2, FStar_Pervasives_Native.Some (x, v1), b) ->
                (g2, (x, v1), b)
            | uu____6064 ->
                failwith "Impossible: Unable to translate pattern" in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____6112 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1 in
                FStar_Pervasives_Native.Some uu____6112 in
          let uu____6113 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t) in
          match uu____6113 with
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
          let rec eta_args more_args t =
            match t with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____6273, t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____6277 =
                  let uu____6289 =
                    let uu____6299 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____6299) in
                  uu____6289 :: more_args in
                eta_args uu____6277 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6315, uu____6316)
                -> ((FStar_List.rev more_args), t)
            | uu____6341 ->
                let uu____6342 =
                  let uu____6344 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr in
                  let uu____6346 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6344 uu____6346 in
                failwith uu____6342 in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____6381, args),
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
               (tyname, fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6418 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____6440 = eta_args [] residualType in
            match uu____6440 with
            | (eargs, tres) ->
                (match eargs with
                 | [] ->
                     let uu____6498 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____6498
                 | uu____6499 ->
                     let uu____6511 = FStar_List.unzip eargs in
                     (match uu____6511 with
                      | (binders, eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor
                               (head1, args) ->
                               let body =
                                 let uu____6557 =
                                   let uu____6558 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6558 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6557 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6568 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6572, FStar_Pervasives_Native.None) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6576;
                FStar_Extraction_ML_Syntax.loc = uu____6577;_},
              mle::args),
             FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname, f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____6600 ->
                    let uu____6603 =
                      let uu____6610 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____6610, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6603 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6614;
                     FStar_Extraction_ML_Syntax.loc = uu____6615;_},
                   uu____6616);
                FStar_Extraction_ML_Syntax.mlty = uu____6617;
                FStar_Extraction_ML_Syntax.loc = uu____6618;_},
              mle::args),
             FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname, f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____6645 ->
                    let uu____6648 =
                      let uu____6655 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____6655, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6648 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6659;
                FStar_Extraction_ML_Syntax.loc = uu____6660;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____6668 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6668
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6672;
                FStar_Extraction_ML_Syntax.loc = uu____6673;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____6675)) ->
              let uu____6688 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6688
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6692;
                     FStar_Extraction_ML_Syntax.loc = uu____6693;_},
                   uu____6694);
                FStar_Extraction_ML_Syntax.mlty = uu____6695;
                FStar_Extraction_ML_Syntax.loc = uu____6696;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____6708 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6708
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6712;
                     FStar_Extraction_ML_Syntax.loc = uu____6713;_},
                   uu____6714);
                FStar_Extraction_ML_Syntax.mlty = uu____6715;
                FStar_Extraction_ML_Syntax.loc = uu____6716;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____6718)) ->
              let uu____6735 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6735
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____6741 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6741
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____6745)) ->
              let uu____6754 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6754
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6758;
                FStar_Extraction_ML_Syntax.loc = uu____6759;_},
              uu____6760),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____6767 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6767
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6771;
                FStar_Extraction_ML_Syntax.loc = uu____6772;_},
              uu____6773),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____6774)) ->
              let uu____6787 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6787
          | uu____6790 -> mlAppExpr
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
        | uu____6821 -> (ml_e, tag)
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
      let maybe_generalize uu____6882 =
        match uu____6882 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____6903;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = uu____6907;
            FStar_Syntax_Syntax.lbpos = uu____6908;_} ->
            let f_e = effect_as_etag g lbeff in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp in
            let no_gen uu____6989 =
              let expected_t = term_as_mlty g lbtyp1 in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef) in
            let uu____7066 =
              FStar_TypeChecker_Util.must_erase_for_extraction
                g.FStar_Extraction_ML_UEnv.env_tcenv lbtyp1 in
            if uu____7066
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                   let uu____7152 = FStar_List.hd bs in
                   FStar_All.pipe_right uu____7152 (is_type_binder g) ->
                   let uu____7174 = FStar_Syntax_Subst.open_comp bs c in
                   (match uu____7174 with
                    | (bs1, c1) ->
                        let uu____7200 =
                          let uu____7213 =
                            FStar_Util.prefix_until
                              (fun x ->
                                 let uu____7259 = is_type_binder g x in
                                 Prims.op_Negation uu____7259) bs1 in
                          match uu____7213 with
                          | FStar_Pervasives_Native.None ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2, b, rest) ->
                              let uu____7386 =
                                FStar_Syntax_Util.arrow (b :: rest) c1 in
                              (bs2, uu____7386) in
                        (match uu____7200 with
                         | (tbinders, tbody) ->
                             let n_tbinders = FStar_List.length tbinders in
                             let lbdef1 =
                               let uu____7448 = normalize_abs lbdef in
                               FStar_All.pipe_right uu____7448
                                 FStar_Syntax_Util.unmeta in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2, body, copt)
                                  ->
                                  let uu____7497 =
                                    FStar_Syntax_Subst.open_term bs2 body in
                                  (match uu____7497 with
                                   | (bs3, body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7549 =
                                           FStar_Util.first_N n_tbinders bs3 in
                                         (match uu____7549 with
                                          | (targs, rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7652 ->
                                                       fun uu____7653 ->
                                                         match (uu____7652,
                                                                 uu____7653)
                                                         with
                                                         | ((x, uu____7679),
                                                            (y, uu____7681))
                                                             ->
                                                             let uu____7702 =
                                                               let uu____7709
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y in
                                                               (x,
                                                                 uu____7709) in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7702)
                                                    tbinders targs in
                                                FStar_Syntax_Subst.subst s
                                                  tbody in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env ->
                                                     fun uu____7726 ->
                                                       match uu____7726 with
                                                       | (a, uu____7734) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a
                                                             FStar_Pervasives_Native.None)
                                                  g targs in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty in
                                              let polytype =
                                                let uu____7745 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____7764 ->
                                                          match uu____7764
                                                          with
                                                          | (x, uu____7773)
                                                              ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x)) in
                                                (uu____7745, expected_t) in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____7789 =
                                                       is_fstar_value body1 in
                                                     Prims.op_Negation
                                                       uu____7789)
                                                      ||
                                                      (let uu____7792 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1 in
                                                       Prims.op_Negation
                                                         uu____7792)
                                                | uu____7794 -> false in
                                              let rest_args1 =
                                                if add_unit
                                                then unit_binder :: rest_args
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____7856 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env ->
                                         fun uu____7875 ->
                                           match uu____7875 with
                                           | (a, uu____7883) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu____7894 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____7913 ->
                                              match uu____7913 with
                                              | (x, uu____7922) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x)) in
                                    (uu____7894, expected_t) in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____7966 ->
                                            match uu____7966 with
                                            | (bv, uu____7974) ->
                                                let uu____7979 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_All.pipe_right
                                                  uu____7979
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      FStar_Pervasives_Native.None
                                      lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | FStar_Syntax_Syntax.Tm_fvar uu____8009 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env ->
                                         fun uu____8022 ->
                                           match uu____8022 with
                                           | (a, uu____8030) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu____8041 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8060 ->
                                              match uu____8060 with
                                              | (x, uu____8069) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x)) in
                                    (uu____8041, expected_t) in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8113 ->
                                            match uu____8113 with
                                            | (bv, uu____8121) ->
                                                let uu____8126 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_All.pipe_right
                                                  uu____8126
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      FStar_Pervasives_Native.None
                                      lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | FStar_Syntax_Syntax.Tm_name uu____8156 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env ->
                                         fun uu____8169 ->
                                           match uu____8169 with
                                           | (a, uu____8177) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu____8188 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8207 ->
                                              match uu____8207 with
                                              | (x, uu____8216) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x)) in
                                    (uu____8188, expected_t) in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8260 ->
                                            match uu____8260 with
                                            | (bv, uu____8268) ->
                                                let uu____8273 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_All.pipe_right
                                                  uu____8273
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      FStar_Pervasives_Native.None
                                      lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | uu____8303 -> err_value_restriction lbdef1)))
               | uu____8323 -> no_gen ()) in
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
           fun uu____8474 ->
             match uu____8474 with
             | (lbname, e_tag, (typ, (binders, mltyscheme)), add_unit, _body)
                 ->
                 let uu____8535 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec in
                 (match uu____8535 with
                  | (env1, uu____8552, exp_binding) ->
                      let uu____8556 =
                        let uu____8561 = FStar_Util.right lbname in
                        (uu____8561, exp_binding) in
                      (env1, uu____8556))) g lbs1
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
            (fun uu____8627 ->
               let uu____8628 = FStar_Syntax_Print.term_to_string e in
               let uu____8630 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty in
               FStar_Util.print2 "Checking %s at type %s\n" uu____8628
                 uu____8630);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST, uu____8637) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE,
              FStar_Extraction_ML_Syntax.MLTY_Erased) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8638 ->
               let uu____8643 = term_as_mlexpr g e in
               (match uu____8643 with
                | (ml_e, tag, t) ->
                    let uu____8657 = maybe_promote_effect ml_e tag t in
                    (match uu____8657 with
                     | (ml_e1, tag1) ->
                         let uu____8668 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f in
                         if uu____8668
                         then
                           let uu____8675 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty in
                           (uu____8675, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST,
                               FStar_Extraction_ML_Syntax.E_PURE,
                               FStar_Extraction_ML_Syntax.MLTY_Erased) ->
                                let uu____8682 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty in
                                (uu____8682, ty)
                            | uu____8683 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____8691 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty in
                                  (uu____8691, ty)))))))
and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun e ->
      let uu____8694 = term_as_mlexpr' g e in
      match uu____8694 with
      | (e1, f, t) ->
          let uu____8710 = maybe_promote_effect e1 f t in
          (match uu____8710 with | (e2, f1) -> (e2, f1, t))
and (term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun top ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u ->
           let uu____8735 =
             let uu____8737 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____8739 = FStar_Syntax_Print.tag_of_term top in
             let uu____8741 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____8737 uu____8739 uu____8741 in
           FStar_Util.print_string uu____8735);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu____8751 =
             let uu____8753 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8753 in
           failwith uu____8751
       | FStar_Syntax_Syntax.Tm_delayed uu____8762 ->
           let uu____8785 =
             let uu____8787 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8787 in
           failwith uu____8785
       | FStar_Syntax_Syntax.Tm_uvar uu____8796 ->
           let uu____8809 =
             let uu____8811 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8811 in
           failwith uu____8809
       | FStar_Syntax_Syntax.Tm_bvar uu____8820 ->
           let uu____8821 =
             let uu____8823 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8823 in
           failwith uu____8821
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____8833 = FStar_Syntax_Util.unfold_lazy i in
           term_as_mlexpr g uu____8833
       | FStar_Syntax_Syntax.Tm_type uu____8834 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____8835 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____8842 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
              FStar_Syntax_Syntax.antiquotes = uu____8858;_})
           ->
           let uu____8871 =
             let uu____8872 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____8872 in
           (match uu____8871 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____8879;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____8881;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____8882;_} ->
                let uu____8885 =
                  let uu____8886 =
                    let uu____8887 =
                      let uu____8894 =
                        let uu____8897 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime")) in
                        [uu____8897] in
                      (fw, uu____8894) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____8887 in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____8886 in
                (uu____8885, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
              FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____8915 = FStar_Reflection_Basic.inspect_ln qt in
           (match uu____8915 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____8923 = FStar_Syntax_Syntax.lookup_aq bv aqs in
                (match uu____8923 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None ->
                     let tv =
                       let uu____8934 =
                         let uu____8941 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs in
                         FStar_Syntax_Embeddings.embed uu____8941
                           (FStar_Reflection_Data.Tv_Var bv) in
                       uu____8934 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb in
                     let t1 =
                       let uu____8949 =
                         let uu____8960 = FStar_Syntax_Syntax.as_arg tv in
                         [uu____8960] in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____8949 in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____8987 =
                    let uu____8994 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs in
                    FStar_Syntax_Embeddings.embed uu____8994 tv in
                  uu____8987 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb in
                let t1 =
                  let uu____9002 =
                    let uu____9013 = FStar_Syntax_Syntax.as_arg tv1 in
                    [uu____9013] in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9002 in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____9040)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9073 =
                  let uu____9080 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.env_tcenv m in
                  FStar_Util.must uu____9080 in
                (match uu____9073 with
                 | (ed, qualifiers) ->
                     let uu____9107 =
                       let uu____9109 =
                         FStar_TypeChecker_Env.is_reifiable_effect
                           g.FStar_Extraction_ML_UEnv.env_tcenv
                           ed.FStar_Syntax_Syntax.mname in
                       Prims.op_Negation uu____9109 in
                     if uu____9107
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9127 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1, uu____9129) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1, uu____9135) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9141 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.env_tcenv t in
           (match uu____9141 with
            | (uu____9154, ty, uu____9156) ->
                let ml_ty = term_as_mlty g ty in
                let uu____9158 =
                  let uu____9159 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9159 in
                (uu____9158, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9160 ->
           let uu____9161 = is_type g t in
           if uu____9161
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9172 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____9172 with
              | (FStar_Util.Inl uu____9185, uu____9186) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9191;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9194;_},
                 qual) ->
                  (match mltys with
                   | ([], t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([], t1) ->
                       let uu____9212 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____9212, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9213 -> instantiate_maybe_partial x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9215 = is_type g t in
           if uu____9215
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9226 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv in
              match uu____9226 with
              | FStar_Pervasives_Native.None ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9235;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9238;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9246 ->
                        let uu____9247 = FStar_Syntax_Print.fv_to_string fv in
                        let uu____9249 =
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            g.FStar_Extraction_ML_UEnv.currentModule x in
                        let uu____9251 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule
                            (FStar_Pervasives_Native.snd mltys) in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9247 uu____9249 uu____9251);
                   (match mltys with
                    | ([], t1) when
                        t1 = FStar_Extraction_ML_Syntax.ml_unit_ty ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([], t1) ->
                        let uu____9264 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x in
                        (uu____9264, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9265 -> instantiate_maybe_partial x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs, body, rcopt) ->
           let uu____9293 = FStar_Syntax_Subst.open_term bs body in
           (match uu____9293 with
            | (bs1, body1) ->
                let uu____9306 = binders_as_ml_binders g bs1 in
                (match uu____9306 with
                 | (ml_bs, env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9342 =
                             FStar_TypeChecker_Env.is_reifiable_rc
                               env.FStar_Extraction_ML_UEnv.env_tcenv rc in
                           if uu____9342
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.env_tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9350 ->
                                 let uu____9351 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9351);
                            body1) in
                     let uu____9354 = term_as_mlexpr env body2 in
                     (match uu____9354 with
                      | (ml_body, f, t1) ->
                          let uu____9370 =
                            FStar_List.fold_right
                              (fun uu____9390 ->
                                 fun uu____9391 ->
                                   match (uu____9390, uu____9391) with
                                   | ((uu____9414, targ), (f1, t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____9370 with
                           | (f1, tfun) ->
                               let uu____9437 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____9437, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____9445;
              FStar_Syntax_Syntax.vars = uu____9446;_},
            (a1, uu____9448)::[])
           ->
           let ty =
             let uu____9488 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
             term_as_mlty g uu____9488 in
           let uu____9489 =
             let uu____9490 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____9490 in
           (uu____9489, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____9491;
              FStar_Syntax_Syntax.vars = uu____9492;_},
            (t1, uu____9494)::(r, uu____9496)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____9551);
              FStar_Syntax_Syntax.pos = uu____9552;
              FStar_Syntax_Syntax.vars = uu____9553;_},
            uu____9554)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1, args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_9623 ->
                        match uu___1_9623 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | uu____9626 -> false))) in
           let uu____9628 =
             let uu____9633 =
               let uu____9634 = FStar_Syntax_Subst.compress head1 in
               uu____9634.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____9633) in
           (match uu____9628 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____9643, uu____9644) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Iota;
                    FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.env_tcenv t in
                term_as_mlexpr g t1
            | (uu____9658, FStar_Syntax_Syntax.Tm_abs
               (bs, uu____9660, FStar_Pervasives_Native.Some rc)) when
                is_total rc ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Iota;
                    FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.env_tcenv t in
                term_as_mlexpr g t1
            | (uu____9685, FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify)) ->
                let e =
                  let uu____9687 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.env_tcenv head1 uu____9687 in
                let tm =
                  let uu____9699 =
                    let uu____9704 = FStar_TypeChecker_Util.remove_reify e in
                    let uu____9705 = FStar_List.tl args in
                    FStar_Syntax_Syntax.mk_Tm_app uu____9704 uu____9705 in
                  uu____9699 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr g tm
            | uu____9714 ->
                let rec extract_app is_data uu____9767 uu____9768 restArgs =
                  match (uu____9767, uu____9768) with
                  | ((mlhead, mlargs_f), (f, t1)) ->
                      let mk_head uu____9849 =
                        let mlargs =
                          FStar_All.pipe_right (FStar_List.rev mlargs_f)
                            (FStar_List.map FStar_Pervasives_Native.fst) in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty t1)
                          (FStar_Extraction_ML_Syntax.MLE_App
                             (mlhead, mlargs)) in
                      (FStar_Extraction_ML_UEnv.debug g
                         (fun uu____9876 ->
                            let uu____9877 =
                              let uu____9879 = mk_head () in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                uu____9879 in
                            let uu____9880 =
                              FStar_Extraction_ML_Code.string_of_mlty
                                g.FStar_Extraction_ML_UEnv.currentModule t1 in
                            let uu____9882 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1, uu____9893)::uu____9894 ->
                                  FStar_Syntax_Print.term_to_string hd1 in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____9877 uu____9880 uu____9882);
                       (match (restArgs, t1) with
                        | ([], uu____9928) ->
                            let app =
                              let uu____9944 = mk_head () in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____9944 in
                            (app, f, t1)
                        | ((arg, uu____9946)::rest,
                           FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t, f', t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____9977 =
                              let uu____9982 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f' in
                              (uu____9982, t2) in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____9977 rest
                        | ((e0, uu____9994)::rest,
                           FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected, f', t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos in
                            let expected_effect =
                              let uu____10027 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1) in
                              if uu____10027
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE in
                            let uu____10032 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected in
                            (match uu____10032 with
                             | (e01, tInferred) ->
                                 let uu____10045 =
                                   let uu____10050 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f'] in
                                   (uu____10050, t2) in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10045 rest)
                        | uu____10061 ->
                            let uu____10074 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1 in
                            (match uu____10074 with
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
                                        let head2 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.MLTY_Top)
                                            (FStar_Extraction_ML_Syntax.MLE_App
                                               (mlhead, mlargs)) in
                                        maybe_coerce
                                          top.FStar_Syntax_Syntax.pos g head2
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t2 in
                                      extract_app is_data (mlhead1, [])
                                        (f, t2) restArgs
                                  | uu____10146 ->
                                      let mlhead1 =
                                        let mlargs =
                                          FStar_All.pipe_right
                                            (FStar_List.rev mlargs_f)
                                            (FStar_List.map
                                               FStar_Pervasives_Native.fst) in
                                        let head2 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.MLTY_Top)
                                            (FStar_Extraction_ML_Syntax.MLE_App
                                               (mlhead, mlargs)) in
                                        maybe_coerce
                                          top.FStar_Syntax_Syntax.pos g head2
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t1 in
                                      err_ill_typed_application g top mlhead1
                                        restArgs t1)))) in
                let extract_app_maybe_projector is_data mlhead uu____10217
                  args1 =
                  match uu____10217 with
                  | (f, t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10247)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10331))::args3,
                                FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____10333, f', t3)) ->
                                 let uu____10371 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____10371 t3
                             | uu____10372 -> (args2, f1, t2) in
                           let uu____10397 = remove_implicits args1 f t1 in
                           (match uu____10397 with
                            | (args2, f1, t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____10453 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let extract_app_with_instantiations uu____10477 =
                  let head2 = FStar_Syntax_Util.un_uinst head1 in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____10485 ->
                      let uu____10486 =
                        let uu____10507 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2 in
                        match uu____10507 with
                        | (FStar_Util.Inr exp_b, q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____10546 ->
                                  let uu____10547 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu____10549 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr in
                                  let uu____10551 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme) in
                                  let uu____10553 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____10547 uu____10549 uu____10551
                                    uu____10553);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____10580 -> failwith "FIXME Ty" in
                      (match uu____10486 with
                       | ((head_ml, (vars, t1), inst_ok), qual) ->
                           let has_typ_apps =
                             match args with
                             | (a, uu____10656)::uu____10657 -> is_type g a
                             | uu____10684 -> false in
                           let uu____10696 =
                             match vars with
                             | uu____10725::uu____10726 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____10740 ->
                                 let n1 = FStar_List.length vars in
                                 let uu____10746 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____10784 =
                                       FStar_List.map
                                         (fun uu____10796 ->
                                            match uu____10796 with
                                            | (x, uu____10804) ->
                                                term_as_mlty g x) args in
                                     (uu____10784, [])
                                   else
                                     (let uu____10827 =
                                        FStar_Util.first_N n1 args in
                                      match uu____10827 with
                                      | (prefix1, rest) ->
                                          let uu____10916 =
                                            FStar_List.map
                                              (fun uu____10928 ->
                                                 match uu____10928 with
                                                 | (x, uu____10936) ->
                                                     term_as_mlty g x)
                                              prefix1 in
                                          (uu____10916, rest)) in
                                 (match uu____10746 with
                                  | (provided_type_args, rest) ->
                                      let uu____10987 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____10996 ->
                                            let uu____10997 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args in
                                            (match uu____10997 with
                                             | (head3, uu____11009, t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____11011 ->
                                            let uu____11013 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args in
                                            (match uu____11013 with
                                             | (head3, uu____11025, t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,
                                             {
                                               FStar_Extraction_ML_Syntax.expr
                                                 =
                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                 (FStar_Extraction_ML_Syntax.MLC_Unit);
                                               FStar_Extraction_ML_Syntax.mlty
                                                 = uu____11028;
                                               FStar_Extraction_ML_Syntax.loc
                                                 = uu____11029;_}::[])
                                            ->
                                            let uu____11032 =
                                              instantiate_maybe_partial head3
                                                (vars, t1) provided_type_args in
                                            (match uu____11032 with
                                             | (head4, uu____11044, t2) ->
                                                 let uu____11046 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2) in
                                                 (uu____11046, t2))
                                        | uu____11049 ->
                                            failwith
                                              "Impossible: Unexpected head term" in
                                      (match uu____10987 with
                                       | (head3, t2) -> (head3, t2, rest))) in
                           (match uu____10696 with
                            | (head_ml1, head_t, args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11116 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1 in
                                     (uu____11116,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11117 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11126 ->
                      let uu____11127 =
                        let uu____11148 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2 in
                        match uu____11148 with
                        | (FStar_Util.Inr exp_b, q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11187 ->
                                  let uu____11188 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let uu____11190 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr in
                                  let uu____11192 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme) in
                                  let uu____11194 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11188 uu____11190 uu____11192
                                    uu____11194);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11221 -> failwith "FIXME Ty" in
                      (match uu____11127 with
                       | ((head_ml, (vars, t1), inst_ok), qual) ->
                           let has_typ_apps =
                             match args with
                             | (a, uu____11297)::uu____11298 -> is_type g a
                             | uu____11325 -> false in
                           let uu____11337 =
                             match vars with
                             | uu____11366::uu____11367 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11381 ->
                                 let n1 = FStar_List.length vars in
                                 let uu____11387 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____11425 =
                                       FStar_List.map
                                         (fun uu____11437 ->
                                            match uu____11437 with
                                            | (x, uu____11445) ->
                                                term_as_mlty g x) args in
                                     (uu____11425, [])
                                   else
                                     (let uu____11468 =
                                        FStar_Util.first_N n1 args in
                                      match uu____11468 with
                                      | (prefix1, rest) ->
                                          let uu____11557 =
                                            FStar_List.map
                                              (fun uu____11569 ->
                                                 match uu____11569 with
                                                 | (x, uu____11577) ->
                                                     term_as_mlty g x)
                                              prefix1 in
                                          (uu____11557, rest)) in
                                 (match uu____11387 with
                                  | (provided_type_args, rest) ->
                                      let uu____11628 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____11637 ->
                                            let uu____11638 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args in
                                            (match uu____11638 with
                                             | (head3, uu____11650, t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____11652 ->
                                            let uu____11654 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args in
                                            (match uu____11654 with
                                             | (head3, uu____11666, t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,
                                             {
                                               FStar_Extraction_ML_Syntax.expr
                                                 =
                                                 FStar_Extraction_ML_Syntax.MLE_Const
                                                 (FStar_Extraction_ML_Syntax.MLC_Unit);
                                               FStar_Extraction_ML_Syntax.mlty
                                                 = uu____11669;
                                               FStar_Extraction_ML_Syntax.loc
                                                 = uu____11670;_}::[])
                                            ->
                                            let uu____11673 =
                                              instantiate_maybe_partial head3
                                                (vars, t1) provided_type_args in
                                            (match uu____11673 with
                                             | (head4, uu____11685, t2) ->
                                                 let uu____11687 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2) in
                                                 (uu____11687, t2))
                                        | uu____11690 ->
                                            failwith
                                              "Impossible: Unexpected head term" in
                                      (match uu____11628 with
                                       | (head3, t2) -> (head3, t2, rest))) in
                           (match uu____11337 with
                            | (head_ml1, head_t, args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11757 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1 in
                                     (uu____11757,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11758 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____11767 ->
                      let uu____11768 = term_as_mlexpr g head2 in
                      (match uu____11768 with
                       | (head3, f, t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args) in
                let uu____11784 = is_type g t in
                if uu____11784
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____11795 =
                     let uu____11796 = FStar_Syntax_Util.un_uinst head1 in
                     uu____11796.FStar_Syntax_Syntax.n in
                   match uu____11795 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____11806 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv in
                       (match uu____11806 with
                        | FStar_Pervasives_Native.None ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____11815 -> extract_app_with_instantiations ())
                   | uu____11818 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____11821), f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c) in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l in
           let uu____11889 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____11889 with | (e, t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____11924 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____11940 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____11940
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____11955 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____11955 in
                   let lb1 =
                     let uu___1710_11957 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1710_11957.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1710_11957.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1710_11957.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1710_11957.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1710_11957.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1710_11957.FStar_Syntax_Syntax.lbpos)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____11924 with
            | (lbs1, e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb ->
                            let tcenv =
                              let uu____11991 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.env_tcenv
                                uu____11991 in
                            let lbdef =
                              let uu____12006 = FStar_Options.ml_ish () in
                              if uu____12006
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____12018 =
                                   FStar_TypeChecker_Normalize.normalize
                                     (FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                     :: extraction_norm_steps) tcenv
                                     lb.FStar_Syntax_Syntax.lbdef in
                                 let uu____12019 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm")) in
                                 if uu____12019
                                 then
                                   ((let uu____12029 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname in
                                     let uu____12031 =
                                       FStar_Syntax_Print.term_to_string
                                         lb.FStar_Syntax_Syntax.lbdef in
                                     FStar_Util.print2
                                       "Starting to normalize top-level let %s)\n\tlbdef=%s"
                                       uu____12029 uu____12031);
                                    (let a =
                                       let uu____12037 =
                                         let uu____12039 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____12039 in
                                       FStar_Util.measure_execution_time
                                         uu____12037 norm_call in
                                     (let uu____12045 =
                                        FStar_Syntax_Print.term_to_string a in
                                      FStar_Util.print1 "Normalized to %s\n"
                                        uu____12045);
                                     a))
                                 else norm_call ()) in
                            let uu___1728_12050 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1728_12050.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1728_12050.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1728_12050.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1728_12050.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1728_12050.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1728_12050.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1 in
                let check_lb env uu____12103 =
                  match uu____12103 with
                  | (nm, (_lbname, f, (_t, (targs, polytype)), add_unit, e))
                      ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1 ->
                             fun uu____12259 ->
                               match uu____12259 with
                               | (a, uu____12267) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs in
                      let expected_t = FStar_Pervasives_Native.snd polytype in
                      let uu____12273 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____12273 with
                       | (e1, ty) ->
                           let uu____12284 =
                             maybe_promote_effect e1 f expected_t in
                           (match uu____12284 with
                            | (e2, f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE,
                                     FStar_Extraction_ML_Syntax.MLTY_Erased)
                                      -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST,
                                     FStar_Extraction_ML_Syntax.MLTY_Erased)
                                      -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____12296 -> [] in
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
                let uu____12327 =
                  FStar_List.fold_right
                    (fun lb ->
                       fun uu____12424 ->
                         match uu____12424 with
                         | (env, lbs4) ->
                             let uu____12558 = lb in
                             (match uu____12558 with
                              | (lbname, uu____12609,
                                 (t1, (uu____12611, polytype)), add_unit,
                                 uu____12614) ->
                                  let uu____12629 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____12629 with
                                   | (env1, nm, uu____12670) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, []) in
                (match uu____12327 with
                 | (env_body, lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____12949 = term_as_mlexpr env_body e'1 in
                     (match uu____12949 with
                      | (e'2, f', t') ->
                          let f =
                            let uu____12966 =
                              let uu____12969 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5 in
                              f' :: uu____12969 in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____12966 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____12982 =
                            let uu____12983 =
                              let uu____12984 =
                                let uu____12985 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5 in
                                (is_rec1, uu____12985) in
                              mk_MLE_Let top_level uu____12984 e'2 in
                            let uu____12994 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____12983 uu____12994 in
                          (uu____12982, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee, pats) ->
           let uu____13033 = term_as_mlexpr g scrutinee in
           (match uu____13033 with
            | (e, f_e, t_e) ->
                let uu____13049 = check_pats_for_ite pats in
                (match uu____13049 with
                 | (b, then_e, else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some then_e1,
                           FStar_Pervasives_Native.Some else_e1) ->
                            let uu____13114 = term_as_mlexpr g then_e1 in
                            (match uu____13114 with
                             | (then_mle, f_then, t_then) ->
                                 let uu____13130 = term_as_mlexpr g else_e1 in
                                 (match uu____13130 with
                                  | (else_mle, f_else, t_else) ->
                                      let uu____13146 =
                                        let uu____13157 =
                                          type_leq g t_then t_else in
                                        if uu____13157
                                        then (t_else, no_lift)
                                        else
                                          (let uu____13178 =
                                             type_leq g t_else t_then in
                                           if uu____13178
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____13146 with
                                       | (t_branch, maybe_lift1) ->
                                           let uu____13225 =
                                             let uu____13226 =
                                               let uu____13227 =
                                                 let uu____13236 =
                                                   maybe_lift1 then_mle
                                                     t_then in
                                                 let uu____13237 =
                                                   let uu____13240 =
                                                     maybe_lift1 else_mle
                                                       t_else in
                                                   FStar_Pervasives_Native.Some
                                                     uu____13240 in
                                                 (e, uu____13236,
                                                   uu____13237) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____13227 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____13226 in
                                           let uu____13243 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____13225, uu____13243,
                                             t_branch))))
                        | uu____13244 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____13262 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat ->
                                  fun br ->
                                    let uu____13361 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____13361 with
                                    | (pat, when_opt, branch1) ->
                                        let uu____13406 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr in
                                        (match uu____13406 with
                                         | (env, p, pat_t_compat) ->
                                             let uu____13468 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let w_pos =
                                                     w.FStar_Syntax_Syntax.pos in
                                                   let uu____13491 =
                                                     term_as_mlexpr env w in
                                                   (match uu____13491 with
                                                    | (w1, f_w, t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w)) in
                                             (match uu____13468 with
                                              | (when_opt1, f_when) ->
                                                  let uu____13541 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____13541 with
                                                   | (mlbranch, f_branch,
                                                      t_branch) ->
                                                       let uu____13576 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____13653
                                                                 ->
                                                                 match uu____13653
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
                                                         uu____13576)))))
                               true) in
                        match uu____13262 with
                        | (pat_t_compat, mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____13824 ->
                                      let uu____13825 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____13827 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____13825 uu____13827);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____13854 =
                                   let uu____13855 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____13855 in
                                 (match uu____13854 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____13862;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____13864;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____13865;_}
                                      ->
                                      let uu____13868 =
                                        let uu____13869 =
                                          let uu____13870 =
                                            let uu____13877 =
                                              let uu____13880 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____13880] in
                                            (fw, uu____13877) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____13870 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____13869 in
                                      (uu____13868,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____13884, uu____13885,
                                (uu____13886, f_first, t_first))::rest ->
                                 let uu____13946 =
                                   FStar_List.fold_left
                                     (fun uu____13988 ->
                                        fun uu____13989 ->
                                          match (uu____13988, uu____13989)
                                          with
                                          | ((topt, f),
                                             (uu____14046, uu____14047,
                                              (uu____14048, f_branch,
                                               t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch in
                                              let topt1 =
                                                match topt with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    t1 ->
                                                    let uu____14104 =
                                                      type_leq g t1 t_branch in
                                                    if uu____14104
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____14111 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____14111
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           t1
                                                       else
                                                         FStar_Pervasives_Native.None) in
                                              (topt1, f1))
                                     ((FStar_Pervasives_Native.Some t_first),
                                       f_first) rest in
                                 (match uu____13946 with
                                  | (topt, f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____14209 ->
                                                match uu____14209 with
                                                | (p, (wopt, uu____14238),
                                                   (b1, uu____14240, t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____14259 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | FStar_Pervasives_Native.Some t1 ->
                                            t1 in
                                      let uu____14264 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____14264, f_match, t_match)))))))
let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env ->
    fun discName ->
      fun constrName ->
        let uu____14291 =
          let uu____14296 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.env_tcenv discName in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____14296 in
        match uu____14291 with
        | (uu____14321, fstar_disc_type) ->
            let wildcards =
              let uu____14331 =
                let uu____14332 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____14332.FStar_Syntax_Syntax.n in
              match uu____14331 with
              | FStar_Syntax_Syntax.Tm_arrow (binders, uu____14343) ->
                  let uu____14364 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_14398 ->
                            match uu___2_14398 with
                            | (uu____14406, FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____14407)) ->
                                true
                            | uu____14412 -> false)) in
                  FStar_All.pipe_right uu____14364
                    (FStar_List.map
                       (fun uu____14448 ->
                          let uu____14455 = fresh "_" in
                          (uu____14455, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____14459 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____14474 =
                let uu____14475 =
                  let uu____14487 =
                    let uu____14488 =
                      let uu____14489 =
                        let uu____14504 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid)) in
                        let uu____14510 =
                          let uu____14521 =
                            let uu____14530 =
                              let uu____14531 =
                                let uu____14538 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____14538,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____14531 in
                            let uu____14541 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____14530, FStar_Pervasives_Native.None,
                              uu____14541) in
                          let uu____14545 =
                            let uu____14556 =
                              let uu____14565 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____14565) in
                            [uu____14556] in
                          uu____14521 :: uu____14545 in
                        (uu____14504, uu____14510) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____14489 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____14488 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____14487) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____14475 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____14474 in
            let uu____14626 =
              let uu____14627 =
                let uu____14630 =
                  let uu____14631 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____14631;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____14630] in
              (FStar_Extraction_ML_Syntax.NonRec, uu____14627) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____14626