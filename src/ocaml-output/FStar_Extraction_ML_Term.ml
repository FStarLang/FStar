open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Un_extractable -> true | uu____6 -> false
let (type_leq :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Extraction_ML_Util.type_leq
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
let (type_leq_c :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool,
            FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Extraction_ML_Util.type_leq_c
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
let (eraseTypeDeep :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t ->
      FStar_Extraction_ML_Util.eraseTypeDeep
        (FStar_Extraction_ML_Util.udelta_unfold g) t
let record_fields :
  'Auu____68 .
    FStar_Ident.ident Prims.list ->
      'Auu____68 Prims.list ->
        (Prims.string, 'Auu____68) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs ->
    fun vs ->
      FStar_List.map2 (fun f -> fun e -> ((f.FStar_Ident.idText), e)) fs vs
let fail :
  'Auu____107 .
    FStar_Range.range ->
      (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2
        -> 'Auu____107
  = fun r -> fun err -> FStar_Errors.raise_error err r
let err_uninst :
  'Auu____136 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (Prims.string Prims.list, FStar_Extraction_ML_Syntax.mlty)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.term -> 'Auu____136
  =
  fun env ->
    fun t ->
      fun uu____161 ->
        fun app ->
          match uu____161 with
          | (vars, ty) ->
              let uu____175 =
                let uu____180 =
                  let uu____181 = FStar_Syntax_Print.term_to_string t in
                  let uu____182 =
                    FStar_All.pipe_right vars (FStar_String.concat ", ") in
                  let uu____185 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      env.FStar_Extraction_ML_UEnv.currentModule ty in
                  let uu____186 = FStar_Syntax_Print.term_to_string app in
                  FStar_Util.format4
                    "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                    uu____181 uu____182 uu____185 uu____186 in
                (FStar_Errors.Fatal_Uninstantiated, uu____180) in
              fail t.FStar_Syntax_Syntax.pos uu____175
let err_ill_typed_application :
  'Auu____199 'Auu____200 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term, 'Auu____199)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Extraction_ML_Syntax.mlty -> 'Auu____200
  =
  fun env ->
    fun t ->
      fun args ->
        fun ty ->
          let uu____233 =
            let uu____238 =
              let uu____239 = FStar_Syntax_Print.term_to_string t in
              let uu____240 =
                let uu____241 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____259 ->
                          match uu____259 with
                          | (x, uu____265) ->
                              FStar_Syntax_Print.term_to_string x)) in
                FStar_All.pipe_right uu____241 (FStar_String.concat " ") in
              let uu____268 =
                FStar_Extraction_ML_Code.string_of_mlty
                  env.FStar_Extraction_ML_UEnv.currentModule ty in
              FStar_Util.format3
                "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
                uu____239 uu____240 uu____268 in
            (FStar_Errors.Fatal_IllTyped, uu____238) in
          fail t.FStar_Syntax_Syntax.pos uu____233
let err_ill_typed_erasure :
  'Auu____277 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____277
  =
  fun env ->
    fun pos ->
      fun ty ->
        let uu____293 =
          let uu____298 =
            let uu____299 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____299 in
          (FStar_Errors.Fatal_IllTyped, uu____298) in
        fail pos uu____293
let err_value_restriction :
  'Auu____304 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____304
  =
  fun t ->
    let uu____314 =
      let uu____319 =
        let uu____320 = FStar_Syntax_Print.tag_of_term t in
        let uu____321 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____320 uu____321 in
      (FStar_Errors.Fatal_ValueRestriction, uu____319) in
    fail t.FStar_Syntax_Syntax.pos uu____314
let (err_unexpected_eff :
  FStar_Extraction_ML_UEnv.env ->
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
            let uu____351 =
              let uu____356 =
                let uu____357 = FStar_Syntax_Print.term_to_string t in
                let uu____358 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty in
                let uu____359 = FStar_Extraction_ML_Util.eff_to_string f0 in
                let uu____360 = FStar_Extraction_ML_Util.eff_to_string f1 in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____357 uu____358 uu____359 uu____360 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____356) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____351
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  let rec delta_norm_eff g l =
    let uu____383 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
    match uu____383 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None ->
        let res =
          let uu____388 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l in
          match uu____388 with
          | FStar_Pervasives_Native.None -> l
          | FStar_Pervasives_Native.Some (uu____399, c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c) in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res) in
  fun g ->
    fun l ->
      let l1 = delta_norm_eff g l in
      let uu____409 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid in
      if uu____409
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____411 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid in
         if uu____411
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.tcenv l1 in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                let uu____434 =
                  FStar_All.pipe_right qualifiers
                    (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                if uu____434
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
let rec (is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____455 =
        let uu____456 = FStar_Syntax_Subst.compress t1 in
        uu____456.FStar_Syntax_Syntax.n in
      match uu____455 with
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____459 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____484 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____511 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____519 = FStar_Syntax_Util.unfold_lazy i in
          is_arity env uu____519
      | FStar_Syntax_Syntax.Tm_uvar uu____520 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____537 -> false
      | FStar_Syntax_Syntax.Tm_name uu____538 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____539 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____546 -> false
      | FStar_Syntax_Syntax.Tm_type uu____547 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____548, c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____566 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1 in
          let uu____568 =
            let uu____569 = FStar_Syntax_Subst.compress t2 in
            uu____569.FStar_Syntax_Syntax.n in
          (match uu____568 with
           | FStar_Syntax_Syntax.Tm_fvar uu____572 -> false
           | uu____573 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____574 ->
          let uu____589 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____589 with | (head1, uu____605) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1, uu____627) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x, uu____633) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____638, body, uu____640) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____661, body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____679, branches) ->
          (match branches with
           | (uu____717, uu____718, e)::uu____720 -> is_arity env e
           | uu____767 -> false)
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____795 ->
          let uu____820 =
            let uu____821 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____821 in
          failwith uu____820
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____822 =
            let uu____823 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____823 in
          failwith uu____822
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____825 = FStar_Syntax_Util.unfold_lazy i in
          is_type_aux env uu____825
      | FStar_Syntax_Syntax.Tm_constant uu____826 -> false
      | FStar_Syntax_Syntax.Tm_type uu____827 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____828 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____835 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar (uu____850, t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____876;
            FStar_Syntax_Syntax.index = uu____877;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____881;
            FStar_Syntax_Syntax.index = uu____882;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____887, uu____888) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____930) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____937) ->
          let uu____958 = FStar_Syntax_Subst.open_term bs body in
          (match uu____958 with | (uu____963, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
          let uu____980 =
            let uu____985 =
              let uu____986 = FStar_Syntax_Syntax.mk_binder x in [uu____986] in
            FStar_Syntax_Subst.open_term uu____985 body in
          (match uu____980 with | (uu____987, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____989, lbs), body) ->
          let uu____1006 = FStar_Syntax_Subst.open_let_rec lbs body in
          (match uu____1006 with
           | (uu____1013, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1019, branches) ->
          (match branches with
           | b::uu____1058 ->
               let uu____1103 = FStar_Syntax_Subst.open_branch b in
               (match uu____1103 with
                | (uu____1104, uu____1105, e) -> is_type_aux env e)
           | uu____1123 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1140 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2, uu____1148) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1, uu____1154) ->
          is_type_aux env head1
let (is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1189 ->
           let uu____1190 = FStar_Syntax_Print.tag_of_term t in
           let uu____1191 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1190
             uu____1191);
      (let b = is_type_aux env t in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1197 ->
            if b
            then
              let uu____1198 = FStar_Syntax_Print.term_to_string t in
              let uu____1199 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1198 uu____1199
            else
              (let uu____1201 = FStar_Syntax_Print.term_to_string t in
               let uu____1202 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1201 uu____1202));
       b)
let is_type_binder :
  'Auu____1209 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv, 'Auu____1209) FStar_Pervasives_Native.tuple2
        -> Prims.bool
  =
  fun env ->
    fun x ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1233 =
      let uu____1234 = FStar_Syntax_Subst.compress t in
      uu____1234.FStar_Syntax_Syntax.n in
    match uu____1233 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1237;
          FStar_Syntax_Syntax.fv_delta = uu____1238;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor);_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1239;
          FStar_Syntax_Syntax.fv_delta = uu____1240;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1241);_}
        -> true
    | uu____1248 -> false
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1254 =
      let uu____1255 = FStar_Syntax_Subst.compress t in
      uu____1255.FStar_Syntax_Syntax.n in
    match uu____1254 with
    | FStar_Syntax_Syntax.Tm_constant uu____1258 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1259 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1260 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1261 -> true
    | FStar_Syntax_Syntax.Tm_app (head1, args) ->
        let uu____1300 = is_constructor head1 in
        if uu____1300
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1316 ->
                  match uu____1316 with
                  | (te, uu____1322) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1, uu____1325) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1331, uu____1332) ->
        is_fstar_value t1
    | uu____1373 -> false
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1379 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1380 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1381 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1382 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1393, exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1402, fields) ->
        FStar_Util.for_all
          (fun uu____1427 ->
             match uu____1427 with | (uu____1432, e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h, uu____1435) -> is_ml_value h
    | uu____1440 -> false
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x ->
    FStar_Util.incr c;
    (let uu____1555 =
       let uu____1556 = FStar_ST.op_Bang c in
       FStar_Util.string_of_int uu____1556 in
     Prims.strcat x uu____1555)
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0 ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1721 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____1723 = FStar_Syntax_Util.is_fun e' in
          if uu____1723
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 FStar_Pervasives_Native.None
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1729 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1729
let (check_pats_for_ite :
  (FStar_Syntax_Syntax.pat,
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,
    FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple3 Prims.list ->
    (Prims.bool, FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3)
  =
  fun l ->
    let def =
      (false, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) in
    if (FStar_List.length l) <> (Prims.parse_int "2")
    then def
    else
      (let uu____1809 = FStar_List.hd l in
       match uu____1809 with
       | (p1, w1, e1) ->
           let uu____1843 =
             let uu____1852 = FStar_List.tl l in FStar_List.hd uu____1852 in
           (match uu____1843 with
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
                 | uu____1926 -> def)))
let (instantiate :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  = fun s -> fun args -> FStar_Extraction_ML_Util.subst s args
let (eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun t ->
    fun e ->
      let uu____1963 = FStar_Extraction_ML_Util.doms_and_cod t in
      match uu____1963 with
      | (ts, r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1983 -> fresh "a") ts in
             let vs_ts = FStar_List.zip vs ts in
             let vs_es =
               let uu____1994 = FStar_List.zip vs ts in
               FStar_List.map
                 (fun uu____2008 ->
                    match uu____2008 with
                    | (v1, t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1994 in
             let body =
               FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r)
                 (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es)) in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
let (default_value_for_ty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun t ->
      let uu____2034 = FStar_Extraction_ML_Util.doms_and_cod t in
      match uu____2034 with
      | (ts, r) ->
          let body r1 =
            let r2 =
              let uu____2054 = FStar_Extraction_ML_Util.udelta_unfold g r1 in
              match uu____2054 with
              | FStar_Pervasives_Native.None -> r1
              | FStar_Pervasives_Native.Some r2 -> r2 in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2058 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2)) in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____2066 -> fresh "a") ts in
             let vs_ts = FStar_List.zip vs ts in
             let uu____2074 =
               let uu____2075 =
                 let uu____2086 = body r in (vs_ts, uu____2086) in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____2075 in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____2074)
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect ->
    fun e ->
      let uu____2103 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____2105 = FStar_Options.codegen () in
           uu____2105 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)) in
      if uu____2103 then e else eta_expand expect e
let maybe_coerce :
  'Auu____2123 .
    'Auu____2123 ->
      FStar_Extraction_ML_UEnv.env ->
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
            let uu____2150 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect in
            match uu____2150 with
            | (true, FStar_Pervasives_Native.Some e') -> e'
            | uu____2160 ->
                (FStar_Extraction_ML_UEnv.debug g
                   (fun uu____2172 ->
                      let uu____2173 =
                        FStar_Extraction_ML_Code.string_of_mlexpr
                          g.FStar_Extraction_ML_UEnv.currentModule e in
                      let uu____2174 =
                        FStar_Extraction_ML_Code.string_of_mlty
                          g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                      let uu____2175 =
                        FStar_Extraction_ML_Code.string_of_mlty
                          g.FStar_Extraction_ML_UEnv.currentModule expect in
                      FStar_Util.print3
                        "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                        uu____2173 uu____2174 uu____2175);
                 (match ty1 with
                  | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                      default_value_for_ty g expect
                  | uu____2176 ->
                      let uu____2177 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty expect)
                          (FStar_Extraction_ML_Syntax.MLE_Coerce
                             (e, ty1, expect)) in
                      maybe_eta_expand expect uu____2177))
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun bv ->
      let uu____2188 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____2188 with
      | FStar_Util.Inl (uu____2189, t) -> t
      | uu____2203 -> FStar_Extraction_ML_Syntax.MLTY_Top
let (basic_norm_steps : FStar_TypeChecker_Normalize.step Prims.list) =
  [FStar_TypeChecker_Normalize.Beta;
  FStar_TypeChecker_Normalize.Eager_unfolding;
  FStar_TypeChecker_Normalize.Iota;
  FStar_TypeChecker_Normalize.Zeta;
  FStar_TypeChecker_Normalize.Inlining;
  FStar_TypeChecker_Normalize.EraseUniverses;
  FStar_TypeChecker_Normalize.AllowUnboundUniverses]
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t0 ->
      let arg_as_mlty g1 uu____2248 =
        match uu____2248 with
        | (a, uu____2254) ->
            let uu____2255 = is_type g1 a in
            if uu____2255
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent in
      let fv_app_as_mlty g1 fv args =
        let uu____2273 =
          let uu____2274 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv in
          Prims.op_Negation uu____2274 in
        if uu____2273
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____2276 =
             let uu____2289 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             match uu____2289 with
             | ((uu____2310, fvty), uu____2312) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.UnfoldUntil
                        FStar_Syntax_Syntax.Delta_constant]
                     g1.FStar_Extraction_ML_UEnv.tcenv fvty in
                 FStar_Syntax_Util.arrow_formals fvty1 in
           match uu____2276 with
           | (formals, uu____2319) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args in
               let mlargs1 =
                 let n_args = FStar_List.length args in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____2363 = FStar_Util.first_N n_args formals in
                   match uu____2363 with
                   | (uu____2390, rest) ->
                       let uu____2416 =
                         FStar_List.map
                           (fun uu____2424 ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest in
                       FStar_List.append mlargs uu____2416
                 else mlargs in
               let nm =
                 let uu____2431 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv in
                 match uu____2431 with
                 | FStar_Pervasives_Native.Some p -> p
                 | FStar_Pervasives_Native.None ->
                     FStar_Extraction_ML_Syntax.mlpath_of_lident
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)) in
      let aux env t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_type uu____2449 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____2450 ->
            let uu____2451 =
              let uu____2452 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2452 in
            failwith uu____2451
        | FStar_Syntax_Syntax.Tm_delayed uu____2453 ->
            let uu____2478 =
              let uu____2479 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2479 in
            failwith uu____2478
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu____2480 =
              let uu____2481 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2481 in
            failwith uu____2480
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____2483 = FStar_Syntax_Util.unfold_lazy i in
            translate_term_to_mlty env uu____2483
        | FStar_Syntax_Syntax.Tm_constant uu____2484 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____2485 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____2492 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2, uu____2510) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____2515;
               FStar_Syntax_Syntax.index = uu____2516;
               FStar_Syntax_Syntax.sort = t2;_},
             uu____2518)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2, uu____2526) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2532, uu____2533) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let uu____2600 = FStar_Syntax_Subst.open_comp bs c in
            (match uu____2600 with
             | (bs1, c1) ->
                 let uu____2607 = binders_as_ml_binders env bs1 in
                 (match uu____2607 with
                  | (mlbs, env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.tcenv
                            (FStar_Syntax_Util.comp_effect_name c1) in
                        let uu____2634 =
                          let uu____2641 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.tcenv eff in
                          FStar_Util.must uu____2641 in
                        match uu____2634 with
                        | (ed, qualifiers) ->
                            let uu____2662 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable) in
                            if uu____2662
                            then
                              let t2 =
                                FStar_TypeChecker_Env.reify_comp
                                  env1.FStar_Extraction_ML_UEnv.tcenv c1
                                  FStar_Syntax_Syntax.U_unknown in
                              let res = translate_term_to_mlty env1 t2 in res
                            else
                              translate_term_to_mlty env1
                                (FStar_Syntax_Util.comp_result c1) in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____2669 =
                        FStar_List.fold_right
                          (fun uu____2688 ->
                             fun uu____2689 ->
                               match (uu____2688, uu____2689) with
                               | ((uu____2710, t2), (tag, t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret) in
                      (match uu____2669 with | (uu____2722, t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1, args) ->
            let res =
              let uu____2747 =
                let uu____2748 = FStar_Syntax_Util.un_uinst head1 in
                uu____2748.FStar_Syntax_Syntax.n in
              match uu____2747 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2, args') ->
                  let uu____2775 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
                  translate_term_to_mlty env uu____2775
              | uu____2792 -> FStar_Extraction_ML_UEnv.unknownType in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____2795) ->
            let uu____2816 = FStar_Syntax_Subst.open_term bs ty in
            (match uu____2816 with
             | (bs1, ty1) ->
                 let uu____2823 = binders_as_ml_binders env bs1 in
                 (match uu____2823 with
                  | (bts, env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____2848 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____2861 ->
            FStar_Extraction_ML_UEnv.unknownType in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____2890 ->
            let uu____2897 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____2897 with
             | FStar_Pervasives_Native.None -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____2901 -> false in
      let uu____2902 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.tcenv t0 in
      if uu____2902
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0 in
         let uu____2905 = is_top_ty mlt in
         if uu____2905
         then
           let t =
             FStar_TypeChecker_Normalize.normalize
               ((FStar_TypeChecker_Normalize.UnfoldUntil
                   FStar_Syntax_Syntax.Delta_constant) :: basic_norm_steps)
               g.FStar_Extraction_ML_UEnv.tcenv t0 in
           aux g t
         else mlt)
and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident, FStar_Extraction_ML_Syntax.mlty)
         FStar_Pervasives_Native.tuple2 Prims.list,
        FStar_Extraction_ML_UEnv.env) FStar_Pervasives_Native.tuple2)
  =
  fun g ->
    fun bs ->
      let uu____2920 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2963 ->
                fun b ->
                  match uu____2963 with
                  | (ml_bs, env) ->
                      let uu____3003 = is_type_binder g b in
                      if uu____3003
                      then
                        let b1 = FStar_Pervasives_Native.fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____3021 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____3021, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort in
                         let uu____3035 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____3035 with
                         | (env1, b2) ->
                             let ml_b =
                               let uu____3059 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____3059, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____2920 with | (ml_bs, env) -> ((FStar_List.rev ml_bs), env)
let (term_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t0 ->
      let t =
        FStar_TypeChecker_Normalize.normalize basic_norm_steps
          g.FStar_Extraction_ML_UEnv.tcenv t0 in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1, uu____3142) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____3145, FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____3149 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                    | uu____3183 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____3184 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____3185 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____3188 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q ->
    fun p ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) ->
          let uu____3209 = FStar_Extraction_ML_Util.is_xtuple d in
          (match uu____3209 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____3213 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty, fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____3240 -> p))
      | uu____3243 -> p
let rec (extract_one_pat :
  Prims.bool ->
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.pat ->
        FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option ->
          (FStar_Extraction_ML_UEnv.env ->
             FStar_Syntax_Syntax.term ->
               (FStar_Extraction_ML_Syntax.mlexpr,
                 FStar_Extraction_ML_Syntax.e_tag,
                 FStar_Extraction_ML_Syntax.mlty)
                 FStar_Pervasives_Native.tuple3)
            ->
            (FStar_Extraction_ML_UEnv.env,
              (FStar_Extraction_ML_Syntax.mlpattern,
                FStar_Extraction_ML_Syntax.mlexpr Prims.list)
                FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
              Prims.bool) FStar_Pervasives_Native.tuple3)
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
                       (fun uu____3335 ->
                          let uu____3336 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t' in
                          let uu____3337 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____3336 uu____3337)
                   else ();
                   ok) in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c, swopt)) when
                let uu____3367 = FStar_Options.codegen () in
                uu____3367 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____3372 =
                  match swopt with
                  | FStar_Pervasives_Native.None ->
                      let uu____3385 =
                        let uu____3386 =
                          let uu____3387 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None)) in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____3387 in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____3386 in
                      (uu____3385, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange in
                      let uu____3408 = term_as_mlexpr g source_term in
                      (match uu____3408 with
                       | (mlterm, uu____3420, mlty) -> (mlterm, mlty)) in
                (match uu____3372 with
                 | (mlc, ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym () in
                     let when_clause =
                       let uu____3440 =
                         let uu____3441 =
                           let uu____3448 =
                             let uu____3451 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x) in
                             [uu____3451; mlc] in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____3448) in
                         FStar_Extraction_ML_Syntax.MLE_App uu____3441 in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3440 in
                     let uu____3454 = ok ml_ty in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____3454))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s in
                let mlty = term_as_mlty g t in
                let uu____3474 =
                  let uu____3483 =
                    let uu____3490 =
                      let uu____3491 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____3491 in
                    (uu____3490, []) in
                  FStar_Pervasives_Native.Some uu____3483 in
                let uu____3500 = ok mlty in (g, uu____3474, uu____3500)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____3511 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                (match uu____3511 with
                 | (g1, x1) ->
                     let uu____3534 = ok mlty in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3534))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____3568 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                (match uu____3568 with
                 | (g1, x1) ->
                     let uu____3591 = ok mlty in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3591))
            | FStar_Syntax_Syntax.Pat_dot_term uu____3623 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f, pats) ->
                let uu____3662 =
                  let uu____3667 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                  match uu____3667 with
                  | FStar_Util.Inr
                      (uu____3672,
                       {
                         FStar_Extraction_ML_Syntax.expr =
                           FStar_Extraction_ML_Syntax.MLE_Name n1;
                         FStar_Extraction_ML_Syntax.mlty = uu____3674;
                         FStar_Extraction_ML_Syntax.loc = uu____3675;_},
                       ttys, uu____3677)
                      -> (n1, ttys)
                  | uu____3690 -> failwith "Expected a constructor" in
                (match uu____3662 with
                 | (d, tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys) in
                     let uu____3712 = FStar_Util.first_N nTyVars pats in
                     (match uu____3712 with
                      | (tysVarPats, restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____3845 ->
                                        match uu____3845 with
                                        | (p1, uu____3853) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____3858, t) ->
                                                 term_as_mlty g t
                                             | uu____3864 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____3868 ->
                                                       let uu____3869 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1 in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____3869);
                                                  FStar_Exn.raise
                                                    Un_extractable)))) in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args in
                              let uu____3871 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty in
                              FStar_Pervasives_Native.Some uu____3871
                            with
                            | Un_extractable -> FStar_Pervasives_Native.None in
                          let uu____3900 =
                            FStar_Util.fold_map
                              (fun g1 ->
                                 fun uu____3936 ->
                                   match uu____3936 with
                                   | (p1, imp1) ->
                                       let uu____3955 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr in
                                       (match uu____3955 with
                                        | (g2, p2, uu____3984) -> (g2, p2)))
                              g tysVarPats in
                          (match uu____3900 with
                           | (g1, tyMLPats) ->
                               let uu____4045 =
                                 FStar_Util.fold_map
                                   (fun uu____4109 ->
                                      fun uu____4110 ->
                                        match (uu____4109, uu____4110) with
                                        | ((g2, f_ty_opt1), (p1, imp1)) ->
                                            let uu____4203 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest, res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____4263 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None) in
                                            (match uu____4203 with
                                             | (f_ty_opt2, expected_ty) ->
                                                 let uu____4334 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr in
                                                 (match uu____4334 with
                                                  | (g3, p2, uu____4375) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats in
                               (match uu____4045 with
                                | ((g2, f_ty_opt1), restMLPats) ->
                                    let uu____4493 =
                                      let uu____4504 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___63_4555 ->
                                                match uu___63_4555 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____4597 -> [])) in
                                      FStar_All.pipe_right uu____4504
                                        FStar_List.split in
                                    (match uu____4493 with
                                     | (mlPats, when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([], t) -> ok t
                                           | uu____4670 -> false in
                                         let uu____4679 =
                                           let uu____4688 =
                                             let uu____4695 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats)) in
                                             let uu____4698 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten in
                                             (uu____4695, uu____4698) in
                                           FStar_Pervasives_Native.Some
                                             uu____4688 in
                                         (g2, uu____4679, pat_ty_compat))))))
let (extract_pat :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_UEnv.env ->
           FStar_Syntax_Syntax.term ->
             (FStar_Extraction_ML_Syntax.mlexpr,
               FStar_Extraction_ML_Syntax.e_tag,
               FStar_Extraction_ML_Syntax.mlty)
               FStar_Pervasives_Native.tuple3)
          ->
          (FStar_Extraction_ML_UEnv.env,
            (FStar_Extraction_ML_Syntax.mlpattern,
              FStar_Extraction_ML_Syntax.mlexpr
                FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2 Prims.list,
            Prims.bool) FStar_Pervasives_Native.tuple3)
  =
  fun g ->
    fun p ->
      fun expected_t ->
        fun term_as_mlexpr ->
          let extract_one_pat1 g1 p1 expected_t1 =
            let uu____4825 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr in
            match uu____4825 with
            | (g2, FStar_Pervasives_Native.Some (x, v1), b) ->
                (g2, (x, v1), b)
            | uu____4882 ->
                failwith "Impossible: Unable to translate pattern" in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____4927 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1 in
                FStar_Pervasives_Native.Some uu____4927 in
          let uu____4928 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t) in
          match uu____4928 with
          | (g1, (p1, whens), b) ->
              let when_clause = mk_when_clause whens in
              (g1, [(p1, when_clause)], b)
let (maybe_eta_data_and_project_record :
  FStar_Extraction_ML_UEnv.env ->
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____5078, t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____5081 =
                  let uu____5092 =
                    let uu____5101 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____5101) in
                  uu____5092 :: more_args in
                eta_args uu____5081 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____5114, uu____5115)
                -> ((FStar_List.rev more_args), t)
            | uu____5138 ->
                let uu____5139 =
                  let uu____5140 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr in
                  let uu____5141 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____5140 uu____5141 in
                failwith uu____5139 in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____5173, args),
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
               (tyname, fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____5205 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____5227 = eta_args [] residualType in
            match uu____5227 with
            | (eargs, tres) ->
                (match eargs with
                 | [] ->
                     let uu____5280 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____5280
                 | uu____5281 ->
                     let uu____5292 = FStar_List.unzip eargs in
                     (match uu____5292 with
                      | (binders, eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor
                               (head1, args) ->
                               let body =
                                 let uu____5334 =
                                   let uu____5335 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____5335 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____5334 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____5344 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____5347, FStar_Pervasives_Native.None) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5351;
                FStar_Extraction_ML_Syntax.loc = uu____5352;_},
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
                | uu____5379 ->
                    let uu____5382 =
                      let uu____5389 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____5389, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5382 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5393;
                     FStar_Extraction_ML_Syntax.loc = uu____5394;_},
                   uu____5395);
                FStar_Extraction_ML_Syntax.mlty = uu____5396;
                FStar_Extraction_ML_Syntax.loc = uu____5397;_},
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
                | uu____5428 ->
                    let uu____5431 =
                      let uu____5438 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____5438, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5431 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5442;
                FStar_Extraction_ML_Syntax.loc = uu____5443;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____5451 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5451
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5455;
                FStar_Extraction_ML_Syntax.loc = uu____5456;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____5458)) ->
              let uu____5471 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5471
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5475;
                     FStar_Extraction_ML_Syntax.loc = uu____5476;_},
                   uu____5477);
                FStar_Extraction_ML_Syntax.mlty = uu____5478;
                FStar_Extraction_ML_Syntax.loc = uu____5479;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____5491 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5491
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5495;
                     FStar_Extraction_ML_Syntax.loc = uu____5496;_},
                   uu____5497);
                FStar_Extraction_ML_Syntax.mlty = uu____5498;
                FStar_Extraction_ML_Syntax.loc = uu____5499;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____5501)) ->
              let uu____5518 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5518
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____5524 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5524
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____5528)) ->
              let uu____5537 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5537
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5541;
                FStar_Extraction_ML_Syntax.loc = uu____5542;_},
              uu____5543),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____5550 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5550
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5554;
                FStar_Extraction_ML_Syntax.loc = uu____5555;_},
              uu____5556),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____5557)) ->
              let uu____5570 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5570
          | uu____5573 -> mlAppExpr
let (maybe_promote_effect :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_Syntax.mlexpr, FStar_Extraction_ML_Syntax.e_tag)
          FStar_Pervasives_Native.tuple2)
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
        | uu____5603 -> (ml_e, tag)
let rec (check_term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,
            FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple2)
  =
  fun g ->
    fun e ->
      fun f ->
        fun ty ->
          FStar_Extraction_ML_UEnv.debug g
            (fun uu____5668 ->
               let uu____5669 = FStar_Syntax_Print.term_to_string e in
               let uu____5670 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty in
               FStar_Util.print2 "Checking %s at type %s\n" uu____5669
                 uu____5670);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST, uu____5675) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE,
              FStar_Extraction_ML_Syntax.MLTY_Erased) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____5676 ->
               let uu____5681 = term_as_mlexpr g e in
               (match uu____5681 with
                | (ml_e, tag, t) ->
                    let uu____5695 = maybe_promote_effect ml_e tag t in
                    (match uu____5695 with
                     | (ml_e1, tag1) ->
                         let uu____5706 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f in
                         if uu____5706
                         then
                           let uu____5711 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty in
                           (uu____5711, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST,
                               FStar_Extraction_ML_Syntax.E_PURE,
                               FStar_Extraction_ML_Syntax.MLTY_Erased) ->
                                let uu____5717 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty in
                                (uu____5717, ty)
                            | uu____5718 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____5726 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty in
                                  (uu____5726, ty)))))))
and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr, FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g ->
    fun e ->
      let uu____5729 = term_as_mlexpr' g e in
      match uu____5729 with
      | (e1, f, t) ->
          let uu____5745 = maybe_promote_effect e1 f t in
          (match uu____5745 with | (e2, f1) -> (e2, f1, t))
and (term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr, FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g ->
    fun top ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u ->
           let uu____5770 =
             let uu____5771 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____5772 = FStar_Syntax_Print.tag_of_term top in
             let uu____5773 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5771 uu____5772 uu____5773 in
           FStar_Util.print_string uu____5770);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu____5781 =
             let uu____5782 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5782 in
           failwith uu____5781
       | FStar_Syntax_Syntax.Tm_delayed uu____5789 ->
           let uu____5814 =
             let uu____5815 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5815 in
           failwith uu____5814
       | FStar_Syntax_Syntax.Tm_uvar uu____5822 ->
           let uu____5839 =
             let uu____5840 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5840 in
           failwith uu____5839
       | FStar_Syntax_Syntax.Tm_bvar uu____5847 ->
           let uu____5848 =
             let uu____5849 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5849 in
           failwith uu____5848
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____5857 = FStar_Syntax_Util.unfold_lazy i in
           term_as_mlexpr g uu____5857
       | FStar_Syntax_Syntax.Tm_type uu____5858 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5859 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5866 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
              FStar_Syntax_Syntax.antiquotes = uu____5880;_})
           ->
           let uu____5895 =
             let uu____5904 =
               let uu____5921 =
                 FStar_Syntax_Syntax.lid_as_fv
                   FStar_Parser_Const.failwith_lid
                   FStar_Syntax_Syntax.Delta_constant
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.lookup_fv g uu____5921 in
             FStar_All.pipe_left FStar_Util.right uu____5904 in
           (match uu____5895 with
            | (uu____5964, fw, uu____5966, uu____5967) ->
                let uu____5968 =
                  let uu____5969 =
                    let uu____5970 =
                      let uu____5977 =
                        let uu____5980 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Open quotation at runtime")) in
                        [uu____5980] in
                      (fw, uu____5977) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5970 in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____5969 in
                (uu____5968, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
              FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____5999 = FStar_Reflection_Basic.inspect_ln qt in
           (match uu____5999 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____6007 = FStar_Syntax_Syntax.lookup_aq bv aqs in
                (match uu____6007 with
                 | FStar_Pervasives_Native.Some (false, tm) ->
                     term_as_mlexpr g tm
                 | FStar_Pervasives_Native.Some (true, tm) ->
                     let uu____6030 =
                       let uu____6039 =
                         let uu____6056 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.failwith_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         FStar_Extraction_ML_UEnv.lookup_fv g uu____6056 in
                       FStar_All.pipe_left FStar_Util.right uu____6039 in
                     (match uu____6030 with
                      | (uu____6099, fw, uu____6101, uu____6102) ->
                          let uu____6103 =
                            let uu____6104 =
                              let uu____6105 =
                                let uu____6112 =
                                  let uu____6115 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         FStar_Extraction_ML_Syntax.ml_string_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_String
                                            "Open quotation at runtime")) in
                                  [uu____6115] in
                                (fw, uu____6112) in
                              FStar_Extraction_ML_Syntax.MLE_App uu____6105 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____6104 in
                          (uu____6103, FStar_Extraction_ML_Syntax.E_PURE,
                            FStar_Extraction_ML_Syntax.ml_int_ty))
                 | FStar_Pervasives_Native.None ->
                     let tv =
                       let uu____6123 =
                         FStar_Reflection_Embeddings.e_term_view_aq aqs in
                       FStar_Syntax_Embeddings.embed uu____6123
                         t.FStar_Syntax_Syntax.pos
                         (FStar_Reflection_Data.Tv_Var bv) in
                     let t1 =
                       let uu____6129 =
                         let uu____6138 = FStar_Syntax_Syntax.as_arg tv in
                         [uu____6138] in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____6129 in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____6141 =
                    FStar_Reflection_Embeddings.e_term_view_aq aqs in
                  FStar_Syntax_Embeddings.embed uu____6141
                    t.FStar_Syntax_Syntax.pos tv in
                let t1 =
                  let uu____6147 =
                    let uu____6156 = FStar_Syntax_Syntax.as_arg tv1 in
                    [uu____6156] in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____6147 in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc))
           ->
           FStar_Errors.raise_err
             (FStar_Errors.Error_NoLetMutable,
               "let-mutable no longer supported")
       | FStar_Syntax_Syntax.Tm_meta
           (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____6170)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____6200 =
                  let uu____6207 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m in
                  FStar_Util.must uu____6207 in
                (match uu____6200 with
                 | (ed, qualifiers) ->
                     let uu____6234 =
                       let uu____6235 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                       FStar_All.pipe_right uu____6235 Prims.op_Negation in
                     if uu____6234
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____6251 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1, uu____6253) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1, uu____6259) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6265 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____6265 with
            | (uu____6278, ty, uu____6280) ->
                let ml_ty = term_as_mlty g ty in
                let uu____6282 =
                  let uu____6283 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____6283 in
                (uu____6282, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____6284 ->
           let uu____6285 = is_type g t in
           if uu____6285
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6293 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____6293 with
              | (FStar_Util.Inl uu____6306, uu____6307) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____6344, x, mltys, uu____6347), qual) ->
                  (match mltys with
                   | ([], t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([], t1) ->
                       let uu____6393 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____6393, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6394 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____6402 = is_type g t in
           if uu____6402
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6410 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv in
              match uu____6410 with
              | FStar_Pervasives_Native.None ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____6419) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | FStar_Pervasives_Native.Some (FStar_Util.Inr
                  (uu____6452, x, mltys, uu____6455)) ->
                  (match mltys with
                   | ([], t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([], t1) ->
                       let uu____6496 =
                         maybe_eta_data_and_project_record g
                           fv.FStar_Syntax_Syntax.fv_qual t1 x in
                       (uu____6496, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6497 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs, body, copt) ->
           let uu____6527 = FStar_Syntax_Subst.open_term bs body in
           (match uu____6527 with
            | (bs1, body1) ->
                let uu____6540 = binders_as_ml_binders g bs1 in
                (match uu____6540 with
                 | (ml_bs, env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____6573 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c in
                           if uu____6573
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____6578 ->
                                 let uu____6579 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____6579);
                            body1) in
                     let uu____6580 = term_as_mlexpr env body2 in
                     (match uu____6580 with
                      | (ml_body, f, t1) ->
                          let uu____6596 =
                            FStar_List.fold_right
                              (fun uu____6615 ->
                                 fun uu____6616 ->
                                   match (uu____6615, uu____6616) with
                                   | ((uu____6637, targ), (f1, t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____6596 with
                           | (f1, tfun) ->
                               let uu____6657 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____6657, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____6664;
              FStar_Syntax_Syntax.vars = uu____6665;_},
            (a1, uu____6667)::[])
           ->
           let ty =
             let uu____6697 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
             term_as_mlty g uu____6697 in
           let uu____6698 =
             let uu____6699 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____6699 in
           (uu____6698, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____6700;
              FStar_Syntax_Syntax.vars = uu____6701;_},
            (t1, uu____6703)::(r, uu____6705)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6744);
              FStar_Syntax_Syntax.pos = uu____6745;
              FStar_Syntax_Syntax.vars = uu____6746;_},
            uu____6747)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1, args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___64_6805 ->
                        match uu___64_6805 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | uu____6806 -> false))) in
           let uu____6807 =
             let uu____6812 =
               let uu____6813 = FStar_Syntax_Subst.compress head1 in
               uu____6813.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____6812) in
           (match uu____6807 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6822, uu____6823) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr g t1
            | (uu____6841, FStar_Syntax_Syntax.Tm_abs
               (bs, uu____6843, FStar_Pervasives_Native.Some rc)) when
                is_total rc ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr g t1
            | (uu____6864, FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify)) ->
                let e =
                  let uu____6866 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6866 in
                let tm =
                  let uu____6876 =
                    let uu____6881 = FStar_TypeChecker_Util.remove_reify e in
                    let uu____6882 = FStar_List.tl args in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6881 uu____6882 in
                  uu____6876 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr g tm
            | uu____6891 ->
                let rec extract_app is_data uu____6944 uu____6945 restArgs =
                  match (uu____6944, uu____6945) with
                  | ((mlhead, mlargs_f), (f, t1)) ->
                      (match (restArgs, t1) with
                       | ([], uu____7035) ->
                           let mlargs =
                             FStar_All.pipe_right (FStar_List.rev mlargs_f)
                               (FStar_List.map FStar_Pervasives_Native.fst) in
                           let app =
                             let uu____7070 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t1)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (mlhead, mlargs)) in
                             FStar_All.pipe_left
                               (maybe_eta_data_and_project_record g is_data
                                  t1) uu____7070 in
                           (app, f, t1)
                       | ((arg, uu____7074)::rest,
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t, f', t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____7105 =
                             let uu____7110 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f' in
                             (uu____7110, t2) in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____7105 rest
                       | ((e0, uu____7122)::rest,
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected, f', t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let expected_effect =
                             let uu____7155 =
                               (FStar_Options.lax ()) &&
                                 (FStar_TypeChecker_Util.short_circuit_head
                                    head1) in
                             if uu____7155
                             then FStar_Extraction_ML_Syntax.E_IMPURE
                             else FStar_Extraction_ML_Syntax.E_PURE in
                           let uu____7157 =
                             check_term_as_mlexpr g e0 expected_effect
                               tExpected in
                           (match uu____7157 with
                            | (e01, tInferred) ->
                                let uu____7170 =
                                  let uu____7175 =
                                    FStar_Extraction_ML_Util.join_l r [f; f'] in
                                  (uu____7175, t2) in
                                extract_app is_data
                                  (mlhead, ((e01, expected_effect) ::
                                    mlargs_f)) uu____7170 rest)
                       | uu____7186 ->
                           let uu____7199 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1 in
                           (match uu____7199 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None ->
                                (match t1 with
                                 | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                                     (FStar_Extraction_ML_Syntax.ml_unit,
                                       FStar_Extraction_ML_Syntax.E_PURE, t1)
                                 | uu____7221 ->
                                     err_ill_typed_application g top restArgs
                                       t1))) in
                let extract_app_maybe_projector is_data mlhead uu____7271
                  args1 =
                  match uu____7271 with
                  | (f, t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____7303)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____7387))::args3,
                                FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____7389, f', t3)) ->
                                 let uu____7426 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____7426 t3
                             | uu____7427 -> (args2, f1, t2) in
                           let uu____7452 = remove_implicits args1 f t1 in
                           (match uu____7452 with
                            | (args2, f1, t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____7508 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let extract_app_with_instantiations uu____7532 =
                  let head2 = FStar_Syntax_Util.un_uinst head1 in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____7540 ->
                      let uu____7541 =
                        let uu____7554 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2 in
                        match uu____7554 with
                        | (FStar_Util.Inr (uu____7573, x1, x2, x3), q) ->
                            ((x1, x2, x3), q)
                        | uu____7618 -> failwith "FIXME Ty" in
                      (match uu____7541 with
                       | ((head_ml, (vars, t1), inst_ok), qual) ->
                           let has_typ_apps =
                             match args with
                             | (a, uu____7668)::uu____7669 -> is_type g a
                             | uu____7688 -> false in
                           let uu____7697 =
                             match vars with
                             | uu____7726::uu____7727 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____7738 ->
                                 let n1 = FStar_List.length vars in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____7766 =
                                     FStar_Util.first_N n1 args in
                                   (match uu____7766 with
                                    | (prefix1, rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____7855 ->
                                               match uu____7855 with
                                               | (x, uu____7861) ->
                                                   term_as_mlty g x) prefix1 in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____7878 ->
                                              let uu___68_7881 = e in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___68_7881.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___68_7881.FStar_Extraction_ML_Syntax.loc)
                                              } in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____7885 ->
                                              let uu___69_7886 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___69_7886.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___69_7886.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____7887 ->
                                              let uu___69_7888 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___69_7888.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___69_7888.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   FStar_Extraction_ML_Syntax.MLE_Const
                                                   (FStar_Extraction_ML_Syntax.MLC_Unit);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = uu____7890;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   = uu____7891;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___70_7897 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___70_7897.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___70_7897.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____7898 ->
                                              failwith
                                                "Impossible: Unexpected head term" in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top in
                           (match uu____7697 with
                            | (head_ml1, head_t, args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____7959 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1 in
                                     (uu____7959,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____7960 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____7969 ->
                      let uu____7970 =
                        let uu____7983 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2 in
                        match uu____7983 with
                        | (FStar_Util.Inr (uu____8002, x1, x2, x3), q) ->
                            ((x1, x2, x3), q)
                        | uu____8047 -> failwith "FIXME Ty" in
                      (match uu____7970 with
                       | ((head_ml, (vars, t1), inst_ok), qual) ->
                           let has_typ_apps =
                             match args with
                             | (a, uu____8097)::uu____8098 -> is_type g a
                             | uu____8117 -> false in
                           let uu____8126 =
                             match vars with
                             | uu____8155::uu____8156 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____8167 ->
                                 let n1 = FStar_List.length vars in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____8195 =
                                     FStar_Util.first_N n1 args in
                                   (match uu____8195 with
                                    | (prefix1, rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____8284 ->
                                               match uu____8284 with
                                               | (x, uu____8290) ->
                                                   term_as_mlty g x) prefix1 in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____8307 ->
                                              let uu___68_8310 = e in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___68_8310.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___68_8310.FStar_Extraction_ML_Syntax.loc)
                                              } in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____8314 ->
                                              let uu___69_8315 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___69_8315.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___69_8315.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____8316 ->
                                              let uu___69_8317 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___69_8317.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___69_8317.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   FStar_Extraction_ML_Syntax.MLE_Const
                                                   (FStar_Extraction_ML_Syntax.MLC_Unit);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = uu____8319;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   = uu____8320;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___70_8326 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___70_8326.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___70_8326.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____8327 ->
                                              failwith
                                                "Impossible: Unexpected head term" in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top in
                           (match uu____8126 with
                            | (head_ml1, head_t, args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____8388 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1 in
                                     (uu____8388,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____8389 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____8398 ->
                      let uu____8399 = term_as_mlexpr g head2 in
                      (match uu____8399 with
                       | (head3, f, t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args) in
                let uu____8415 = is_type g t in
                if uu____8415
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____8423 =
                     let uu____8424 = FStar_Syntax_Util.un_uinst head1 in
                     uu____8424.FStar_Syntax_Syntax.n in
                   match uu____8423 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____8434 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv in
                       (match uu____8434 with
                        | FStar_Pervasives_Native.None ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____8443 -> extract_app_with_instantiations ())
                   | uu____8446 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____8449), f) ->
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
           let uu____8516 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____8516 with | (e, t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____8547 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8561 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____8561
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____8575 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____8575 in
                   let lb1 =
                     let uu___71_8577 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___71_8577.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___71_8577.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___71_8577.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___71_8577.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___71_8577.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___71_8577.FStar_Syntax_Syntax.lbpos)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____8547 with
            | (lbs1, e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb ->
                            let tcenv =
                              let uu____8608 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8608 in
                            let lbdef =
                              let uu____8616 = FStar_Options.ml_ish () in
                              if uu____8616
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.EraseUniverses;
                                  FStar_TypeChecker_Normalize.Inlining;
                                  FStar_TypeChecker_Normalize.Eager_unfolding;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.PureSubtermsWithinComputations;
                                  FStar_TypeChecker_Normalize.Primops] tcenv
                                  lb.FStar_Syntax_Syntax.lbdef in
                            let uu___72_8620 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___72_8620.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___72_8620.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___72_8620.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___72_8620.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___72_8620.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___72_8620.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1 in
                let maybe_generalize uu____8645 =
                  match uu____8645 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8665;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;
                      FStar_Syntax_Syntax.lbattrs = uu____8669;
                      FStar_Syntax_Syntax.lbpos = uu____8670;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t2 = FStar_Syntax_Subst.compress t1 in
                      let no_gen uu____8746 =
                        let expected_t = term_as_mlty g t2 in
                        (lbname_, f_e, (t2, ([], ([], expected_t))), false,
                          e) in
                      let uu____8808 =
                        FStar_TypeChecker_Util.must_erase_for_extraction
                          g.FStar_Extraction_ML_UEnv.tcenv t2 in
                      if uu____8808
                      then
                        (lbname_, f_e,
                          (t2,
                            ([],
                              ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                          false, e)
                      else
                        (match t2.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                             let uu____8924 = FStar_List.hd bs in
                             FStar_All.pipe_right uu____8924
                               (is_type_binder g)
                             ->
                             let uu____8937 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____8937 with
                              | (bs1, c1) ->
                                  let uu____8962 =
                                    let uu____8969 =
                                      FStar_Util.prefix_until
                                        (fun x ->
                                           let uu____9005 =
                                             is_type_binder g x in
                                           Prims.op_Negation uu____9005) bs1 in
                                    match uu____8969 with
                                    | FStar_Pervasives_Native.None ->
                                        (bs1,
                                          (FStar_Syntax_Util.comp_result c1))
                                    | FStar_Pervasives_Native.Some
                                        (bs2, b, rest) ->
                                        let uu____9093 =
                                          FStar_Syntax_Util.arrow (b :: rest)
                                            c1 in
                                        (bs2, uu____9093) in
                                  (match uu____8962 with
                                   | (tbinders, tbody) ->
                                       let n_tbinders =
                                         FStar_List.length tbinders in
                                       let e1 =
                                         let uu____9138 = normalize_abs e in
                                         FStar_All.pipe_right uu____9138
                                           FStar_Syntax_Util.unmeta in
                                       (match e1.FStar_Syntax_Syntax.n with
                                        | FStar_Syntax_Syntax.Tm_abs
                                            (bs2, body, copt) ->
                                            let uu____9180 =
                                              FStar_Syntax_Subst.open_term
                                                bs2 body in
                                            (match uu____9180 with
                                             | (bs3, body1) ->
                                                 if
                                                   n_tbinders <=
                                                     (FStar_List.length bs3)
                                                 then
                                                   let uu____9233 =
                                                     FStar_Util.first_N
                                                       n_tbinders bs3 in
                                                   (match uu____9233 with
                                                    | (targs, rest_args) ->
                                                        let expected_source_ty
                                                          =
                                                          let s =
                                                            FStar_List.map2
                                                              (fun uu____9321
                                                                 ->
                                                                 fun
                                                                   uu____9322
                                                                   ->
                                                                   match 
                                                                    (uu____9321,
                                                                    uu____9322)
                                                                   with
                                                                   | 
                                                                   ((x,
                                                                    uu____9340),
                                                                    (y,
                                                                    uu____9342))
                                                                    ->
                                                                    let uu____9351
                                                                    =
                                                                    let uu____9358
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____9358) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9351)
                                                              tbinders targs in
                                                          FStar_Syntax_Subst.subst
                                                            s tbody in
                                                        let env =
                                                          FStar_List.fold_left
                                                            (fun env ->
                                                               fun uu____9369
                                                                 ->
                                                                 match uu____9369
                                                                 with
                                                                 | (a,
                                                                    uu____9375)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    FStar_Pervasives_Native.None)
                                                            g targs in
                                                        let expected_t =
                                                          term_as_mlty env
                                                            expected_source_ty in
                                                        let polytype =
                                                          let uu____9384 =
                                                            FStar_All.pipe_right
                                                              targs
                                                              (FStar_List.map
                                                                 (fun
                                                                    uu____9402
                                                                    ->
                                                                    match uu____9402
                                                                    with
                                                                    | 
                                                                    (x,
                                                                    uu____9408)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                          (uu____9384,
                                                            expected_t) in
                                                        let add_unit =
                                                          match rest_args
                                                          with
                                                          | [] ->
                                                              (let uu____9418
                                                                 =
                                                                 is_fstar_value
                                                                   body1 in
                                                               Prims.op_Negation
                                                                 uu____9418)
                                                                ||
                                                                (let uu____9420
                                                                   =
                                                                   FStar_Syntax_Util.is_pure_comp
                                                                    c1 in
                                                                 Prims.op_Negation
                                                                   uu____9420)
                                                          | uu____9421 ->
                                                              false in
                                                        let rest_args1 =
                                                          if add_unit
                                                          then unit_binder ::
                                                            rest_args
                                                          else rest_args in
                                                        let polytype1 =
                                                          if add_unit
                                                          then
                                                            FStar_Extraction_ML_Syntax.push_unit
                                                              polytype
                                                          else polytype in
                                                        let body2 =
                                                          FStar_Syntax_Util.abs
                                                            rest_args1 body1
                                                            copt in
                                                        (lbname_, f_e,
                                                          (t2,
                                                            (targs,
                                                              polytype1)),
                                                          add_unit, body2))
                                                 else
                                                   failwith
                                                     "Not enough type binders")
                                        | FStar_Syntax_Syntax.Tm_uinst
                                            uu____9490 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env ->
                                                   fun uu____9507 ->
                                                     match uu____9507 with
                                                     | (a, uu____9513) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders in
                                            let expected_t =
                                              term_as_mlty env tbody in
                                            let polytype =
                                              let uu____9522 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9534 ->
                                                        match uu____9534 with
                                                        | (x, uu____9540) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x)) in
                                              (uu____9522, expected_t) in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9556 ->
                                                      match uu____9556 with
                                                      | (bv, uu____9562) ->
                                                          let uu____9563 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv in
                                                          FStar_All.pipe_right
                                                            uu____9563
                                                            FStar_Syntax_Syntax.as_arg)) in
                                            let e2 =
                                              FStar_Syntax_Syntax.mk
                                                (FStar_Syntax_Syntax.Tm_app
                                                   (e1, args))
                                                FStar_Pervasives_Native.None
                                                e1.FStar_Syntax_Syntax.pos in
                                            (lbname_, f_e,
                                              (t2, (tbinders, polytype)),
                                              false, e2)
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            uu____9605 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env ->
                                                   fun uu____9616 ->
                                                     match uu____9616 with
                                                     | (a, uu____9622) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders in
                                            let expected_t =
                                              term_as_mlty env tbody in
                                            let polytype =
                                              let uu____9631 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9643 ->
                                                        match uu____9643 with
                                                        | (x, uu____9649) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x)) in
                                              (uu____9631, expected_t) in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9665 ->
                                                      match uu____9665 with
                                                      | (bv, uu____9671) ->
                                                          let uu____9672 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv in
                                                          FStar_All.pipe_right
                                                            uu____9672
                                                            FStar_Syntax_Syntax.as_arg)) in
                                            let e2 =
                                              FStar_Syntax_Syntax.mk
                                                (FStar_Syntax_Syntax.Tm_app
                                                   (e1, args))
                                                FStar_Pervasives_Native.None
                                                e1.FStar_Syntax_Syntax.pos in
                                            (lbname_, f_e,
                                              (t2, (tbinders, polytype)),
                                              false, e2)
                                        | FStar_Syntax_Syntax.Tm_name
                                            uu____9714 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env ->
                                                   fun uu____9725 ->
                                                     match uu____9725 with
                                                     | (a, uu____9731) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders in
                                            let expected_t =
                                              term_as_mlty env tbody in
                                            let polytype =
                                              let uu____9740 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9752 ->
                                                        match uu____9752 with
                                                        | (x, uu____9758) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x)) in
                                              (uu____9740, expected_t) in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9774 ->
                                                      match uu____9774 with
                                                      | (bv, uu____9780) ->
                                                          let uu____9781 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv in
                                                          FStar_All.pipe_right
                                                            uu____9781
                                                            FStar_Syntax_Syntax.as_arg)) in
                                            let e2 =
                                              FStar_Syntax_Syntax.mk
                                                (FStar_Syntax_Syntax.Tm_app
                                                   (e1, args))
                                                FStar_Pervasives_Native.None
                                                e1.FStar_Syntax_Syntax.pos in
                                            (lbname_, f_e,
                                              (t2, (tbinders, polytype)),
                                              false, e2)
                                        | uu____9823 ->
                                            err_value_restriction e1)))
                         | uu____9842 -> no_gen ()) in
                let check_lb env uu____9889 =
                  match uu____9889 with
                  | (nm, (lbname, f, (t1, (targs, polytype)), add_unit, e))
                      ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1 ->
                             fun uu____10024 ->
                               match uu____10024 with
                               | (a, uu____10030) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs in
                      let expected_t = FStar_Pervasives_Native.snd polytype in
                      let uu____10032 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____10032 with
                       | (e1, ty) ->
                           let uu____10043 =
                             maybe_promote_effect e1 f expected_t in
                           (match uu____10043 with
                            | (e2, f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE,
                                     FStar_Extraction_ML_Syntax.MLTY_Erased)
                                      -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST,
                                     FStar_Extraction_ML_Syntax.MLTY_Erased)
                                      -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____10059 -> [] in
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
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize) in
                let uu____10129 =
                  FStar_List.fold_right
                    (fun lb ->
                       fun uu____10220 ->
                         match uu____10220 with
                         | (env, lbs4) ->
                             let uu____10345 = lb in
                             (match uu____10345 with
                              | (lbname, uu____10393,
                                 (t1, (uu____10395, polytype)), add_unit,
                                 uu____10398) ->
                                  let uu____10411 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____10411 with
                                   | (env1, nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, []) in
                (match uu____10129 with
                 | (env_body, lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____10688 = term_as_mlexpr env_body e'1 in
                     (match uu____10688 with
                      | (e'2, f', t') ->
                          let f =
                            let uu____10705 =
                              let uu____10708 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5 in
                              f' :: uu____10708 in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10705 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____10717 =
                            let uu____10718 =
                              let uu____10719 =
                                let uu____10720 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5 in
                                (is_rec1, uu____10720) in
                              mk_MLE_Let top_level uu____10719 e'2 in
                            let uu____10729 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10718 uu____10729 in
                          (uu____10717, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee, pats) ->
           let uu____10768 = term_as_mlexpr g scrutinee in
           (match uu____10768 with
            | (e, f_e, t_e) ->
                let uu____10784 = check_pats_for_ite pats in
                (match uu____10784 with
                 | (b, then_e, else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some then_e1,
                           FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10845 = term_as_mlexpr g then_e1 in
                            (match uu____10845 with
                             | (then_mle, f_then, t_then) ->
                                 let uu____10861 = term_as_mlexpr g else_e1 in
                                 (match uu____10861 with
                                  | (else_mle, f_else, t_else) ->
                                      let uu____10877 =
                                        let uu____10888 =
                                          type_leq g t_then t_else in
                                        if uu____10888
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10906 =
                                             type_leq g t_else t_then in
                                           if uu____10906
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____10877 with
                                       | (t_branch, maybe_lift1) ->
                                           let uu____10950 =
                                             let uu____10951 =
                                               let uu____10952 =
                                                 let uu____10961 =
                                                   maybe_lift1 then_mle
                                                     t_then in
                                                 let uu____10962 =
                                                   let uu____10965 =
                                                     maybe_lift1 else_mle
                                                       t_else in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10965 in
                                                 (e, uu____10961,
                                                   uu____10962) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10952 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10951 in
                                           let uu____10968 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____10950, uu____10968,
                                             t_branch))))
                        | uu____10969 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10985 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat ->
                                  fun br ->
                                    let uu____11094 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____11094 with
                                    | (pat, when_opt, branch1) ->
                                        let uu____11138 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr in
                                        (match uu____11138 with
                                         | (env, p, pat_t_compat) ->
                                             let uu____11196 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let w_pos =
                                                     w.FStar_Syntax_Syntax.pos in
                                                   let uu____11219 =
                                                     term_as_mlexpr env w in
                                                   (match uu____11219 with
                                                    | (w1, f_w, t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w)) in
                                             (match uu____11196 with
                                              | (when_opt1, f_when) ->
                                                  let uu____11268 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____11268 with
                                                   | (mlbranch, f_branch,
                                                      t_branch) ->
                                                       let uu____11302 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____11379
                                                                 ->
                                                                 match uu____11379
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
                                                         uu____11302)))))
                               true) in
                        match uu____10985 with
                        | (pat_t_compat, mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____11544 ->
                                      let uu____11545 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____11546 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____11545 uu____11546);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____11571 =
                                   let uu____11580 =
                                     let uu____11597 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____11597 in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____11580 in
                                 (match uu____11571 with
                                  | (uu____11640, fw, uu____11642,
                                     uu____11643) ->
                                      let uu____11644 =
                                        let uu____11645 =
                                          let uu____11646 =
                                            let uu____11653 =
                                              let uu____11656 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____11656] in
                                            (fw, uu____11653) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11646 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____11645 in
                                      (uu____11644,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____11659, uu____11660,
                                (uu____11661, f_first, t_first))::rest ->
                                 let uu____11721 =
                                   FStar_List.fold_left
                                     (fun uu____11763 ->
                                        fun uu____11764 ->
                                          match (uu____11763, uu____11764)
                                          with
                                          | ((topt, f),
                                             (uu____11821, uu____11822,
                                              (uu____11823, f_branch,
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
                                                    let uu____11879 =
                                                      type_leq g t1 t_branch in
                                                    if uu____11879
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11883 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____11883
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           t1
                                                       else
                                                         FStar_Pervasives_Native.None) in
                                              (topt1, f1))
                                     ((FStar_Pervasives_Native.Some t_first),
                                       f_first) rest in
                                 (match uu____11721 with
                                  | (topt, f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11978 ->
                                                match uu____11978 with
                                                | (p, (wopt, uu____12007),
                                                   (b1, uu____12009, t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____12028 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | FStar_Pervasives_Native.Some t1 ->
                                            t1 in
                                      let uu____12033 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____12033, f_match, t_match)))))))
let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env ->
    fun discName ->
      fun constrName ->
        let uu____12059 =
          let uu____12064 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12064 in
        match uu____12059 with
        | (uu____12089, fstar_disc_type) ->
            let wildcards =
              let uu____12098 =
                let uu____12099 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____12099.FStar_Syntax_Syntax.n in
              match uu____12098 with
              | FStar_Syntax_Syntax.Tm_arrow (binders, uu____12109) ->
                  let uu____12126 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___65_12158 ->
                            match uu___65_12158 with
                            | (uu____12165, FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____12166)) ->
                                true
                            | uu____12169 -> false)) in
                  FStar_All.pipe_right uu____12126
                    (FStar_List.map
                       (fun uu____12202 ->
                          let uu____12209 = fresh "_" in
                          (uu____12209, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____12210 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____12221 =
                let uu____12222 =
                  let uu____12233 =
                    let uu____12234 =
                      let uu____12235 =
                        let uu____12250 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid)) in
                        let uu____12253 =
                          let uu____12264 =
                            let uu____12273 =
                              let uu____12274 =
                                let uu____12281 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____12281,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____12274 in
                            let uu____12284 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____12273, FStar_Pervasives_Native.None,
                              uu____12284) in
                          let uu____12287 =
                            let uu____12298 =
                              let uu____12307 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____12307) in
                            [uu____12298] in
                          uu____12264 :: uu____12287 in
                        (uu____12250, uu____12253) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____12235 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____12234 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____12233) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____12222 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____12221 in
            let uu____12362 =
              let uu____12363 =
                let uu____12366 =
                  let uu____12367 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____12367;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____12366] in
              (FStar_Extraction_ML_Syntax.NonRec, uu____12363) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____12362