open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Un_extractable -> true | uu____5 -> false
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
  'uuuuuu67 .
    FStar_Range.range -> (FStar_Errors.raw_error * Prims.string) -> 'uuuuuu67
  = fun r -> fun err -> FStar_Errors.raise_error err r
let err_ill_typed_application :
  'uuuuuu100 'uuuuuu101 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'uuuuuu100) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'uuuuuu101
  =
  fun env ->
    fun t ->
      fun mlhead ->
        fun args ->
          fun ty ->
            let uu____139 =
              let uu____144 =
                let uu____145 = FStar_Syntax_Print.term_to_string t in
                let uu____146 =
                  let uu____147 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env in
                  FStar_Extraction_ML_Code.string_of_mlexpr uu____147 mlhead in
                let uu____148 =
                  let uu____149 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env in
                  FStar_Extraction_ML_Code.string_of_mlty uu____149 ty in
                let uu____150 =
                  let uu____151 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____169 ->
                            match uu____169 with
                            | (x, uu____175) ->
                                FStar_Syntax_Print.term_to_string x)) in
                  FStar_All.pipe_right uu____151 (FStar_String.concat " ") in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____145 uu____146 uu____148 uu____150 in
              (FStar_Errors.Fatal_IllTyped, uu____144) in
            fail t.FStar_Syntax_Syntax.pos uu____139
let err_ill_typed_erasure :
  'uuuuuu186 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'uuuuuu186
  =
  fun env ->
    fun pos ->
      fun ty ->
        let uu____202 =
          let uu____207 =
            let uu____208 =
              let uu____209 =
                FStar_Extraction_ML_UEnv.current_module_of_uenv env in
              FStar_Extraction_ML_Code.string_of_mlty uu____209 ty in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____208 in
          (FStar_Errors.Fatal_IllTyped, uu____207) in
        fail pos uu____202
let err_value_restriction :
  'uuuuuu214 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'uuuuuu214
  =
  fun t ->
    let uu____224 =
      let uu____229 =
        let uu____230 = FStar_Syntax_Print.tag_of_term t in
        let uu____231 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____230 uu____231 in
      (FStar_Errors.Fatal_ValueRestriction, uu____229) in
    fail t.FStar_Syntax_Syntax.pos uu____224
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
            let uu____261 =
              let uu____266 =
                let uu____267 = FStar_Syntax_Print.term_to_string t in
                let uu____268 =
                  let uu____269 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env in
                  FStar_Extraction_ML_Code.string_of_mlty uu____269 ty in
                let uu____270 = FStar_Extraction_ML_Util.eff_to_string f0 in
                let uu____271 = FStar_Extraction_ML_Util.eff_to_string f1 in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____267 uu____268 uu____270 uu____271 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____266) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____261
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.of_int (20)) in
  let rec delta_norm_eff g l =
    let uu____294 =
      let uu____297 = FStar_Ident.string_of_lid l in
      FStar_Util.smap_try_find cache uu____297 in
    match uu____294 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None ->
        let res =
          let uu____300 =
            let uu____307 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
            FStar_TypeChecker_Env.lookup_effect_abbrev uu____307
              [FStar_Syntax_Syntax.U_zero] l in
          match uu____300 with
          | FStar_Pervasives_Native.None -> l
          | FStar_Pervasives_Native.Some (uu____312, c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c) in
        ((let uu____319 = FStar_Ident.string_of_lid l in
          FStar_Util.smap_add cache uu____319 res);
         res) in
  fun g ->
    fun l ->
      let l1 = delta_norm_eff g l in
      let uu____323 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid in
      if uu____323
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____325 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid in
         if uu____325
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              let uu____336 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
              FStar_TypeChecker_Env.effect_decl_opt uu____336 l1 in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                let uu____349 =
                  let uu____350 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                  FStar_TypeChecker_Env.is_reifiable_effect uu____350
                    ed.FStar_Syntax_Syntax.mname in
                if uu____349
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____369 =
        let uu____370 = FStar_Syntax_Subst.compress t1 in
        uu____370.FStar_Syntax_Syntax.n in
      match uu____369 with
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____373 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____388 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____415 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____423 = FStar_Syntax_Util.unfold_lazy i in
          is_arity env uu____423
      | FStar_Syntax_Syntax.Tm_uvar uu____424 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____437 -> false
      | FStar_Syntax_Syntax.Tm_name uu____438 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____439 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____446 -> false
      | FStar_Syntax_Syntax.Tm_type uu____447 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____448, c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let topt =
            let uu____478 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] uu____478
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match topt with
           | FStar_Pervasives_Native.None -> false
           | FStar_Pervasives_Native.Some (uu____483, t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____489 ->
          let uu____506 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____506 with | (head, uu____524) -> is_arity env head)
      | FStar_Syntax_Syntax.Tm_uinst (head, uu____550) -> is_arity env head
      | FStar_Syntax_Syntax.Tm_refine (x, uu____556) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____561, body, uu____563) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____588, body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____606, branches) ->
          (match branches with
           | (uu____644, uu____645, e)::uu____647 -> is_arity env e
           | uu____694 -> false)
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____722 ->
          let uu____737 =
            let uu____738 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____738 in
          failwith uu____737
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____739 =
            let uu____740 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____740 in
          failwith uu____739
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____742 = FStar_Syntax_Util.unfold_lazy i in
          is_type_aux env uu____742
      | FStar_Syntax_Syntax.Tm_constant uu____743 -> false
      | FStar_Syntax_Syntax.Tm_type uu____744 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____745 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____752 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____769;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____770;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____771;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____773;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____774;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____775;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____776;_},
           s)
          ->
          let uu____820 = FStar_Syntax_Subst.subst' s t2 in
          is_arity env uu____820
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____821;
            FStar_Syntax_Syntax.index = uu____822;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____826;
            FStar_Syntax_Syntax.index = uu____827;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____832, uu____833) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____875) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____882) ->
          let uu____907 = FStar_Syntax_Subst.open_term bs body in
          (match uu____907 with | (uu____912, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
          let uu____929 =
            let uu____934 =
              let uu____935 = FStar_Syntax_Syntax.mk_binder x in [uu____935] in
            FStar_Syntax_Subst.open_term uu____934 body in
          (match uu____929 with | (uu____954, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____956, lbs), body) ->
          let uu____973 = FStar_Syntax_Subst.open_let_rec lbs body in
          (match uu____973 with | (uu____980, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____986, branches) ->
          (match branches with
           | b::uu____1025 ->
               let uu____1070 = FStar_Syntax_Subst.open_branch b in
               (match uu____1070 with
                | (uu____1071, uu____1072, e) -> is_type_aux env e)
           | uu____1090 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1107 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2, uu____1115) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head, uu____1121) -> is_type_aux env head
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1160 ->
           let uu____1161 = FStar_Syntax_Print.tag_of_term t in
           let uu____1162 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1161
             uu____1162);
      (let b = is_type_aux env t in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1168 ->
            if b
            then
              let uu____1169 = FStar_Syntax_Print.term_to_string t in
              let uu____1170 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1169
                uu____1170
            else
              (let uu____1172 = FStar_Syntax_Print.term_to_string t in
               let uu____1173 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1172 uu____1173));
       b)
let is_type_binder :
  'uuuuuu1180 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu1180) -> Prims.bool
  =
  fun env ->
    fun x ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1204 =
      let uu____1205 = FStar_Syntax_Subst.compress t in
      uu____1205.FStar_Syntax_Syntax.n in
    match uu____1204 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1208;
          FStar_Syntax_Syntax.fv_delta = uu____1209;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor);_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1210;
          FStar_Syntax_Syntax.fv_delta = uu____1211;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1212);_}
        -> true
    | uu____1219 -> false
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1225 =
      let uu____1226 = FStar_Syntax_Subst.compress t in
      uu____1226.FStar_Syntax_Syntax.n in
    match uu____1225 with
    | FStar_Syntax_Syntax.Tm_constant uu____1229 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1230 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1231 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1232 -> true
    | FStar_Syntax_Syntax.Tm_app (head, args) ->
        let uu____1277 = is_constructor head in
        if uu____1277
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1295 ->
                  match uu____1295 with
                  | (te, uu____1303) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1, uu____1310) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1316, uu____1317) ->
        is_fstar_value t1
    | uu____1358 -> false
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1364 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1365 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1366 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1367 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1378, exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1387, fields) ->
        FStar_Util.for_all
          (fun uu____1412 ->
             match uu____1412 with | (uu____1417, e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h, uu____1420) -> is_ml_value h
    | uu____1425 -> false
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0 ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1505 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____1507 = FStar_Syntax_Util.is_fun e' in
          if uu____1507
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 FStar_Pervasives_Native.None
let (unit_binder : unit -> FStar_Syntax_Syntax.binder) =
  fun uu____1521 ->
    let uu____1522 =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.t_unit in
    FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1522
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
      (let uu____1602 = FStar_List.hd l in
       match uu____1602 with
       | (p1, w1, e1) ->
           let uu____1636 =
             let uu____1645 = FStar_List.tl l in FStar_List.hd uu____1645 in
           (match uu____1636 with
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
                 | uu____1719 -> def)))
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
      let uu____1780 =
        FStar_List.fold_right
          (fun t ->
             fun uu____1809 ->
               match uu____1809 with
               | (uenv, vs) ->
                   let uu____1844 = FStar_Extraction_ML_UEnv.new_mlident uenv in
                   (match uu____1844 with
                    | (uenv1, v) -> (uenv1, ((v, t) :: vs)))) ts (g, []) in
      match uu____1780 with | (g1, vs_ts) -> (vs_ts, g1)
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
          let uu____1947 = s in
          match uu____1947 with
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
                      let uu___372_1973 = e in
                      {
                        FStar_Extraction_ML_Syntax.expr =
                          (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                        FStar_Extraction_ML_Syntax.mlty = ts;
                        FStar_Extraction_ML_Syntax.loc =
                          (uu___372_1973.FStar_Extraction_ML_Syntax.loc)
                      } in
                    (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
              else
                if n_args < n_vars
                then
                  (let extra_tyargs =
                     let uu____1986 = FStar_Util.first_N n_args vars in
                     match uu____1986 with
                     | (uu____1997, rest_vars) ->
                         FStar_All.pipe_right rest_vars
                           (FStar_List.map
                              (fun uu____2012 ->
                                 FStar_Extraction_ML_Syntax.MLTY_Erased)) in
                   let tyargs1 = FStar_List.append tyargs extra_tyargs in
                   let ts = instantiate_tyscheme (vars, t) tyargs1 in
                   let tapp =
                     let uu___383_2018 = e in
                     {
                       FStar_Extraction_ML_Syntax.expr =
                         (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                       FStar_Extraction_ML_Syntax.mlty = ts;
                       FStar_Extraction_ML_Syntax.loc =
                         (uu___383_2018.FStar_Extraction_ML_Syntax.loc)
                     } in
                   let t1 =
                     FStar_List.fold_left
                       (fun out ->
                          fun t1 ->
                            FStar_Extraction_ML_Syntax.MLTY_Fun
                              (t1, FStar_Extraction_ML_Syntax.E_PURE, out))
                       ts extra_tyargs in
                   let uu____2026 = fresh_mlidents extra_tyargs g in
                   match uu____2026 with
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
        let uu____2086 = FStar_Extraction_ML_Util.doms_and_cod t in
        match uu____2086 with
        | (ts, r) ->
            if ts = []
            then e
            else
              (let uu____2102 = fresh_mlidents ts g in
               match uu____2102 with
               | (vs_ts, g1) ->
                   let vs_es =
                     FStar_List.map
                       (fun uu____2137 ->
                          match uu____2137 with
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
      let uu____2163 = FStar_Extraction_ML_Util.doms_and_cod t in
      match uu____2163 with
      | (ts, r) ->
          let body r1 =
            let r2 =
              let uu____2183 = FStar_Extraction_ML_Util.udelta_unfold g r1 in
              match uu____2183 with
              | FStar_Pervasives_Native.None -> r1
              | FStar_Pervasives_Native.Some r2 -> r2 in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2187 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2)) in
          if ts = []
          then body r
          else
            (let uu____2191 = fresh_mlidents ts g in
             match uu____2191 with
             | (vs_ts, g1) ->
                 let uu____2216 =
                   let uu____2217 =
                     let uu____2228 = body r in (vs_ts, uu____2228) in
                   FStar_Extraction_ML_Syntax.MLE_Fun uu____2217 in
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
                   uu____2216)
let (maybe_eta_expand :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun expect ->
      fun e ->
        let uu____2250 =
          (FStar_Options.ml_no_eta_expand_coertions ()) ||
            (let uu____2252 = FStar_Options.codegen () in
             uu____2252 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin)) in
        if uu____2250 then e else eta_expand g expect e
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
            | uu____2321 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body) in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____2373 =
              match uu____2373 with
              | (pat, w, b) ->
                  let uu____2397 = aux b ty1 expect1 in (pat, w, uu____2397) in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun (arg::rest, body),
               FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____2404, t1),
               FStar_Extraction_ML_Syntax.MLTY_Fun (s0, uu____2407, s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____2434 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body)) in
                let body2 = aux body1 t1 s1 in
                let uu____2448 = type_leq g s0 t0 in
                if uu____2448
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____2451 =
                       let uu____2452 =
                         let uu____2453 =
                           let uu____2460 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg)) in
                           (uu____2460, s0, t0) in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____2453 in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____2452 in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____2451;
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
            | (FStar_Extraction_ML_Syntax.MLE_Let (lbs, body), uu____2472,
               uu____2473) ->
                let uu____2486 =
                  let uu____2487 =
                    let uu____2498 = aux body ty1 expect1 in
                    (lbs, uu____2498) in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____2487 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2486
            | (FStar_Extraction_ML_Syntax.MLE_Match (s, branches),
               uu____2507, uu____2508) ->
                let uu____2529 =
                  let uu____2530 =
                    let uu____2545 = FStar_List.map coerce_branch branches in
                    (s, uu____2545) in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____2530 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2529
            | (FStar_Extraction_ML_Syntax.MLE_If (s, b1, b2_opt), uu____2585,
               uu____2586) ->
                let uu____2591 =
                  let uu____2592 =
                    let uu____2601 = aux b1 ty1 expect1 in
                    let uu____2602 =
                      FStar_Util.map_opt b2_opt
                        (fun b2 -> aux b2 ty1 expect1) in
                    (s, uu____2601, uu____2602) in
                  FStar_Extraction_ML_Syntax.MLE_If uu____2592 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2591
            | (FStar_Extraction_ML_Syntax.MLE_Seq es, uu____2610, uu____2611)
                ->
                let uu____2614 = FStar_Util.prefix es in
                (match uu____2614 with
                 | (prefix, last) ->
                     let uu____2627 =
                       let uu____2628 =
                         let uu____2631 =
                           let uu____2634 = aux last ty1 expect1 in
                           [uu____2634] in
                         FStar_List.append prefix uu____2631 in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____2628 in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____2627)
            | (FStar_Extraction_ML_Syntax.MLE_Try (s, branches), uu____2637,
               uu____2638) ->
                let uu____2659 =
                  let uu____2660 =
                    let uu____2675 = FStar_List.map coerce_branch branches in
                    (s, uu____2675) in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____2660 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2659
            | uu____2712 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1)) in
          aux e ty expect
let maybe_coerce :
  'uuuuuu2731 .
    'uuuuuu2731 ->
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
            let uu____2758 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect in
            match uu____2758 with
            | (true, FStar_Pervasives_Native.Some e') -> e'
            | uu____2768 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                     default_value_for_ty g expect
                 | uu____2775 ->
                     let uu____2776 =
                       let uu____2777 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1 in
                       let uu____2778 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect in
                       type_leq g uu____2777 uu____2778 in
                     if uu____2776
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____2783 ->
                             let uu____2784 =
                               let uu____2785 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____2785 e in
                             let uu____2786 =
                               let uu____2787 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____2787 ty1 in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____2784 uu____2786);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____2794 ->
                             let uu____2795 =
                               let uu____2796 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____2796 e in
                             let uu____2797 =
                               let uu____2798 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____2798 ty1 in
                             let uu____2799 =
                               let uu____2800 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____2800 expect in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____2795 uu____2797 uu____2799);
                        (let uu____2801 = apply_coercion g e ty1 expect in
                         maybe_eta_expand g expect uu____2801)))
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun bv ->
      let uu____2812 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____2812 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____2814 -> FStar_Extraction_ML_Syntax.MLTY_Top
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
  fun uu____2825 ->
    let uu____2826 = FStar_Options.use_nbe_for_extraction () in
    if uu____2826
    then extraction_norm_steps_nbe
    else extraction_norm_steps_core
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2843 -> c
    | FStar_Syntax_Syntax.GTotal uu____2852 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____2888 ->
               match uu____2888 with
               | (uu____2903, aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args in
        let ct1 =
          let uu___550_2916 = ct in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___550_2916.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___550_2916.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___550_2916.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___550_2916.FStar_Syntax_Syntax.flags)
          } in
        let c1 =
          let uu___553_2920 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___553_2920.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___553_2920.FStar_Syntax_Syntax.vars)
          } in
        c1
let maybe_reify_comp :
  'uuuuuu2931 .
    'uuuuuu2931 ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun g ->
    fun env ->
      fun c ->
        let c1 = comp_no_args c in
        let uu____2950 =
          let uu____2951 =
            let uu____2952 =
              FStar_All.pipe_right c1 FStar_Syntax_Util.comp_effect_name in
            FStar_All.pipe_right uu____2952
              (FStar_TypeChecker_Env.norm_eff_name env) in
          FStar_All.pipe_right uu____2951
            (FStar_TypeChecker_Env.is_reifiable_effect env) in
        if uu____2950
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
      let arg_as_mlty g1 uu____3000 =
        match uu____3000 with
        | (a, uu____3008) ->
            let uu____3013 = is_type g1 a in
            if uu____3013
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_Syntax.MLTY_Erased in
      let fv_app_as_mlty g1 fv args =
        let uu____3031 =
          let uu____3032 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv in
          Prims.op_Negation uu____3032 in
        if uu____3031
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____3034 =
             let uu____3041 =
               let uu____3050 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
               FStar_TypeChecker_Env.lookup_lid uu____3050
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             match uu____3041 with
             | ((uu____3057, fvty), uu____3059) ->
                 let fvty1 =
                   let uu____3065 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.ForExtraction] uu____3065 fvty in
                 FStar_Syntax_Util.arrow_formals fvty1 in
           match uu____3034 with
           | (formals, uu____3067) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args in
               let mlargs1 =
                 let n_args = FStar_List.length args in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3103 = FStar_Util.first_N n_args formals in
                   match uu____3103 with
                   | (uu____3132, rest) ->
                       let uu____3166 =
                         FStar_List.map
                           (fun uu____3176 ->
                              FStar_Extraction_ML_Syntax.MLTY_Erased) rest in
                       FStar_List.append mlargs uu____3166
                 else mlargs in
               let nm =
                 FStar_Extraction_ML_UEnv.mlpath_of_lident g1
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)) in
      let aux env t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_type uu____3199 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3200 ->
            let uu____3201 =
              let uu____3202 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3202 in
            failwith uu____3201
        | FStar_Syntax_Syntax.Tm_delayed uu____3203 ->
            let uu____3218 =
              let uu____3219 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3219 in
            failwith uu____3218
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu____3220 =
              let uu____3221 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3221 in
            failwith uu____3220
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3223 = FStar_Syntax_Util.unfold_lazy i in
            translate_term_to_mlty env uu____3223
        | FStar_Syntax_Syntax.Tm_constant uu____3224 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_quoted uu____3225 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_uvar uu____3232 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_meta (t2, uu____3246) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3251;
               FStar_Syntax_Syntax.index = uu____3252;
               FStar_Syntax_Syntax.sort = t2;_},
             uu____3254)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2, uu____3262) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____3268, uu____3269) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let uu____3342 = FStar_Syntax_Subst.open_comp bs c in
            (match uu____3342 with
             | (bs1, c1) ->
                 let uu____3349 = binders_as_ml_binders env bs1 in
                 (match uu____3349 with
                  | (mlbs, env1) ->
                      let t_ret =
                        let uu____3375 =
                          let uu____3376 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv env1 in
                          maybe_reify_comp env1 uu____3376 c1 in
                        translate_term_to_mlty env1 uu____3375 in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____3378 =
                        FStar_List.fold_right
                          (fun uu____3397 ->
                             fun uu____3398 ->
                               match (uu____3397, uu____3398) with
                               | ((uu____3419, t2), (tag, t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret) in
                      (match uu____3378 with | (uu____3431, t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head, args) ->
            let res =
              let uu____3460 =
                let uu____3461 = FStar_Syntax_Util.un_uinst head in
                uu____3461.FStar_Syntax_Syntax.n in
              match uu____3460 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head1, args') ->
                  let uu____3492 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head1, (FStar_List.append args' args)))
                      t1.FStar_Syntax_Syntax.pos in
                  translate_term_to_mlty env uu____3492
              | uu____3513 -> FStar_Extraction_ML_Syntax.MLTY_Top in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____3516) ->
            let uu____3541 = FStar_Syntax_Subst.open_term bs ty in
            (match uu____3541 with
             | (bs1, ty1) ->
                 let uu____3548 = binders_as_ml_binders env bs1 in
                 (match uu____3548 with
                  | (bts, env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____3573 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_match uu____3586 ->
            FStar_Extraction_ML_Syntax.MLTY_Top in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____3615 ->
            let uu____3622 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____3622 with
             | FStar_Pervasives_Native.None -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____3626 -> false in
      let uu____3627 =
        let uu____3628 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
        FStar_TypeChecker_Util.must_erase_for_extraction uu____3628 t0 in
      if uu____3627
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0 in
         let uu____3631 = is_top_ty mlt in
         if uu____3631 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)
and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g ->
    fun bs ->
      let uu____3645 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____3699 ->
                fun b ->
                  match uu____3699 with
                  | (ml_bs, env) ->
                      let uu____3741 = is_type_binder g b in
                      if uu____3741
                      then
                        let b1 = FStar_Pervasives_Native.fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1 true in
                        let ml_b =
                          let uu____3759 =
                            FStar_Extraction_ML_UEnv.lookup_ty env1 b1 in
                          uu____3759.FStar_Extraction_ML_UEnv.ty_b_name in
                        let ml_b1 =
                          (ml_b, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b1 :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort in
                         let uu____3780 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false in
                         match uu____3780 with
                         | (env1, b2, uu____3799) ->
                             let ml_b = (b2, t) in ((ml_b :: ml_bs), env1)))
             ([], g)) in
      match uu____3645 with | (ml_bs, env) -> ((FStar_List.rev ml_bs), env)
let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t0 ->
      let t =
        let uu____3870 = extraction_norm_steps () in
        let uu____3871 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
        FStar_TypeChecker_Normalize.normalize uu____3870 uu____3871 t0 in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1, uu____3889) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____3892, FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____3896 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                    | uu____3922 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____3923 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____3924 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____3933 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
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
            (fun uu____4004 ->
               fun x -> match uu____4004 with | (p, s) -> (s, x)) fns1 xs
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
            let uu____4047 = FStar_Extraction_ML_Util.is_xtuple d in
            (match uu____4047 with
             | FStar_Pervasives_Native.Some n ->
                 FStar_Extraction_ML_Syntax.MLP_Tuple pats
             | uu____4051 ->
                 (match q with
                  | FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor (ty, fns)) ->
                      let path =
                        let uu____4063 = FStar_Ident.ns_of_lid ty in
                        FStar_List.map FStar_Ident.string_of_id uu____4063 in
                      let fs = record_fields g ty fns pats in
                      FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                  | uu____4081 -> p))
        | uu____4084 -> p
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
                       (fun uu____4176 ->
                          let uu____4177 =
                            let uu____4178 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4178 t' in
                          let uu____4179 =
                            let uu____4180 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4180 t in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4177 uu____4179)
                   else ();
                   ok) in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c, swopt)) when
                let uu____4210 = FStar_Options.codegen () in
                uu____4210 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4215 =
                  match swopt with
                  | FStar_Pervasives_Native.None ->
                      let uu____4228 =
                        let uu____4229 =
                          let uu____4230 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None)) in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4230 in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4229 in
                      (uu____4228, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        let uu____4251 =
                          let uu____4252 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                          uu____4252.FStar_TypeChecker_Env.dsenv in
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          uu____4251 c sw FStar_Range.dummyRange in
                      let uu____4253 = term_as_mlexpr g source_term in
                      (match uu____4253 with
                       | (mlterm, uu____4265, mlty) -> (mlterm, mlty)) in
                (match uu____4215 with
                 | (mlc, ml_ty) ->
                     let uu____4283 = FStar_Extraction_ML_UEnv.new_mlident g in
                     (match uu____4283 with
                      | (g1, x) ->
                          let when_clause =
                            let uu____4305 =
                              let uu____4306 =
                                let uu____4313 =
                                  let uu____4316 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         ml_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Var x) in
                                  [uu____4316; mlc] in
                                (FStar_Extraction_ML_Util.prims_op_equality,
                                  uu____4313) in
                              FStar_Extraction_ML_Syntax.MLE_App uu____4306 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_bool_ty)
                              uu____4305 in
                          let uu____4319 = ok ml_ty in
                          (g1,
                            (FStar_Pervasives_Native.Some
                               ((FStar_Extraction_ML_Syntax.MLP_Var x),
                                 [when_clause])), uu____4319)))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  let uu____4338 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                  FStar_TypeChecker_TcTerm.tc_constant uu____4338
                    FStar_Range.dummyRange s in
                let mlty = term_as_mlty g t in
                let uu____4340 =
                  let uu____4349 =
                    let uu____4356 =
                      let uu____4357 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4357 in
                    (uu____4356, []) in
                  FStar_Pervasives_Native.Some uu____4349 in
                let uu____4366 = ok mlty in (g, uu____4340, uu____4366)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____4377 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false imp in
                (match uu____4377 with
                 | (g1, x1, uu____4400) ->
                     let uu____4401 = ok mlty in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4401))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____4435 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false imp in
                (match uu____4435 with
                 | (g1, x1, uu____4458) ->
                     let uu____4459 = ok mlty in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4459))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4491 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f, pats) ->
                let uu____4530 =
                  let uu____4539 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                  match uu____4539 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____4548;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n;
                          FStar_Extraction_ML_Syntax.mlty = uu____4550;
                          FStar_Extraction_ML_Syntax.loc = uu____4551;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;_} ->
                      (n, ttys)
                  | uu____4557 -> failwith "Expected a constructor" in
                (match uu____4530 with
                 | (d, tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys) in
                     let uu____4591 = FStar_Util.first_N nTyVars pats in
                     (match uu____4591 with
                      | (tysVarPats, restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___852_4687 ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____4716 ->
                                               match uu____4716 with
                                               | (p1, uu____4722) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____4723, t) ->
                                                        term_as_mlty g t
                                                    | uu____4729 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____4733 ->
                                                              let uu____4734
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____4734);
                                                         FStar_Exn.raise
                                                           Un_extractable)))) in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args in
                                     let uu____4736 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty in
                                     FStar_Pervasives_Native.Some uu____4736)
                                ()
                            with
                            | Un_extractable -> FStar_Pervasives_Native.None in
                          let uu____4765 =
                            FStar_Util.fold_map
                              (fun g1 ->
                                 fun uu____4801 ->
                                   match uu____4801 with
                                   | (p1, imp1) ->
                                       let uu____4820 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr in
                                       (match uu____4820 with
                                        | (g2, p2, uu____4849) -> (g2, p2)))
                              g tysVarPats in
                          (match uu____4765 with
                           | (g1, tyMLPats) ->
                               let uu____4910 =
                                 FStar_Util.fold_map
                                   (fun uu____4974 ->
                                      fun uu____4975 ->
                                        match (uu____4974, uu____4975) with
                                        | ((g2, f_ty_opt1), (p1, imp1)) ->
                                            let uu____5068 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd::rest, res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd))
                                              | uu____5128 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None) in
                                            (match uu____5068 with
                                             | (f_ty_opt2, expected_ty) ->
                                                 let uu____5199 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr in
                                                 (match uu____5199 with
                                                  | (g3, p2, uu____5240) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats in
                               (match uu____4910 with
                                | ((g2, f_ty_opt1), restMLPats) ->
                                    let uu____5358 =
                                      let uu____5369 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5420 ->
                                                match uu___0_5420 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____5462 -> [])) in
                                      FStar_All.pipe_right uu____5369
                                        FStar_List.split in
                                    (match uu____5358 with
                                     | (mlPats, when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([], t) -> ok t
                                           | uu____5535 -> false in
                                         let uu____5544 =
                                           let uu____5553 =
                                             let uu____5560 =
                                               resugar_pat g2
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats)) in
                                             let uu____5563 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten in
                                             (uu____5560, uu____5563) in
                                           FStar_Pervasives_Native.Some
                                             uu____5553 in
                                         (g2, uu____5544, pat_ty_compat))))))
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
            let uu____5690 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr in
            match uu____5690 with
            | (g2, FStar_Pervasives_Native.Some (x, v), b) -> (g2, (x, v), b)
            | uu____5747 ->
                failwith "Impossible: Unable to translate pattern" in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd::tl ->
                let uu____5792 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl in
                FStar_Pervasives_Native.Some uu____5792 in
          let uu____5793 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t) in
          match uu____5793 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____5948, t1) ->
                let uu____5950 = FStar_Extraction_ML_UEnv.new_mlident g1 in
                (match uu____5950 with
                 | (g2, x) ->
                     let uu____5971 =
                       let uu____5982 =
                         let uu____5991 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty t0)
                             (FStar_Extraction_ML_Syntax.MLE_Var x) in
                         ((x, t0), uu____5991) in
                       uu____5982 :: more_args in
                     eta_args g2 uu____5971 t1)
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6004, uu____6005)
                -> ((FStar_List.rev more_args), t)
            | uu____6028 ->
                let uu____6029 =
                  let uu____6030 =
                    let uu____6031 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1 in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu____6031
                      mlAppExpr in
                  let uu____6032 =
                    let uu____6033 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1 in
                    FStar_Extraction_ML_Code.string_of_mlty uu____6033 t in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6030 uu____6032 in
                failwith uu____6029 in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____6065, args),
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
               (tyname, fields))) ->
                let path =
                  let uu____6082 = FStar_Ident.ns_of_lid tyname in
                  FStar_List.map FStar_Ident.string_of_id uu____6082 in
                let fields1 = record_fields g tyname fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6100 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____6122 = eta_args g [] residualType in
            match uu____6122 with
            | (eargs, tres) ->
                (match eargs with
                 | [] ->
                     let uu____6175 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____6175
                 | uu____6176 ->
                     let uu____6187 = FStar_List.unzip eargs in
                     (match uu____6187 with
                      | (binders, eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head, args)
                               ->
                               let body =
                                 let uu____6229 =
                                   let uu____6230 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6230 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6229 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6239 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6242, FStar_Pervasives_Native.None) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6246;
                FStar_Extraction_ML_Syntax.loc = uu____6247;_},
              mle::args),
             FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname, f))) ->
              let fn =
                let uu____6259 =
                  let uu____6264 =
                    let uu____6265 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6265
                      constrname in
                  (uu____6264, f) in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6259 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____6268 ->
                    let uu____6271 =
                      let uu____6278 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____6278, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6271 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6282;
                     FStar_Extraction_ML_Syntax.loc = uu____6283;_},
                   uu____6284);
                FStar_Extraction_ML_Syntax.mlty = uu____6285;
                FStar_Extraction_ML_Syntax.loc = uu____6286;_},
              mle::args),
             FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname, f))) ->
              let fn =
                let uu____6302 =
                  let uu____6307 =
                    let uu____6308 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6308
                      constrname in
                  (uu____6307, f) in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6302 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____6311 ->
                    let uu____6314 =
                      let uu____6321 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____6321, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6314 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6325;
                FStar_Extraction_ML_Syntax.loc = uu____6326;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____6334 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6334
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6338;
                FStar_Extraction_ML_Syntax.loc = uu____6339;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____6341)) ->
              let uu____6354 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6354
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6358;
                     FStar_Extraction_ML_Syntax.loc = uu____6359;_},
                   uu____6360);
                FStar_Extraction_ML_Syntax.mlty = uu____6361;
                FStar_Extraction_ML_Syntax.loc = uu____6362;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____6374 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6374
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6378;
                     FStar_Extraction_ML_Syntax.loc = uu____6379;_},
                   uu____6380);
                FStar_Extraction_ML_Syntax.mlty = uu____6381;
                FStar_Extraction_ML_Syntax.loc = uu____6382;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____6384)) ->
              let uu____6401 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6401
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____6407 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6407
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____6411)) ->
              let uu____6420 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6420
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6424;
                FStar_Extraction_ML_Syntax.loc = uu____6425;_},
              uu____6426),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____6433 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6433
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6437;
                FStar_Extraction_ML_Syntax.loc = uu____6438;_},
              uu____6439),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____6440)) ->
              let uu____6453 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6453
          | uu____6456 -> mlAppExpr
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
        | uu____6486 -> (ml_e, tag)
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
      let maybe_generalize uu____6544 =
        match uu____6544 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____6564;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____6569;_} ->
            let f_e = effect_as_etag g lbeff in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp in
            let no_gen uu____6647 =
              let expected_t = term_as_mlty g lbtyp1 in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef) in
            let uu____6717 =
              let uu____6718 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
              FStar_TypeChecker_Util.must_erase_for_extraction uu____6718
                lbtyp1 in
            if uu____6717
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                   let uu____6796 = FStar_List.hd bs in
                   FStar_All.pipe_right uu____6796 (is_type_binder g) ->
                   let uu____6817 = FStar_Syntax_Subst.open_comp bs c in
                   (match uu____6817 with
                    | (bs1, c1) ->
                        let uu____6842 =
                          let uu____6855 =
                            FStar_Util.prefix_until
                              (fun x ->
                                 let uu____6901 = is_type_binder g x in
                                 Prims.op_Negation uu____6901) bs1 in
                          match uu____6855 with
                          | FStar_Pervasives_Native.None ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2, b, rest) ->
                              let uu____7027 =
                                FStar_Syntax_Util.arrow (b :: rest) c1 in
                              (bs2, uu____7027) in
                        (match uu____6842 with
                         | (tbinders, tbody) ->
                             let n_tbinders = FStar_List.length tbinders in
                             let lbdef1 =
                               let uu____7088 = normalize_abs lbdef in
                               FStar_All.pipe_right uu____7088
                                 FStar_Syntax_Util.unmeta in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2, body, copt)
                                  ->
                                  let uu____7136 =
                                    FStar_Syntax_Subst.open_term bs2 body in
                                  (match uu____7136 with
                                   | (bs3, body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7185 =
                                           FStar_Util.first_N n_tbinders bs3 in
                                         (match uu____7185 with
                                          | (targs, rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7287 ->
                                                       fun uu____7288 ->
                                                         match (uu____7287,
                                                                 uu____7288)
                                                         with
                                                         | ((x, uu____7314),
                                                            (y, uu____7316))
                                                             ->
                                                             let uu____7337 =
                                                               let uu____7344
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y in
                                                               (x,
                                                                 uu____7344) in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7337)
                                                    tbinders targs in
                                                FStar_Syntax_Subst.subst s
                                                  tbody in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env ->
                                                     fun uu____7361 ->
                                                       match uu____7361 with
                                                       | (a, uu____7369) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a false) g
                                                  targs in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty in
                                              let polytype =
                                                let uu____7380 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____7399 ->
                                                          match uu____7399
                                                          with
                                                          | (x, uu____7407)
                                                              ->
                                                              let uu____7412
                                                                =
                                                                FStar_Extraction_ML_UEnv.lookup_ty
                                                                  env x in
                                                              uu____7412.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                                (uu____7380, expected_t) in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____7422 =
                                                       is_fstar_value body1 in
                                                     Prims.op_Negation
                                                       uu____7422)
                                                      ||
                                                      (let uu____7424 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1 in
                                                       Prims.op_Negation
                                                         uu____7424)
                                                | uu____7425 -> false in
                                              let rest_args1 =
                                                if add_unit
                                                then
                                                  let uu____7435 =
                                                    unit_binder () in
                                                  uu____7435 :: rest_args
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____7485 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env ->
                                         fun uu____7504 ->
                                           match uu____7504 with
                                           | (a, uu____7512) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu____7523 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____7542 ->
                                              match uu____7542 with
                                              | (x, uu____7550) ->
                                                  let uu____7555 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x in
                                                  uu____7555.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                    (uu____7523, expected_t) in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____7595 ->
                                            match uu____7595 with
                                            | (bv, uu____7603) ->
                                                let uu____7608 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_All.pipe_right
                                                  uu____7608
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | FStar_Syntax_Syntax.Tm_fvar uu____7636 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env ->
                                         fun uu____7649 ->
                                           match uu____7649 with
                                           | (a, uu____7657) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu____7668 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____7687 ->
                                              match uu____7687 with
                                              | (x, uu____7695) ->
                                                  let uu____7700 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x in
                                                  uu____7700.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                    (uu____7668, expected_t) in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____7740 ->
                                            match uu____7740 with
                                            | (bv, uu____7748) ->
                                                let uu____7753 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_All.pipe_right
                                                  uu____7753
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | FStar_Syntax_Syntax.Tm_name uu____7781 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env ->
                                         fun uu____7794 ->
                                           match uu____7794 with
                                           | (a, uu____7802) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu____7813 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____7832 ->
                                              match uu____7832 with
                                              | (x, uu____7840) ->
                                                  let uu____7845 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x in
                                                  uu____7845.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                    (uu____7813, expected_t) in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____7885 ->
                                            match uu____7885 with
                                            | (bv, uu____7893) ->
                                                let uu____7898 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_All.pipe_right
                                                  uu____7898
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | uu____7926 -> err_value_restriction lbdef1)))
               | uu____7945 -> no_gen ()) in
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
           fun uu____8086 ->
             match uu____8086 with
             | (lbname, e_tag, (typ, (binders, mltyscheme)), add_unit, _body)
                 ->
                 let uu____8144 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit in
                 (match uu____8144 with
                  | (env1, uu____8160, exp_binding) ->
                      let uu____8162 =
                        let uu____8167 = FStar_Util.right lbname in
                        (uu____8167, exp_binding) in
                      (env1, uu____8162))) g lbs1
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
            (fun uu____8233 ->
               let uu____8234 = FStar_Syntax_Print.term_to_string e in
               let uu____8235 =
                 let uu____8236 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g in
                 FStar_Extraction_ML_Code.string_of_mlty uu____8236 ty in
               let uu____8237 = FStar_Extraction_ML_Util.eff_to_string f in
               FStar_Util.print3 "Checking %s at type %s and eff %s\n"
                 uu____8234 uu____8235 uu____8237);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST, uu____8242) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE,
              FStar_Extraction_ML_Syntax.MLTY_Erased) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8243 ->
               let uu____8248 = term_as_mlexpr g e in
               (match uu____8248 with
                | (ml_e, tag, t) ->
                    let uu____8262 = FStar_Extraction_ML_Util.eff_leq tag f in
                    if uu____8262
                    then
                      let uu____8267 =
                        maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t ty in
                      (uu____8267, ty)
                    else
                      (match (tag, f, ty) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST,
                          FStar_Extraction_ML_Syntax.E_PURE,
                          FStar_Extraction_ML_Syntax.MLTY_Erased) ->
                           let uu____8273 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t
                               ty in
                           (uu____8273, ty)
                       | uu____8274 ->
                           (err_unexpected_eff g e ty f tag;
                            (let uu____8282 =
                               maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e
                                 t ty in
                             (uu____8282, ty))))))
and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun e ->
      let uu____8291 = term_as_mlexpr' g e in
      match uu____8291 with
      | (e1, f, t) ->
          let uu____8307 = maybe_promote_effect e1 f t in
          (match uu____8307 with | (e2, f1) -> (e2, f1, t))
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
           let uu____8333 =
             let uu____8334 =
               FStar_Range.string_of_range top1.FStar_Syntax_Syntax.pos in
             let uu____8335 = FStar_Syntax_Print.tag_of_term top1 in
             let uu____8336 = FStar_Syntax_Print.term_to_string top1 in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____8334 uu____8335 uu____8336 in
           FStar_Util.print_string uu____8333);
      (let is_match t =
         let uu____8343 =
           let uu____8344 =
             let uu____8347 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress in
             FStar_All.pipe_right uu____8347 FStar_Syntax_Util.unascribe in
           uu____8344.FStar_Syntax_Syntax.n in
         match uu____8343 with
         | FStar_Syntax_Syntax.Tm_match uu____8350 -> true
         | uu____8373 -> false in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____8390 ->
              match uu____8390 with
              | (t, uu____8398) ->
                  let uu____8403 =
                    let uu____8404 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress in
                    uu____8404.FStar_Syntax_Syntax.n in
                  (match uu____8403 with
                   | FStar_Syntax_Syntax.Tm_name uu____8409 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____8410 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____8411 -> true
                   | uu____8412 -> false)) in
       let apply_to_match_branches head args =
         let uu____8450 =
           let uu____8451 =
             let uu____8454 =
               FStar_All.pipe_right head FStar_Syntax_Subst.compress in
             FStar_All.pipe_right uu____8454 FStar_Syntax_Util.unascribe in
           uu____8451.FStar_Syntax_Syntax.n in
         match uu____8450 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee, branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____8578 ->
                       match uu____8578 with
                       | (pat, when_opt, body) ->
                           (pat, when_opt,
                             (let uu___1319_8635 = body in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1319_8635.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1319_8635.FStar_Syntax_Syntax.vars)
                              })))) in
             let uu___1322_8650 = head in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1322_8650.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1322_8650.FStar_Syntax_Syntax.vars)
             }
         | uu____8671 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match" in
       let t = FStar_Syntax_Subst.compress top1 in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu____8681 =
             let uu____8682 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8682 in
           failwith uu____8681
       | FStar_Syntax_Syntax.Tm_delayed uu____8689 ->
           let uu____8704 =
             let uu____8705 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8705 in
           failwith uu____8704
       | FStar_Syntax_Syntax.Tm_uvar uu____8712 ->
           let uu____8725 =
             let uu____8726 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8726 in
           failwith uu____8725
       | FStar_Syntax_Syntax.Tm_bvar uu____8733 ->
           let uu____8734 =
             let uu____8735 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____8735 in
           failwith uu____8734
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____8743 = FStar_Syntax_Util.unfold_lazy i in
           term_as_mlexpr g uu____8743
       | FStar_Syntax_Syntax.Tm_type uu____8744 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____8745 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____8752 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
              FStar_Syntax_Syntax.antiquotes = uu____8768;_})
           ->
           let uu____8781 =
             let uu____8782 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____8782 in
           (match uu____8781 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____8789;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____8791;_} ->
                let uu____8792 =
                  let uu____8793 =
                    let uu____8794 =
                      let uu____8801 =
                        let uu____8804 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime")) in
                        [uu____8804] in
                      (fw, uu____8801) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____8794 in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____8793 in
                (uu____8792, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
              FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____8821 = FStar_Reflection_Basic.inspect_ln qt in
           (match uu____8821 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____8829 = FStar_Syntax_Syntax.lookup_aq bv aqs in
                (match uu____8829 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None ->
                     let tv =
                       let uu____8840 =
                         let uu____8847 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs in
                         FStar_Syntax_Embeddings.embed uu____8847
                           (FStar_Reflection_Data.Tv_Var bv) in
                       uu____8840 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb in
                     let t1 =
                       let uu____8855 =
                         let uu____8866 = FStar_Syntax_Syntax.as_arg tv in
                         [uu____8866] in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____8855 in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____8893 =
                    let uu____8900 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs in
                    FStar_Syntax_Embeddings.embed uu____8900 tv in
                  uu____8893 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb in
                let t1 =
                  let uu____8908 =
                    let uu____8919 = FStar_Syntax_Syntax.as_arg tv1 in
                    [uu____8919] in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____8908 in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____8946)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____8976 =
                  let uu____8983 =
                    let uu____8992 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Env.effect_decl_opt uu____8992 m in
                  FStar_Util.must uu____8983 in
                (match uu____8976 with
                 | (ed, qualifiers) ->
                     let uu____9011 =
                       let uu____9012 =
                         let uu____9013 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                         FStar_TypeChecker_Env.is_reifiable_effect uu____9013
                           ed.FStar_Syntax_Syntax.mname in
                       Prims.op_Negation uu____9012 in
                     if uu____9011
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9027 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1, uu____9029) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1, uu____9035) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9041 =
             let uu____9048 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
             FStar_TypeChecker_TcTerm.type_of_tot_term uu____9048 t in
           (match uu____9041 with
            | (uu____9055, ty, uu____9057) ->
                let ml_ty = term_as_mlty g ty in
                let uu____9059 =
                  let uu____9060 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9060 in
                (uu____9059, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9061 ->
           let uu____9062 = is_type g t in
           if uu____9062
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9070 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____9070 with
              | (FStar_Util.Inl uu____9083, uu____9084) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9089;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_},
                 qual) ->
                  (match mltys with
                   | ([], t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([], t1) ->
                       let uu____9105 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____9105, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9106 -> instantiate_maybe_partial g x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9108 = is_type g t in
           if uu____9108
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9116 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv in
              match uu____9116 with
              | FStar_Pervasives_Native.None ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9125;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9133 ->
                        let uu____9134 = FStar_Syntax_Print.fv_to_string fv in
                        let uu____9135 =
                          let uu____9136 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g in
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            uu____9136 x in
                        let uu____9137 =
                          let uu____9138 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g in
                          FStar_Extraction_ML_Code.string_of_mlty uu____9138
                            (FStar_Pervasives_Native.snd mltys) in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9134 uu____9135 uu____9137);
                   (match mltys with
                    | ([], t1) when
                        t1 = FStar_Extraction_ML_Syntax.ml_unit_ty ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([], t1) ->
                        let uu____9147 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x in
                        (uu____9147, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9148 -> instantiate_maybe_partial g x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs, body, rcopt) ->
           let uu____9176 = FStar_Syntax_Subst.open_term bs body in
           (match uu____9176 with
            | (bs1, body1) ->
                let uu____9189 = binders_as_ml_binders g bs1 in
                (match uu____9189 with
                 | (ml_bs, env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9222 =
                             let uu____9223 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
                             FStar_TypeChecker_Env.is_reifiable_rc uu____9223
                               rc in
                           if uu____9222
                           then
                             let uu____9224 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
                             FStar_TypeChecker_Util.reify_body uu____9224
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.ForExtraction;
                               FStar_TypeChecker_Env.Unascribe] body1
                           else body1
                       | FStar_Pervasives_Native.None ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9229 ->
                                 let uu____9230 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9230);
                            body1) in
                     let uu____9231 = term_as_mlexpr env body2 in
                     (match uu____9231 with
                      | (ml_body, f, t1) ->
                          let uu____9247 =
                            FStar_List.fold_right
                              (fun uu____9266 ->
                                 fun uu____9267 ->
                                   match (uu____9266, uu____9267) with
                                   | ((uu____9288, targ), (f1, t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____9247 with
                           | (f1, tfun) ->
                               let uu____9308 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____9308, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____9315;
              FStar_Syntax_Syntax.vars = uu____9316;_},
            (a1, uu____9318)::[])
           ->
           let ty =
             let uu____9358 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
             term_as_mlty g uu____9358 in
           let uu____9359 =
             let uu____9360 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____9360 in
           (uu____9359, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____9361;
              FStar_Syntax_Syntax.vars = uu____9362;_},
            (t1, uu____9364)::(r, uu____9366)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____9421);
              FStar_Syntax_Syntax.pos = uu____9422;
              FStar_Syntax_Syntax.vars = uu____9423;_},
            uu____9424)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head, args) when
           (is_match head) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____9481 =
             FStar_All.pipe_right args (apply_to_match_branches head) in
           FStar_All.pipe_right uu____9481 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head, args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_9533 ->
                        match uu___1_9533 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | uu____9534 -> false))) in
           let uu____9535 =
             let uu____9536 =
               let uu____9539 =
                 FStar_All.pipe_right head FStar_Syntax_Subst.compress in
               FStar_All.pipe_right uu____9539 FStar_Syntax_Util.unascribe in
             uu____9536.FStar_Syntax_Syntax.n in
           (match uu____9535 with
            | FStar_Syntax_Syntax.Tm_abs (bs, uu____9549, _rc) ->
                let uu____9575 =
                  let uu____9576 =
                    let uu____9581 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses;
                      FStar_TypeChecker_Env.ForExtraction] uu____9581 in
                  FStar_All.pipe_right t uu____9576 in
                FStar_All.pipe_right uu____9575 (term_as_mlexpr g)
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) ->
                let e =
                  let uu____9589 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                  let uu____9590 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg uu____9589
                    [FStar_TypeChecker_Env.Inlining;
                    FStar_TypeChecker_Env.ForExtraction;
                    FStar_TypeChecker_Env.Unascribe] head uu____9590 in
                let tm =
                  let uu____9600 = FStar_TypeChecker_Util.remove_reify e in
                  let uu____9601 = FStar_List.tl args in
                  FStar_Syntax_Syntax.mk_Tm_app uu____9600 uu____9601
                    t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr g tm
            | uu____9610 ->
                let rec extract_app is_data uu____9659 uu____9660 restArgs =
                  match (uu____9659, uu____9660) with
                  | ((mlhead, mlargs_f), (f, t1)) ->
                      let mk_head uu____9741 =
                        let mlargs =
                          FStar_All.pipe_right (FStar_List.rev mlargs_f)
                            (FStar_List.map FStar_Pervasives_Native.fst) in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty t1)
                          (FStar_Extraction_ML_Syntax.MLE_App
                             (mlhead, mlargs)) in
                      (FStar_Extraction_ML_UEnv.debug g
                         (fun uu____9768 ->
                            let uu____9769 =
                              let uu____9770 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g in
                              let uu____9771 = mk_head () in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____9770 uu____9771 in
                            let uu____9772 =
                              let uu____9773 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g in
                              FStar_Extraction_ML_Code.string_of_mlty
                                uu____9773 t1 in
                            let uu____9774 =
                              match restArgs with
                              | [] -> "none"
                              | (hd, uu____9782)::uu____9783 ->
                                  FStar_Syntax_Print.term_to_string hd in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____9769 uu____9772 uu____9774);
                       (match (restArgs, t1) with
                        | ([], uu____9816) ->
                            let app =
                              let uu____9832 = mk_head () in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____9832 in
                            (app, f, t1)
                        | ((arg, uu____9834)::rest,
                           FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t, f', t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____9865 =
                              let uu____9870 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f' in
                              (uu____9870, t2) in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____9865 rest
                        | ((e0, uu____9882)::rest,
                           FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected, f', t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos in
                            let expected_effect =
                              let uu____9915 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head) in
                              if uu____9915
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE in
                            let uu____9917 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected in
                            (match uu____9917 with
                             | (e01, tInferred) ->
                                 let uu____9930 =
                                   let uu____9935 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f'] in
                                   (uu____9935, t2) in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____9930 rest)
                        | uu____9946 ->
                            let uu____9959 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1 in
                            (match uu____9959 with
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
                                  | uu____10031 ->
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
                let extract_app_maybe_projector is_data mlhead uu____10102
                  args1 =
                  match uu____10102 with
                  | (f, t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10132)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10216))::args3,
                                FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____10218, f', t3)) ->
                                 let uu____10255 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____10255 t3
                             | uu____10256 -> (args2, f1, t2) in
                           let uu____10281 = remove_implicits args1 f t1 in
                           (match uu____10281 with
                            | (args2, f1, t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____10337 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let extract_app_with_instantiations uu____10361 =
                  let head1 = FStar_Syntax_Util.un_uinst head in
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____10369 ->
                      let uu____10370 =
                        let uu____10385 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1 in
                        match uu____10385 with
                        | (FStar_Util.Inr exp_b, q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____10417 ->
                                  let uu____10418 =
                                    FStar_Syntax_Print.term_to_string head1 in
                                  let uu____10419 =
                                    let uu____10420 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____10420
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr in
                                  let uu____10421 =
                                    let uu____10422 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____10422
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme) in
                                  FStar_Util.print3
                                    "@@@looked up %s: got %s at %s\n"
                                    uu____10418 uu____10419 uu____10421);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu____10437 -> failwith "FIXME Ty" in
                      (match uu____10370 with
                       | ((head_ml, (vars, t1)), qual) ->
                           let has_typ_apps =
                             match args with
                             | (a, uu____10486)::uu____10487 -> is_type g a
                             | uu____10514 -> false in
                           let uu____10525 =
                             let n = FStar_List.length vars in
                             let uu____10541 =
                               if (FStar_List.length args) <= n
                               then
                                 let uu____10578 =
                                   FStar_List.map
                                     (fun uu____10590 ->
                                        match uu____10590 with
                                        | (x, uu____10598) ->
                                            term_as_mlty g x) args in
                                 (uu____10578, [])
                               else
                                 (let uu____10620 = FStar_Util.first_N n args in
                                  match uu____10620 with
                                  | (prefix, rest) ->
                                      let uu____10709 =
                                        FStar_List.map
                                          (fun uu____10721 ->
                                             match uu____10721 with
                                             | (x, uu____10729) ->
                                                 term_as_mlty g x) prefix in
                                      (uu____10709, rest)) in
                             match uu____10541 with
                             | (provided_type_args, rest) ->
                                 let uu____10780 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu____10789 ->
                                       let uu____10790 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu____10790 with
                                        | (head2, uu____10802, t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu____10804 ->
                                       let uu____10805 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu____10805 with
                                        | (head2, uu____10817, t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head2,
                                        {
                                          FStar_Extraction_ML_Syntax.expr =
                                            FStar_Extraction_ML_Syntax.MLE_Const
                                            (FStar_Extraction_ML_Syntax.MLC_Unit);
                                          FStar_Extraction_ML_Syntax.mlty =
                                            uu____10820;
                                          FStar_Extraction_ML_Syntax.loc =
                                            uu____10821;_}::[])
                                       ->
                                       let uu____10824 =
                                         instantiate_maybe_partial g head2
                                           (vars, t1) provided_type_args in
                                       (match uu____10824 with
                                        | (head3, uu____10836, t2) ->
                                            let uu____10838 =
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head3,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2) in
                                            (uu____10838, t2))
                                   | uu____10841 ->
                                       failwith
                                         "Impossible: Unexpected head term" in
                                 (match uu____10780 with
                                  | (head2, t2) -> (head2, t2, rest)) in
                           (match uu____10525 with
                            | (head_ml1, head_t, args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____10907 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1 in
                                     (uu____10907,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____10908 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____10917 ->
                      let uu____10918 =
                        let uu____10933 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1 in
                        match uu____10933 with
                        | (FStar_Util.Inr exp_b, q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____10965 ->
                                  let uu____10966 =
                                    FStar_Syntax_Print.term_to_string head1 in
                                  let uu____10967 =
                                    let uu____10968 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____10968
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr in
                                  let uu____10969 =
                                    let uu____10970 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____10970
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme) in
                                  FStar_Util.print3
                                    "@@@looked up %s: got %s at %s\n"
                                    uu____10966 uu____10967 uu____10969);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu____10985 -> failwith "FIXME Ty" in
                      (match uu____10918 with
                       | ((head_ml, (vars, t1)), qual) ->
                           let has_typ_apps =
                             match args with
                             | (a, uu____11034)::uu____11035 -> is_type g a
                             | uu____11062 -> false in
                           let uu____11073 =
                             let n = FStar_List.length vars in
                             let uu____11089 =
                               if (FStar_List.length args) <= n
                               then
                                 let uu____11126 =
                                   FStar_List.map
                                     (fun uu____11138 ->
                                        match uu____11138 with
                                        | (x, uu____11146) ->
                                            term_as_mlty g x) args in
                                 (uu____11126, [])
                               else
                                 (let uu____11168 = FStar_Util.first_N n args in
                                  match uu____11168 with
                                  | (prefix, rest) ->
                                      let uu____11257 =
                                        FStar_List.map
                                          (fun uu____11269 ->
                                             match uu____11269 with
                                             | (x, uu____11277) ->
                                                 term_as_mlty g x) prefix in
                                      (uu____11257, rest)) in
                             match uu____11089 with
                             | (provided_type_args, rest) ->
                                 let uu____11328 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu____11337 ->
                                       let uu____11338 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu____11338 with
                                        | (head2, uu____11350, t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu____11352 ->
                                       let uu____11353 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu____11353 with
                                        | (head2, uu____11365, t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head2,
                                        {
                                          FStar_Extraction_ML_Syntax.expr =
                                            FStar_Extraction_ML_Syntax.MLE_Const
                                            (FStar_Extraction_ML_Syntax.MLC_Unit);
                                          FStar_Extraction_ML_Syntax.mlty =
                                            uu____11368;
                                          FStar_Extraction_ML_Syntax.loc =
                                            uu____11369;_}::[])
                                       ->
                                       let uu____11372 =
                                         instantiate_maybe_partial g head2
                                           (vars, t1) provided_type_args in
                                       (match uu____11372 with
                                        | (head3, uu____11384, t2) ->
                                            let uu____11386 =
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head3,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2) in
                                            (uu____11386, t2))
                                   | uu____11389 ->
                                       failwith
                                         "Impossible: Unexpected head term" in
                                 (match uu____11328 with
                                  | (head2, t2) -> (head2, t2, rest)) in
                           (match uu____11073 with
                            | (head_ml1, head_t, args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11455 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1 in
                                     (uu____11455,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11456 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____11465 ->
                      let uu____11466 = term_as_mlexpr g head1 in
                      (match uu____11466 with
                       | (head2, f, t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head2 (f, t1) args) in
                let uu____11482 = is_type g t in
                if uu____11482
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____11490 =
                     let uu____11491 = FStar_Syntax_Util.un_uinst head in
                     uu____11491.FStar_Syntax_Syntax.n in
                   match uu____11490 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____11501 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv in
                       (match uu____11501 with
                        | FStar_Pervasives_Native.None ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____11510 -> extract_app_with_instantiations ())
                   | uu____11513 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____11516), f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____11581 =
                   let uu____11582 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                   maybe_reify_comp g uu____11582 c in
                 term_as_mlty g uu____11581 in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l in
           let uu____11585 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____11585 with | (e, t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e') when
           (let uu____11614 = FStar_Syntax_Syntax.is_top_level [lb] in
            Prims.op_Negation uu____11614) &&
             (let uu____11616 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs in
              FStar_Util.is_some uu____11616)
           ->
           let b =
             let uu____11626 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
             (uu____11626, FStar_Pervasives_Native.None) in
           let uu____11629 = FStar_Syntax_Subst.open_term_1 b e' in
           (match uu____11629 with
            | ((x, uu____11641), body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str, uu____11656)::[]) ->
                      let uu____11681 =
                        let uu____11682 = FStar_Syntax_Subst.compress str in
                        uu____11682.FStar_Syntax_Syntax.n in
                      (match uu____11681 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s, uu____11688)) ->
                           let id =
                             let uu____11690 =
                               let uu____11695 =
                                 FStar_Syntax_Syntax.range_of_bv x in
                               (s, uu____11695) in
                             FStar_Ident.mk_ident uu____11690 in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             } in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv in
                           FStar_Pervasives_Native.Some bv1
                       | uu____11698 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____11699 ->
                      (FStar_Errors.log_issue top1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `rename_let`");
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None in
                let remove_attr attrs =
                  let uu____11717 =
                    FStar_List.partition
                      (fun attr ->
                         let uu____11729 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr] in
                         FStar_Util.is_some uu____11729)
                      lb.FStar_Syntax_Syntax.lbattrs in
                  match uu____11717 with
                  | (uu____11734, other_attrs) -> other_attrs in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1774_11759 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1774_11759.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1774_11759.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1774_11759.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1774_11759.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1774_11759.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1774_11759.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs in
                      let rename =
                        let uu____11767 =
                          let uu____11768 =
                            let uu____11775 =
                              FStar_Syntax_Syntax.bv_to_name y in
                            (x, uu____11775) in
                          FStar_Syntax_Syntax.NT uu____11768 in
                        [uu____11767] in
                      let body1 =
                        let uu____11781 =
                          FStar_Syntax_Subst.subst rename body in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____11781 in
                      let lb1 =
                        let uu___1781_11797 = lb in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1781_11797.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1781_11797.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1781_11797.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1781_11797.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1781_11797.FStar_Syntax_Syntax.lbpos)
                        } in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1) in
                let top2 =
                  let uu___1785_11811 = top1 in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1785_11811.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1785_11811.FStar_Syntax_Syntax.vars)
                  } in
                term_as_mlexpr' g top2)
       | FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____11830 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____11844 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____11844
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____11856 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____11856 in
                   let lb1 =
                     let uu___1799_11858 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1799_11858.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1799_11858.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1799_11858.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1799_11858.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1799_11858.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1799_11858.FStar_Syntax_Syntax.lbpos)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e' in
                   ([lb1], e'1))) in
           (match uu____11830 with
            | (lbs1, e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____11880 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                      let uu____11881 =
                        let uu____11882 =
                          let uu____11883 =
                            let uu____11886 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g in
                            FStar_Pervasives_Native.fst uu____11886 in
                          let uu____11895 =
                            let uu____11898 =
                              let uu____11899 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g in
                              FStar_Pervasives_Native.snd uu____11899 in
                            [uu____11898] in
                          FStar_List.append uu____11883 uu____11895 in
                        FStar_Ident.lid_of_path uu____11882
                          FStar_Range.dummyRange in
                      FStar_TypeChecker_Env.set_current_module uu____11880
                        uu____11881 in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb ->
                            let lbdef =
                              let uu____11919 = FStar_Options.ml_ish () in
                              if uu____11919
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____11928 =
                                   let uu____11929 =
                                     let uu____11930 =
                                       let uu____11933 =
                                         extraction_norm_steps () in
                                       FStar_TypeChecker_Env.Reify ::
                                         uu____11933 in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____11930 in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____11929 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef in
                                 let uu____11936 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm")) in
                                 if uu____11936
                                 then
                                   ((let uu____11940 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____11940);
                                    (let a =
                                       let uu____11944 =
                                         let uu____11945 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____11945 in
                                       FStar_Util.measure_execution_time
                                         uu____11944 norm_call in
                                     (let uu____11949 =
                                        FStar_Syntax_Print.term_to_string a in
                                      FStar_Util.print1 "Normalized to %s\n"
                                        uu____11949);
                                     a))
                                 else norm_call ()) in
                            let uu___1817_11951 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1817_11951.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1817_11951.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1817_11951.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1817_11951.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1817_11951.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1817_11951.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1 in
                let check_lb env uu____12001 =
                  match uu____12001 with
                  | (nm, (_lbname, f, (_t, (targs, polytype)), add_unit, e))
                      ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1 ->
                             fun uu____12150 ->
                               match uu____12150 with
                               | (a, uu____12158) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     false) env targs in
                      let expected_t = FStar_Pervasives_Native.snd polytype in
                      let uu____12164 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____12164 with
                       | (e1, ty) ->
                           let uu____12175 =
                             maybe_promote_effect e1 f expected_t in
                           (match uu____12175 with
                            | (e2, f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE,
                                     FStar_Extraction_ML_Syntax.MLTY_Erased)
                                      -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST,
                                     FStar_Extraction_ML_Syntax.MLTY_Erased)
                                      -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____12187 -> [] in
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
                let uu____12215 =
                  FStar_List.fold_right
                    (fun lb ->
                       fun uu____12307 ->
                         match uu____12307 with
                         | (env, lbs4) ->
                             let uu____12432 = lb in
                             (match uu____12432 with
                              | (lbname, uu____12480,
                                 (t1, (uu____12482, polytype)), add_unit,
                                 uu____12485) ->
                                  let uu____12498 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit in
                                  (match uu____12498 with
                                   | (env1, nm, uu____12535) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, []) in
                (match uu____12215 with
                 | (env_body, lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____12792 = term_as_mlexpr env_body e'1 in
                     (match uu____12792 with
                      | (e'2, f', t') ->
                          let f =
                            let uu____12809 =
                              let uu____12812 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5 in
                              f' :: uu____12812 in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____12809 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____12821 =
                            let uu____12822 =
                              let uu____12823 =
                                let uu____12824 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5 in
                                (is_rec1, uu____12824) in
                              mk_MLE_Let top_level uu____12823 e'2 in
                            let uu____12833 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____12822 uu____12833 in
                          (uu____12821, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee, pats) ->
           let uu____12872 = term_as_mlexpr g scrutinee in
           (match uu____12872 with
            | (e, f_e, t_e) ->
                let uu____12888 = check_pats_for_ite pats in
                (match uu____12888 with
                 | (b, then_e, else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some then_e1,
                           FStar_Pervasives_Native.Some else_e1) ->
                            let uu____12949 = term_as_mlexpr g then_e1 in
                            (match uu____12949 with
                             | (then_mle, f_then, t_then) ->
                                 let uu____12965 = term_as_mlexpr g else_e1 in
                                 (match uu____12965 with
                                  | (else_mle, f_else, t_else) ->
                                      let uu____12981 =
                                        let uu____12992 =
                                          type_leq g t_then t_else in
                                        if uu____12992
                                        then (t_else, no_lift)
                                        else
                                          (let uu____13010 =
                                             type_leq g t_else t_then in
                                           if uu____13010
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____12981 with
                                       | (t_branch, maybe_lift) ->
                                           let uu____13054 =
                                             let uu____13055 =
                                               let uu____13056 =
                                                 let uu____13065 =
                                                   maybe_lift then_mle t_then in
                                                 let uu____13066 =
                                                   let uu____13069 =
                                                     maybe_lift else_mle
                                                       t_else in
                                                   FStar_Pervasives_Native.Some
                                                     uu____13069 in
                                                 (e, uu____13065,
                                                   uu____13066) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____13056 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____13055 in
                                           let uu____13072 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____13054, uu____13072,
                                             t_branch))))
                        | uu____13073 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____13089 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat ->
                                  fun br ->
                                    let uu____13184 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____13184 with
                                    | (pat, when_opt, branch) ->
                                        let uu____13228 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr in
                                        (match uu____13228 with
                                         | (env, p, pat_t_compat) ->
                                             let uu____13286 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let w_pos =
                                                     w.FStar_Syntax_Syntax.pos in
                                                   let uu____13309 =
                                                     term_as_mlexpr env w in
                                                   (match uu____13309 with
                                                    | (w1, f_w, t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w)) in
                                             (match uu____13286 with
                                              | (when_opt1, f_when) ->
                                                  let uu____13358 =
                                                    term_as_mlexpr env branch in
                                                  (match uu____13358 with
                                                   | (mlbranch, f_branch,
                                                      t_branch) ->
                                                       let uu____13392 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____13469
                                                                 ->
                                                                 match uu____13469
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
                                                         uu____13392)))))
                               true) in
                        match uu____13089 with
                        | (pat_t_compat, mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____13634 ->
                                      let uu____13635 =
                                        let uu____13636 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu____13636 e in
                                      let uu____13637 =
                                        let uu____13638 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu____13638 t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____13635 uu____13637);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____13663 =
                                   let uu____13664 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____13664 in
                                 (match uu____13663 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____13671;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____13673;_}
                                      ->
                                      let uu____13674 =
                                        let uu____13675 =
                                          let uu____13676 =
                                            let uu____13683 =
                                              let uu____13686 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____13686] in
                                            (fw, uu____13683) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____13676 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____13675 in
                                      (uu____13674,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____13689, uu____13690,
                                (uu____13691, f_first, t_first))::rest ->
                                 let uu____13751 =
                                   FStar_List.fold_left
                                     (fun uu____13793 ->
                                        fun uu____13794 ->
                                          match (uu____13793, uu____13794)
                                          with
                                          | ((topt, f),
                                             (uu____13851, uu____13852,
                                              (uu____13853, f_branch,
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
                                                    let uu____13909 =
                                                      type_leq g t1 t_branch in
                                                    if uu____13909
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____13913 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____13913
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           t1
                                                       else
                                                         FStar_Pervasives_Native.None) in
                                              (topt1, f1))
                                     ((FStar_Pervasives_Native.Some t_first),
                                       f_first) rest in
                                 (match uu____13751 with
                                  | (topt, f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____14008 ->
                                                match uu____14008 with
                                                | (p, (wopt, uu____14037),
                                                   (b1, uu____14039, t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____14058 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | FStar_Pervasives_Native.Some t1 ->
                                            t1 in
                                      let uu____14063 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____14063, f_match, t_match)))))))
let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env ->
    fun discName ->
      fun constrName ->
        let uu____14089 =
          let uu____14094 =
            let uu____14103 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
            FStar_TypeChecker_Env.lookup_lid uu____14103 discName in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____14094 in
        match uu____14089 with
        | (uu____14120, fstar_disc_type) ->
            let uu____14122 =
              let uu____14133 =
                let uu____14134 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____14134.FStar_Syntax_Syntax.n in
              match uu____14133 with
              | FStar_Syntax_Syntax.Tm_arrow (binders, uu____14148) ->
                  let binders1 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_14203 ->
                            match uu___2_14203 with
                            | (uu____14210, FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____14211)) ->
                                true
                            | uu____14214 -> false)) in
                  FStar_List.fold_right
                    (fun uu____14244 ->
                       fun uu____14245 ->
                         match uu____14245 with
                         | (g, vs) ->
                             let uu____14286 =
                               FStar_Extraction_ML_UEnv.new_mlident g in
                             (match uu____14286 with
                              | (g1, v) ->
                                  (g1,
                                    ((v, FStar_Extraction_ML_Syntax.MLTY_Top)
                                    :: vs)))) binders1 (env, [])
              | uu____14323 -> failwith "Discriminator must be a function" in
            (match uu____14122 with
             | (g, wildcards) ->
                 let uu____14348 = FStar_Extraction_ML_UEnv.new_mlident g in
                 (match uu____14348 with
                  | (g1, mlid) ->
                      let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
                      let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
                      let discrBody =
                        let uu____14358 =
                          let uu____14359 =
                            let uu____14370 =
                              let uu____14371 =
                                let uu____14372 =
                                  let uu____14387 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         targ)
                                      (FStar_Extraction_ML_Syntax.MLE_Name
                                         ([], mlid)) in
                                  let uu____14390 =
                                    let uu____14401 =
                                      let uu____14410 =
                                        let uu____14411 =
                                          let uu____14418 =
                                            FStar_Extraction_ML_UEnv.mlpath_of_lident
                                              g1 constrName in
                                          (uu____14418,
                                            [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                                        FStar_Extraction_ML_Syntax.MLP_CTor
                                          uu____14411 in
                                      let uu____14421 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_bool_ty)
                                          (FStar_Extraction_ML_Syntax.MLE_Const
                                             (FStar_Extraction_ML_Syntax.MLC_Bool
                                                true)) in
                                      (uu____14410,
                                        FStar_Pervasives_Native.None,
                                        uu____14421) in
                                    let uu____14424 =
                                      let uu____14435 =
                                        let uu____14444 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.ml_bool_ty)
                                            (FStar_Extraction_ML_Syntax.MLE_Const
                                               (FStar_Extraction_ML_Syntax.MLC_Bool
                                                  false)) in
                                        (FStar_Extraction_ML_Syntax.MLP_Wild,
                                          FStar_Pervasives_Native.None,
                                          uu____14444) in
                                      [uu____14435] in
                                    uu____14401 :: uu____14424 in
                                  (uu____14387, uu____14390) in
                                FStar_Extraction_ML_Syntax.MLE_Match
                                  uu____14372 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                uu____14371 in
                            ((FStar_List.append wildcards [(mlid, targ)]),
                              uu____14370) in
                          FStar_Extraction_ML_Syntax.MLE_Fun uu____14359 in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty disc_ty)
                          uu____14358 in
                      let uu____14499 =
                        FStar_Extraction_ML_UEnv.mlpath_of_lident env
                          discName in
                      (match uu____14499 with
                       | (uu____14500, name) ->
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