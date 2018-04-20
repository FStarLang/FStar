open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Un_extractable -> true | uu____4 -> false
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
let (erasableType :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g ->
    fun t ->
      FStar_Extraction_ML_Util.erasableType
        (FStar_Extraction_ML_Util.udelta_unfold g) t
let (eraseTypeDeep :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t ->
      FStar_Extraction_ML_Util.eraseTypeDeep
        (FStar_Extraction_ML_Util.udelta_unfold g) t
let record_fields :
  'Auu____50 .
    FStar_Ident.ident Prims.list ->
      'Auu____50 Prims.list ->
        (Prims.string, 'Auu____50) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs ->
    fun vs ->
      FStar_List.map2 (fun f -> fun e -> ((f.FStar_Ident.idText), e)) fs vs
let fail :
  'Auu____84 .
    FStar_Range.range ->
      (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2
        -> 'Auu____84
  = fun r -> fun err -> FStar_Errors.raise_error err r
let err_uninst :
  'Auu____106 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (Prims.string Prims.list, FStar_Extraction_ML_Syntax.mlty)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.term -> 'Auu____106
  =
  fun env ->
    fun t ->
      fun uu____127 ->
        fun app ->
          match uu____127 with
          | (vars, ty) ->
              let uu____141 =
                let uu____146 =
                  let uu____147 = FStar_Syntax_Print.term_to_string t in
                  let uu____148 =
                    FStar_All.pipe_right vars (FStar_String.concat ", ") in
                  let uu____151 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      env.FStar_Extraction_ML_UEnv.currentModule ty in
                  let uu____152 = FStar_Syntax_Print.term_to_string app in
                  FStar_Util.format4
                    "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                    uu____147 uu____148 uu____151 uu____152 in
                (FStar_Errors.Fatal_Uninstantiated, uu____146) in
              fail t.FStar_Syntax_Syntax.pos uu____141
let err_ill_typed_application :
  'Auu____159 'Auu____160 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term, 'Auu____159)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Extraction_ML_Syntax.mlty -> 'Auu____160
  =
  fun env ->
    fun t ->
      fun args ->
        fun ty ->
          let uu____189 =
            let uu____194 =
              let uu____195 = FStar_Syntax_Print.term_to_string t in
              let uu____196 =
                let uu____197 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____215 ->
                          match uu____215 with
                          | (x, uu____221) ->
                              FStar_Syntax_Print.term_to_string x)) in
                FStar_All.pipe_right uu____197 (FStar_String.concat " ") in
              let uu____224 =
                FStar_Extraction_ML_Code.string_of_mlty
                  env.FStar_Extraction_ML_UEnv.currentModule ty in
              FStar_Util.format3
                "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
                uu____195 uu____196 uu____224 in
            (FStar_Errors.Fatal_IllTyped, uu____194) in
          fail t.FStar_Syntax_Syntax.pos uu____189
let err_value_restriction :
  'Auu____227 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____227
  =
  fun t ->
    let uu____236 =
      let uu____241 =
        let uu____242 = FStar_Syntax_Print.tag_of_term t in
        let uu____243 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____242 uu____243 in
      (FStar_Errors.Fatal_ValueRestriction, uu____241) in
    fail t.FStar_Syntax_Syntax.pos uu____236
let err_unexpected_eff :
  'Auu____248 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.e_tag -> 'Auu____248
  =
  fun t ->
    fun f0 ->
      fun f1 ->
        let uu____265 =
          let uu____270 =
            let uu____271 = FStar_Syntax_Print.term_to_string t in
            let uu____272 = FStar_Extraction_ML_Util.eff_to_string f0 in
            let uu____273 = FStar_Extraction_ML_Util.eff_to_string f1 in
            FStar_Util.format3
              "for expression %s, Expected effect %s; got effect %s"
              uu____271 uu____272 uu____273 in
          (FStar_Errors.Fatal_UnexpectedEffect, uu____270) in
        fail t.FStar_Syntax_Syntax.pos uu____265
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  let rec delta_norm_eff g l =
    let uu____288 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
    match uu____288 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None ->
        let res =
          let uu____293 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l in
          match uu____293 with
          | FStar_Pervasives_Native.None -> l
          | FStar_Pervasives_Native.Some (uu____304, c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c) in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res) in
  fun g ->
    fun l ->
      let l1 = delta_norm_eff g l in
      if FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        if FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid
        then FStar_Extraction_ML_Syntax.E_GHOST
        else
          (let ed_opt =
             FStar_TypeChecker_Env.effect_decl_opt
               g.FStar_Extraction_ML_UEnv.tcenv l1 in
           match ed_opt with
           | FStar_Pervasives_Native.Some (ed, qualifiers) ->
               let uu____337 =
                 FStar_All.pipe_right qualifiers
                   (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
               if uu____337
               then FStar_Extraction_ML_Syntax.E_PURE
               else FStar_Extraction_ML_Syntax.E_IMPURE
           | FStar_Pervasives_Native.None ->
               FStar_Extraction_ML_Syntax.E_IMPURE)
let rec (is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____354 =
        let uu____355 = FStar_Syntax_Subst.compress t1 in
        uu____355.FStar_Syntax_Syntax.n in
      match uu____354 with
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____358 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____383 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____410 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____418 = FStar_Syntax_Util.unfold_lazy i in
          is_arity env uu____418
      | FStar_Syntax_Syntax.Tm_uvar uu____419 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____436 -> false
      | FStar_Syntax_Syntax.Tm_name uu____437 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____438 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____445 -> false
      | FStar_Syntax_Syntax.Tm_type uu____446 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____447, c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____465 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1 in
          let uu____467 =
            let uu____468 = FStar_Syntax_Subst.compress t2 in
            uu____468.FStar_Syntax_Syntax.n in
          (match uu____467 with
           | FStar_Syntax_Syntax.Tm_fvar uu____471 -> false
           | uu____472 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____473 ->
          let uu____488 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____488 with | (head1, uu____504) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1, uu____526) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x, uu____532) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____537, body, uu____539) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____560, body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____578, branches) ->
          (match branches with
           | (uu____616, uu____617, e)::uu____619 -> is_arity env e
           | uu____666 -> false)
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____690 ->
          let uu____715 =
            let uu____716 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____716 in
          failwith uu____715
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____717 =
            let uu____718 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____718 in
          failwith uu____717
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____720 = FStar_Syntax_Util.unfold_lazy i in
          is_type_aux env uu____720
      | FStar_Syntax_Syntax.Tm_constant uu____721 -> false
      | FStar_Syntax_Syntax.Tm_type uu____722 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____723 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____730 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar (uu____745, t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____771;
            FStar_Syntax_Syntax.index = uu____772;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____776;
            FStar_Syntax_Syntax.index = uu____777;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____782, uu____783) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____825) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____832) ->
          let uu____853 = FStar_Syntax_Subst.open_term bs body in
          (match uu____853 with | (uu____858, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
          let uu____875 =
            let uu____880 =
              let uu____881 = FStar_Syntax_Syntax.mk_binder x in [uu____881] in
            FStar_Syntax_Subst.open_term uu____880 body in
          (match uu____875 with | (uu____882, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____884, lbs), body) ->
          let uu____901 = FStar_Syntax_Subst.open_let_rec lbs body in
          (match uu____901 with | (uu____908, body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____914, branches) ->
          (match branches with
           | b::uu____953 ->
               let uu____998 = FStar_Syntax_Subst.open_branch b in
               (match uu____998 with
                | (uu____999, uu____1000, e) -> is_type_aux env e)
           | uu____1018 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1035 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2, uu____1043) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1, uu____1049) ->
          is_type_aux env head1
let (is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1080 ->
           let uu____1081 = FStar_Syntax_Print.tag_of_term t in
           let uu____1082 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1081
             uu____1082);
      (let b = is_type_aux env t in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1088 ->
            if b
            then
              let uu____1089 = FStar_Syntax_Print.term_to_string t in
              let uu____1090 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1089 uu____1090
            else
              (let uu____1092 = FStar_Syntax_Print.term_to_string t in
               let uu____1093 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1092 uu____1093));
       b)
let is_type_binder :
  'Auu____1097 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv, 'Auu____1097) FStar_Pervasives_Native.tuple2
        -> Prims.bool
  =
  fun env ->
    fun x ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1117 =
      let uu____1118 = FStar_Syntax_Subst.compress t in
      uu____1118.FStar_Syntax_Syntax.n in
    match uu____1117 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1121;
          FStar_Syntax_Syntax.fv_delta = uu____1122;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor);_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1123;
          FStar_Syntax_Syntax.fv_delta = uu____1124;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1125);_}
        -> true
    | uu____1132 -> false
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1136 =
      let uu____1137 = FStar_Syntax_Subst.compress t in
      uu____1137.FStar_Syntax_Syntax.n in
    match uu____1136 with
    | FStar_Syntax_Syntax.Tm_constant uu____1140 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1141 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1142 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1143 -> true
    | FStar_Syntax_Syntax.Tm_app (head1, args) ->
        let uu____1182 = is_constructor head1 in
        if uu____1182
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1198 ->
                  match uu____1198 with
                  | (te, uu____1204) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1, uu____1207) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____1213, uu____1214) ->
        is_fstar_value t1
    | uu____1255 -> false
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1259 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1260 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1261 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1262 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1273, exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1282, fields) ->
        FStar_Util.for_all
          (fun uu____1307 ->
             match uu____1307 with | (uu____1312, e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h, uu____1315) -> is_ml_value h
    | uu____1320 -> false
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x ->
    FStar_Util.incr c;
    (let uu____1433 =
       let uu____1434 = FStar_ST.op_Bang c in
       FStar_Util.string_of_int uu____1434 in
     Prims.strcat x uu____1433)
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0 ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1587 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____1589 = FStar_Syntax_Util.is_fun e' in
          if uu____1589
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 FStar_Pervasives_Native.None
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1595 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1595
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
      (let uu____1673 = FStar_List.hd l in
       match uu____1673 with
       | (p1, w1, e1) ->
           let uu____1707 =
             let uu____1716 = FStar_List.tl l in FStar_List.hd uu____1716 in
           (match uu____1707 with
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
                 | uu____1790 -> def)))
let (instantiate :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  = fun s -> fun args -> FStar_Extraction_ML_Util.subst s args
let (erasable :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g ->
    fun f ->
      fun t ->
        (f = FStar_Extraction_ML_Syntax.E_GHOST) ||
          ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))
let (erase :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.e_tag ->
          (FStar_Extraction_ML_Syntax.mlexpr,
            FStar_Extraction_ML_Syntax.e_tag,
            FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g ->
    fun e ->
      fun ty ->
        fun f ->
          let e1 =
            let uu____1847 = erasable g f ty in
            if uu____1847
            then
              let uu____1848 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
              (if uu____1848
               then FStar_Extraction_ML_Syntax.ml_unit
               else
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            else e in
          (e1, f, ty)
let (eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun t ->
    fun e ->
      let uu____1857 = FStar_Extraction_ML_Util.doms_and_cod t in
      match uu____1857 with
      | (ts, r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1877 -> fresh "a") ts in
             let vs_ts = FStar_List.zip vs ts in
             let vs_es =
               let uu____1888 = FStar_List.zip vs ts in
               FStar_List.map
                 (fun uu____1902 ->
                    match uu____1902 with
                    | (v1, t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1888 in
             let body =
               FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r)
                 (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es)) in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect ->
    fun e ->
      let uu____1924 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____1926 = FStar_Options.codegen () in
           uu____1926 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin)) in
      if uu____1924 then e else eta_expand expect e
let (maybe_coerce :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun e ->
      fun ty ->
        fun expect ->
          let ty1 = eraseTypeDeep g ty in
          let uu____1945 =
            type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect in
          match uu____1945 with
          | (true, FStar_Pervasives_Native.Some e') -> e'
          | uu____1955 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1967 ->
                    let uu____1968 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let uu____1969 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                    let uu____1970 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1968 uu____1969 uu____1970);
               (let uu____1971 =
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty expect)
                    (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)) in
                maybe_eta_expand expect uu____1971))
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun bv ->
      let uu____1978 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1978 with
      | FStar_Util.Inl (uu____1979, t) -> t
      | uu____1993 -> FStar_Extraction_ML_Syntax.MLTY_Top
let rec (term_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t0 ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____2036 ->
            let uu____2043 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____2043 with
             | FStar_Pervasives_Native.None -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____2047 -> false in
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.Iota;
          FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]
          g.FStar_Extraction_ML_UEnv.tcenv t0 in
      let mlt = term_as_mlty' g t in
      let uu____2050 = is_top_ty mlt in
      if uu____2050
      then
        let t1 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.Delta_constant;
            FStar_TypeChecker_Normalize.Iota;
            FStar_TypeChecker_Normalize.Zeta;
            FStar_TypeChecker_Normalize.Inlining;
            FStar_TypeChecker_Normalize.EraseUniverses;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses]
            g.FStar_Extraction_ML_UEnv.tcenv t0 in
        term_as_mlty' g t1
      else mlt
and (term_as_mlty' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar uu____2056 ->
          let uu____2057 =
            let uu____2058 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2058 in
          failwith uu____2057
      | FStar_Syntax_Syntax.Tm_delayed uu____2059 ->
          let uu____2084 =
            let uu____2085 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2085 in
          failwith uu____2084
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____2086 =
            let uu____2087 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2087 in
          failwith uu____2086
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____2089 = FStar_Syntax_Util.unfold_lazy i in
          term_as_mlty' env uu____2089
      | FStar_Syntax_Syntax.Tm_constant uu____2090 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_quoted uu____2091 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____2098 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2, uu____2116) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____2121;
             FStar_Syntax_Syntax.index = uu____2122;
             FStar_Syntax_Syntax.sort = t2;_},
           uu____2124)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____2132) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____2138, uu____2139) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____2206 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____2206 with
           | (bs1, c1) ->
               let uu____2213 = binders_as_ml_binders env bs1 in
               (match uu____2213 with
                | (mlbs, env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____2240 =
                        let uu____2247 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff in
                        FStar_Util.must uu____2247 in
                      match uu____2240 with
                      | (ed, qualifiers) ->
                          let uu____2268 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable) in
                          if uu____2268
                          then
                            let t2 =
                              FStar_TypeChecker_Env.reify_comp
                                env1.FStar_Extraction_ML_UEnv.tcenv c1
                                FStar_Syntax_Syntax.U_unknown in
                            let res = term_as_mlty' env1 t2 in res
                          else
                            term_as_mlty' env1
                              (FStar_Syntax_Util.comp_result c1) in
                    let erase1 =
                      effect_as_etag env1
                        (FStar_Syntax_Util.comp_effect_name c1) in
                    let uu____2275 =
                      FStar_List.fold_right
                        (fun uu____2294 ->
                           fun uu____2295 ->
                             match (uu____2294, uu____2295) with
                             | ((uu____2316, t2), (tag, t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret) in
                    (match uu____2275 with | (uu____2328, t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1, args) ->
          let res =
            let uu____2353 =
              let uu____2354 = FStar_Syntax_Util.un_uinst head1 in
              uu____2354.FStar_Syntax_Syntax.n in
            match uu____2353 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2, args') ->
                let uu____2381 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args)))
                    FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
                term_as_mlty' env uu____2381
            | uu____2398 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____2401) ->
          let uu____2422 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____2422 with
           | (bs1, ty1) ->
               let uu____2429 = binders_as_ml_binders env bs1 in
               (match uu____2429 with | (bts, env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____2454 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____2455 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____2468 ->
          FStar_Extraction_ML_UEnv.unknownType
and (arg_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun uu____2492 ->
      match uu____2492 with
      | (a, uu____2498) ->
          let uu____2499 = is_type g a in
          if uu____2499
          then term_as_mlty' g a
          else FStar_Extraction_ML_UEnv.erasedContent
and (fv_app_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.args -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun fv ->
      fun args ->
        let uu____2504 =
          let uu____2517 =
            FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____2517 with
          | ((uu____2538, fvty), uu____2540) ->
              let fvty1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant]
                  g.FStar_Extraction_ML_UEnv.tcenv fvty in
              FStar_Syntax_Util.arrow_formals fvty1 in
        match uu____2504 with
        | (formals, uu____2547) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs1 =
              let n_args = FStar_List.length args in
              if (FStar_List.length formals) > n_args
              then
                let uu____2591 = FStar_Util.first_N n_args formals in
                match uu____2591 with
                | (uu____2618, rest) ->
                    let uu____2644 =
                      FStar_List.map
                        (fun uu____2652 ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest in
                    FStar_List.append mlargs uu____2644
              else mlargs in
            let nm =
              let uu____2659 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____2659 with
              | FStar_Pervasives_Native.Some p -> p
              | FStar_Pervasives_Native.None ->
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)
and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident, FStar_Extraction_ML_Syntax.mlty)
         FStar_Pervasives_Native.tuple2 Prims.list,
        FStar_Extraction_ML_UEnv.env) FStar_Pervasives_Native.tuple2)
  =
  fun g ->
    fun bs ->
      let uu____2677 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2720 ->
                fun b ->
                  match uu____2720 with
                  | (ml_bs, env) ->
                      let uu____2760 = is_type_binder g b in
                      if uu____2760
                      then
                        let b1 = FStar_Pervasives_Native.fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____2778 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____2778, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort in
                         let uu____2792 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____2792 with
                         | (env1, b2) ->
                             let ml_b =
                               let uu____2816 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____2816, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____2677 with | (ml_bs, env) -> ((FStar_List.rev ml_bs), env)
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1, uu____2884) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____2887, FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____2891 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
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
                    | uu____2919 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____2920 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____2921 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____2924 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q ->
    fun p ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) ->
          let uu____2941 = FStar_Extraction_ML_Util.is_xtuple d in
          (match uu____2941 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____2945 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty, fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____2972 -> p))
      | uu____2975 -> p
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
                       (fun uu____3055 ->
                          let uu____3056 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t' in
                          let uu____3057 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____3056 uu____3057)
                   else ();
                   ok) in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c, swopt)) when
                let uu____3087 = FStar_Options.codegen () in
                uu____3087 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____3092 =
                  match swopt with
                  | FStar_Pervasives_Native.None ->
                      let uu____3105 =
                        let uu____3106 =
                          let uu____3107 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None)) in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____3107 in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____3106 in
                      (uu____3105, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange in
                      let uu____3128 = term_as_mlexpr g source_term in
                      (match uu____3128 with
                       | (mlterm, uu____3140, mlty) -> (mlterm, mlty)) in
                (match uu____3092 with
                 | (mlc, ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym () in
                     let when_clause =
                       let uu____3160 =
                         let uu____3161 =
                           let uu____3168 =
                             let uu____3171 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x) in
                             [uu____3171; mlc] in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____3168) in
                         FStar_Extraction_ML_Syntax.MLE_App uu____3161 in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3160 in
                     let uu____3174 = ok ml_ty in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____3174))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s in
                let mlty = term_as_mlty g t in
                let uu____3194 =
                  let uu____3203 =
                    let uu____3210 =
                      let uu____3211 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____3211 in
                    (uu____3210, []) in
                  FStar_Pervasives_Native.Some uu____3203 in
                let uu____3220 = ok mlty in (g, uu____3194, uu____3220)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____3231 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                (match uu____3231 with
                 | (g1, x1) ->
                     let uu____3254 = ok mlty in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3254))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
                let uu____3288 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp in
                (match uu____3288 with
                 | (g1, x1) ->
                     let uu____3311 = ok mlty in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3311))
            | FStar_Syntax_Syntax.Pat_dot_term uu____3343 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f, pats) ->
                let uu____3382 =
                  let uu____3387 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                  match uu____3387 with
                  | FStar_Util.Inr
                      (uu____3392,
                       {
                         FStar_Extraction_ML_Syntax.expr =
                           FStar_Extraction_ML_Syntax.MLE_Name n1;
                         FStar_Extraction_ML_Syntax.mlty = uu____3394;
                         FStar_Extraction_ML_Syntax.loc = uu____3395;_},
                       ttys, uu____3397)
                      -> (n1, ttys)
                  | uu____3410 -> failwith "Expected a constructor" in
                (match uu____3382 with
                 | (d, tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys) in
                     let uu____3432 = FStar_Util.first_N nTyVars pats in
                     (match uu____3432 with
                      | (tysVarPats, restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____3565 ->
                                        match uu____3565 with
                                        | (p1, uu____3573) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____3578, t) ->
                                                 term_as_mlty g t
                                             | uu____3584 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____3588 ->
                                                       let uu____3589 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1 in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____3589);
                                                  FStar_Exn.raise
                                                    Un_extractable)))) in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args in
                              let uu____3591 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty in
                              FStar_Pervasives_Native.Some uu____3591
                            with
                            | Un_extractable -> FStar_Pervasives_Native.None in
                          let uu____3620 =
                            FStar_Util.fold_map
                              (fun g1 ->
                                 fun uu____3656 ->
                                   match uu____3656 with
                                   | (p1, imp1) ->
                                       let uu____3675 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr in
                                       (match uu____3675 with
                                        | (g2, p2, uu____3704) -> (g2, p2)))
                              g tysVarPats in
                          (match uu____3620 with
                           | (g1, tyMLPats) ->
                               let uu____3765 =
                                 FStar_Util.fold_map
                                   (fun uu____3829 ->
                                      fun uu____3830 ->
                                        match (uu____3829, uu____3830) with
                                        | ((g2, f_ty_opt1), (p1, imp1)) ->
                                            let uu____3923 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest, res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____3983 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None) in
                                            (match uu____3923 with
                                             | (f_ty_opt2, expected_ty) ->
                                                 let uu____4054 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr in
                                                 (match uu____4054 with
                                                  | (g3, p2, uu____4095) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats in
                               (match uu____3765 with
                                | ((g2, f_ty_opt1), restMLPats) ->
                                    let uu____4213 =
                                      let uu____4224 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___61_4275 ->
                                                match uu___61_4275 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____4317 -> [])) in
                                      FStar_All.pipe_right uu____4224
                                        FStar_List.split in
                                    (match uu____4213 with
                                     | (mlPats, when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([], t) -> ok t
                                           | uu____4390 -> false in
                                         let uu____4399 =
                                           let uu____4408 =
                                             let uu____4415 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats)) in
                                             let uu____4418 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten in
                                             (uu____4415, uu____4418) in
                                           FStar_Pervasives_Native.Some
                                             uu____4408 in
                                         (g2, uu____4399, pat_ty_compat))))))
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
            let uu____4531 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr in
            match uu____4531 with
            | (g2, FStar_Pervasives_Native.Some (x, v1), b) ->
                (g2, (x, v1), b)
            | uu____4588 ->
                failwith "Impossible: Unable to translate pattern" in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____4631 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1 in
                FStar_Pervasives_Native.Some uu____4631 in
          let uu____4632 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t) in
          match uu____4632 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____4770, t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____4773 =
                  let uu____4784 =
                    let uu____4793 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____4793) in
                  uu____4784 :: more_args in
                eta_args uu____4773 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4806, uu____4807)
                -> ((FStar_List.rev more_args), t)
            | uu____4830 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu____4858, args),
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
               (tyname, fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____4890 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____4908 = eta_args [] residualType in
            match uu____4908 with
            | (eargs, tres) ->
                (match eargs with
                 | [] ->
                     let uu____4961 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____4961
                 | uu____4962 ->
                     let uu____4973 = FStar_List.unzip eargs in
                     (match uu____4973 with
                      | (binders, eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor
                               (head1, args) ->
                               let body =
                                 let uu____5015 =
                                   let uu____5016 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____5016 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____5015 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____5025 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____5028, FStar_Pervasives_Native.None) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5032;
                FStar_Extraction_ML_Syntax.loc = uu____5033;_},
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
                | uu____5060 ->
                    let uu____5063 =
                      let uu____5070 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____5070, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5063 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5074;
                     FStar_Extraction_ML_Syntax.loc = uu____5075;_},
                   uu____5076);
                FStar_Extraction_ML_Syntax.mlty = uu____5077;
                FStar_Extraction_ML_Syntax.loc = uu____5078;_},
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
                | uu____5109 ->
                    let uu____5112 =
                      let uu____5119 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____5119, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5112 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5123;
                FStar_Extraction_ML_Syntax.loc = uu____5124;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____5132 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5132
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5136;
                FStar_Extraction_ML_Syntax.loc = uu____5137;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____5139)) ->
              let uu____5152 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5152
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5156;
                     FStar_Extraction_ML_Syntax.loc = uu____5157;_},
                   uu____5158);
                FStar_Extraction_ML_Syntax.mlty = uu____5159;
                FStar_Extraction_ML_Syntax.loc = uu____5160;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____5172 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5172
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5176;
                     FStar_Extraction_ML_Syntax.loc = uu____5177;_},
                   uu____5178);
                FStar_Extraction_ML_Syntax.mlty = uu____5179;
                FStar_Extraction_ML_Syntax.loc = uu____5180;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____5182)) ->
              let uu____5199 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5199
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____5205 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5205
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____5209)) ->
              let uu____5218 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5218
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5222;
                FStar_Extraction_ML_Syntax.loc = uu____5223;_},
              uu____5224),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu____5231 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5231
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5235;
                FStar_Extraction_ML_Syntax.loc = uu____5236;_},
              uu____5237),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu____5238)) ->
              let uu____5251 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5251
          | uu____5254 -> mlAppExpr
let (maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag)
  =
  fun g ->
    fun f ->
      fun t ->
        let rec non_informative1 t1 =
          let uu____5274 =
            (type_leq g t1 FStar_Extraction_ML_Syntax.ml_unit_ty) ||
              (erasableType g t1) in
          if uu____5274
          then true
          else
            (match t1 with
             | FStar_Extraction_ML_Syntax.MLTY_Fun
                 (uu____5276, FStar_Extraction_ML_Syntax.E_PURE, t2) ->
                 non_informative1 t2
             | FStar_Extraction_ML_Syntax.MLTY_Fun
                 (uu____5278, FStar_Extraction_ML_Syntax.E_GHOST, t2) ->
                 non_informative1 t2
             | uu____5280 -> false) in
        let uu____5281 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) && (non_informative1 t) in
        if uu____5281 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr, FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g ->
    fun t ->
      let uu____5335 = term_as_mlexpr' g t in
      match uu____5335 with
      | (e, tag, ty) ->
          let tag1 = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u ->
                let uu____5356 =
                  let uu____5357 = FStar_Syntax_Print.tag_of_term t in
                  let uu____5358 = FStar_Syntax_Print.term_to_string t in
                  let uu____5359 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty in
                  let uu____5360 =
                    FStar_Extraction_ML_Util.eff_to_string tag1 in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____5357 uu____5358 uu____5359 uu____5360 in
                FStar_Util.print_string uu____5356);
           erase g e ty tag1)
and (check_term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,
            FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple2)
  =
  fun g ->
    fun t ->
      fun f ->
        fun ty ->
          let uu____5369 = check_term_as_mlexpr' g t f ty in
          match uu____5369 with
          | (e, t1) ->
              let uu____5380 = erase g e t1 f in
              (match uu____5380 with | (r, uu____5392, t2) -> (r, t2))
and (check_term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,
            FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple2)
  =
  fun g ->
    fun e0 ->
      fun f ->
        fun ty ->
          let uu____5402 = term_as_mlexpr g e0 in
          match uu____5402 with
          | (e, tag, t) ->
              let tag1 = maybe_downgrade_eff g tag t in
              let uu____5417 = FStar_Extraction_ML_Util.eff_leq tag1 f in
              if uu____5417
              then let uu____5422 = maybe_coerce g e t ty in (uu____5422, ty)
              else err_unexpected_eff e0 f tag1
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
           let uu____5440 =
             let uu____5441 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____5442 = FStar_Syntax_Print.tag_of_term top in
             let uu____5443 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5441 uu____5442 uu____5443 in
           FStar_Util.print_string uu____5440);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu____5451 =
             let uu____5452 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5452 in
           failwith uu____5451
       | FStar_Syntax_Syntax.Tm_delayed uu____5459 ->
           let uu____5484 =
             let uu____5485 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5485 in
           failwith uu____5484
       | FStar_Syntax_Syntax.Tm_uvar uu____5492 ->
           let uu____5509 =
             let uu____5510 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5510 in
           failwith uu____5509
       | FStar_Syntax_Syntax.Tm_bvar uu____5517 ->
           let uu____5518 =
             let uu____5519 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5519 in
           failwith uu____5518
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____5527 = FStar_Syntax_Util.unfold_lazy i in
           term_as_mlexpr' g uu____5527
       | FStar_Syntax_Syntax.Tm_type uu____5528 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5529 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5536 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
              FStar_Syntax_Syntax.antiquotes = uu____5550;_})
           ->
           let uu____5565 =
             let uu____5574 =
               let uu____5591 =
                 FStar_Syntax_Syntax.lid_as_fv
                   FStar_Parser_Const.failwith_lid
                   FStar_Syntax_Syntax.Delta_constant
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.lookup_fv g uu____5591 in
             FStar_All.pipe_left FStar_Util.right uu____5574 in
           (match uu____5565 with
            | (uu____5634, fw, uu____5636, uu____5637) ->
                let uu____5638 =
                  let uu____5639 =
                    let uu____5640 =
                      let uu____5647 =
                        let uu____5650 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Open quotation at runtime")) in
                        [uu____5650] in
                      (fw, uu____5647) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5640 in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____5639 in
                (uu____5638, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
              FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____5669 = FStar_Reflection_Basic.inspect_ln qt in
           (match uu____5669 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____5677 = FStar_Syntax_Syntax.lookup_aq bv aqs in
                (match uu____5677 with
                 | FStar_Pervasives_Native.Some (false, tm) ->
                     term_as_mlexpr' g tm
                 | FStar_Pervasives_Native.Some (true, tm) ->
                     let uu____5700 =
                       let uu____5709 =
                         let uu____5726 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.failwith_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None in
                         FStar_Extraction_ML_UEnv.lookup_fv g uu____5726 in
                       FStar_All.pipe_left FStar_Util.right uu____5709 in
                     (match uu____5700 with
                      | (uu____5769, fw, uu____5771, uu____5772) ->
                          let uu____5773 =
                            let uu____5774 =
                              let uu____5775 =
                                let uu____5782 =
                                  let uu____5785 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         FStar_Extraction_ML_Syntax.ml_string_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_String
                                            "Open quotation at runtime")) in
                                  [uu____5785] in
                                (fw, uu____5782) in
                              FStar_Extraction_ML_Syntax.MLE_App uu____5775 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____5774 in
                          (uu____5773, FStar_Extraction_ML_Syntax.E_PURE,
                            FStar_Extraction_ML_Syntax.ml_int_ty))
                 | FStar_Pervasives_Native.None ->
                     let tv =
                       let uu____5793 =
                         FStar_Reflection_Embeddings.embed_term_view_aq aqs in
                       uu____5793 t.FStar_Syntax_Syntax.pos
                         (FStar_Reflection_Data.Tv_Var bv) in
                     let t1 =
                       let uu____5802 =
                         let uu____5811 = FStar_Syntax_Syntax.as_arg tv in
                         [uu____5811] in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____5802 in
                     term_as_mlexpr' g t1)
            | tv ->
                let tv1 =
                  let uu____5814 =
                    FStar_Reflection_Embeddings.embed_term_view_aq aqs in
                  uu____5814 t.FStar_Syntax_Syntax.pos tv in
                let t1 =
                  let uu____5823 =
                    let uu____5832 = FStar_Syntax_Syntax.as_arg tv1 in
                    [uu____5832] in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____5823 in
                term_as_mlexpr' g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1, FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc))
           ->
           FStar_Errors.raise_err
             (FStar_Errors.Error_NoLetMutable,
               "let-mutable no longer supported")
       | FStar_Syntax_Syntax.Tm_meta
           (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____5846)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____5876 =
                  let uu____5883 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m in
                  FStar_Util.must uu____5883 in
                (match uu____5876 with
                 | (ed, qualifiers) ->
                     let uu____5910 =
                       let uu____5911 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                       FStar_All.pipe_right uu____5911 Prims.op_Negation in
                     if uu____5910
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____5927 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1, uu____5929) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1, uu____5935) ->
           term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____5941 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____5941 with
            | (uu____5954, ty, uu____5956) ->
                let ml_ty = term_as_mlty g ty in
                let uu____5958 =
                  let uu____5959 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5959 in
                (uu____5958, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____5960 ->
           let uu____5961 = is_type g t in
           if uu____5961
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5969 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____5969 with
              | (FStar_Util.Inl uu____5982, uu____5983) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____6020, x, mltys, uu____6023), qual) ->
                  (match mltys with
                   | ([], t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([], t1) ->
                       let uu____6069 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____6069, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6070 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____6077 ->
           let uu____6078 = is_type g t in
           if uu____6078
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6086 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____6086 with
              | (FStar_Util.Inl uu____6099, uu____6100) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____6137, x, mltys, uu____6140), qual) ->
                  (match mltys with
                   | ([], t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([], t1) ->
                       let uu____6186 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____6186, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6187 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs, body, copt) ->
           let uu____6217 = FStar_Syntax_Subst.open_term bs body in
           (match uu____6217 with
            | (bs1, body1) ->
                let uu____6230 = binders_as_ml_binders g bs1 in
                (match uu____6230 with
                 | (ml_bs, env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____6263 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c in
                           if uu____6263
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____6268 ->
                                 let uu____6269 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____6269);
                            body1) in
                     let uu____6270 = term_as_mlexpr env body2 in
                     (match uu____6270 with
                      | (ml_body, f, t1) ->
                          let uu____6286 =
                            FStar_List.fold_right
                              (fun uu____6305 ->
                                 fun uu____6306 ->
                                   match (uu____6305, uu____6306) with
                                   | ((uu____6327, targ), (f1, t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____6286 with
                           | (f1, tfun) ->
                               let uu____6347 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____6347, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of);
              FStar_Syntax_Syntax.pos = uu____6354;
              FStar_Syntax_Syntax.vars = uu____6355;_},
            (a1, uu____6357)::[])
           ->
           let ty =
             let uu____6387 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
             term_as_mlty g uu____6387 in
           let uu____6388 =
             let uu____6389 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____6389 in
           (uu____6388, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of);
              FStar_Syntax_Syntax.pos = uu____6390;
              FStar_Syntax_Syntax.vars = uu____6391;_},
            (t1, uu____6393)::(r, uu____6395)::[])
           -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6434);
              FStar_Syntax_Syntax.pos = uu____6435;
              FStar_Syntax_Syntax.vars = uu____6436;_},
            uu____6437)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1, args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___62_6493 ->
                        match uu___62_6493 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | uu____6494 -> false))) in
           let uu____6495 =
             let uu____6500 =
               let uu____6501 = FStar_Syntax_Subst.compress head1 in
               uu____6501.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____6500) in
           (match uu____6495 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6510, uu____6511) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____6529, FStar_Syntax_Syntax.Tm_abs
               (bs, uu____6531, FStar_Pervasives_Native.Some rc)) when
                is_total rc ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____6552, FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify)) ->
                let e =
                  let uu____6554 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6554 in
                let tm =
                  let uu____6564 =
                    let uu____6565 = FStar_TypeChecker_Util.remove_reify e in
                    let uu____6566 = FStar_List.tl args in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6565 uu____6566 in
                  uu____6564 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr' g tm
            | uu____6575 ->
                let rec extract_app is_data uu____6620 uu____6621 restArgs =
                  match (uu____6620, uu____6621) with
                  | ((mlhead, mlargs_f), (f, t1)) ->
                      (match (restArgs, t1) with
                       | ([], uu____6711) ->
                           let evaluation_order_guaranteed =
                             (((FStar_List.length mlargs_f) =
                                 (Prims.parse_int "1"))
                                ||
                                (FStar_Extraction_ML_Util.codegen_fsharp ()))
                               ||
                               (match head1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_fvar fv ->
                                    (FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.op_And)
                                      ||
                                      (FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.op_Or)
                                | uu____6733 -> false) in
                           let uu____6734 =
                             if evaluation_order_guaranteed
                             then
                               let uu____6759 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ([], uu____6759)
                             else
                               FStar_List.fold_left
                                 (fun uu____6813 ->
                                    fun uu____6814 ->
                                      match (uu____6813, uu____6814) with
                                      | ((lbs, out_args), (arg, f1)) ->
                                          if
                                            (f1 =
                                               FStar_Extraction_ML_Syntax.E_PURE)
                                              ||
                                              (f1 =
                                                 FStar_Extraction_ML_Syntax.E_GHOST)
                                          then (lbs, (arg :: out_args))
                                          else
                                            (let x =
                                               FStar_Extraction_ML_Syntax.gensym
                                                 () in
                                             let uu____6917 =
                                               let uu____6920 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x) in
                                               uu____6920 :: out_args in
                                             (((x, arg) :: lbs), uu____6917)))
                                 ([], []) mlargs_f in
                           (match uu____6734 with
                            | (lbs, mlargs) ->
                                let app =
                                  let uu____6970 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____6970 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____6982 ->
                                       fun out ->
                                         match uu____6982 with
                                         | (x, arg) ->
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  out.FStar_Extraction_ML_Syntax.mlty)
                                               (mk_MLE_Let false
                                                  (FStar_Extraction_ML_Syntax.NonRec,
                                                    [{
                                                       FStar_Extraction_ML_Syntax.mllb_name
                                                         = x;
                                                       FStar_Extraction_ML_Syntax.mllb_tysc
                                                         =
                                                         (FStar_Pervasives_Native.Some
                                                            ([],
                                                              (arg.FStar_Extraction_ML_Syntax.mlty)));
                                                       FStar_Extraction_ML_Syntax.mllb_add_unit
                                                         = false;
                                                       FStar_Extraction_ML_Syntax.mllb_def
                                                         = arg;
                                                       FStar_Extraction_ML_Syntax.mllb_meta
                                                         = [];
                                                       FStar_Extraction_ML_Syntax.print_typ
                                                         = true
                                                     }]) out)) lbs app in
                                (l_app, f, t1))
                       | ((arg, uu____7001)::rest,
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t, f', t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____7032 =
                             let uu____7037 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f' in
                             (uu____7037, t2) in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____7032 rest
                       | ((e0, uu____7049)::rest,
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected, f', t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____7081 = term_as_mlexpr g e0 in
                           (match uu____7081 with
                            | (e01, f0, tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected in
                                let uu____7098 =
                                  let uu____7103 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (uu____7103, t2) in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____7098 rest)
                       | uu____7114 ->
                           let uu____7127 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1 in
                           (match uu____7127 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None ->
                                err_ill_typed_application g top restArgs t1)) in
                let extract_app_maybe_projector is_data mlhead uu____7184
                  args1 =
                  match uu____7184 with
                  | (f, t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____7216)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0, FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____7294))::args3,
                                FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____7296, f', t3)) ->
                                 let uu____7333 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____7333 t3
                             | uu____7334 -> (args2, f1, t2) in
                           let uu____7359 = remove_implicits args1 f t1 in
                           (match uu____7359 with
                            | (args2, f1, t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____7415 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let uu____7428 = is_type g t in
                if uu____7428
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1 in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_name uu____7443 ->
                       let uu____7444 =
                         let uu____7457 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____7457 with
                         | (FStar_Util.Inr (uu____7476, x1, x2, x3), q) ->
                             ((x1, x2, x3), q)
                         | uu____7521 -> failwith "FIXME Ty" in
                       (match uu____7444 with
                        | ((head_ml, (vars, t1), inst_ok), qual) ->
                            let has_typ_apps =
                              match args with
                              | (a, uu____7571)::uu____7572 -> is_type g a
                              | uu____7591 -> false in
                            let uu____7600 =
                              match vars with
                              | uu____7629::uu____7630 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7641 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7669 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____7669 with
                                     | (prefix1, rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7758 ->
                                                match uu____7758 with
                                                | (x, uu____7764) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____7777 ->
                                               let uu___66_7780 = e in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___66_7780.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___66_7780.FStar_Extraction_ML_Syntax.loc)
                                               } in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7784 ->
                                               let uu___67_7785 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___67_7785.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___67_7785.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7786 ->
                                               let uu___67_7787 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___67_7787.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___67_7787.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    FStar_Extraction_ML_Syntax.MLE_Const
                                                    (FStar_Extraction_ML_Syntax.MLC_Unit);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = uu____7789;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    = uu____7790;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___68_7796 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___68_7796.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___68_7796.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7797 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____7600 with
                             | (head_ml1, head_t, args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7858 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____7858,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7859 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____7868 ->
                       let uu____7869 =
                         let uu____7882 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____7882 with
                         | (FStar_Util.Inr (uu____7901, x1, x2, x3), q) ->
                             ((x1, x2, x3), q)
                         | uu____7946 -> failwith "FIXME Ty" in
                       (match uu____7869 with
                        | ((head_ml, (vars, t1), inst_ok), qual) ->
                            let has_typ_apps =
                              match args with
                              | (a, uu____7996)::uu____7997 -> is_type g a
                              | uu____8016 -> false in
                            let uu____8025 =
                              match vars with
                              | uu____8054::uu____8055 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____8066 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____8094 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____8094 with
                                     | (prefix1, rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____8183 ->
                                                match uu____8183 with
                                                | (x, uu____8189) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let mk_tapp e ty_args =
                                           match ty_args with
                                           | [] -> e
                                           | uu____8202 ->
                                               let uu___66_8205 = e in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (FStar_Extraction_ML_Syntax.MLE_TApp
                                                      (e, ty_args));
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   =
                                                   (uu___66_8205.FStar_Extraction_ML_Syntax.mlty);
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___66_8205.FStar_Extraction_ML_Syntax.loc)
                                               } in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____8209 ->
                                               let uu___67_8210 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___67_8210.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___67_8210.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____8211 ->
                                               let uu___67_8212 =
                                                 mk_tapp head_ml
                                                   prefixAsMLTypes in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___67_8212.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___67_8212.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,
                                                {
                                                  FStar_Extraction_ML_Syntax.expr
                                                    =
                                                    FStar_Extraction_ML_Syntax.MLE_Const
                                                    (FStar_Extraction_ML_Syntax.MLC_Unit);
                                                  FStar_Extraction_ML_Syntax.mlty
                                                    = uu____8214;
                                                  FStar_Extraction_ML_Syntax.loc
                                                    = uu____8215;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___68_8221 =
                                                        mk_tapp head3
                                                          prefixAsMLTypes in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___68_8221.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___68_8221.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____8222 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____8025 with
                             | (head_ml1, head_t, args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____8283 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____8283,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____8284 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____8293 ->
                       let uu____8294 = term_as_mlexpr g head2 in
                       (match uu____8294 with
                        | (head3, f, t1) ->
                            extract_app_maybe_projector
                              FStar_Pervasives_Native.None head3 (f, t1) args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____8312), f) ->
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
           let uu____8379 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____8379 with | (e, t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____8410 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8424 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____8424
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____8438 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____8438 in
                   let lb1 =
                     let uu___69_8440 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___69_8440.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___69_8440.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___69_8440.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___69_8440.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___69_8440.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___69_8440.FStar_Syntax_Syntax.lbpos)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____8410 with
            | (lbs1, e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb ->
                            let tcenv =
                              let uu____8472 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8472 in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____8479 ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____8483 = FStar_Options.ml_ish () in
                               if uu____8483
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
                             let uu___70_8487 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___70_8487.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___70_8487.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___70_8487.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___70_8487.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___70_8487.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___70_8487.FStar_Syntax_Syntax.lbpos)
                             })))
                  else lbs1 in
                let maybe_generalize uu____8510 =
                  match uu____8510 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8530;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;
                      FStar_Syntax_Syntax.lbattrs = uu____8534;
                      FStar_Syntax_Syntax.lbpos = uu____8535;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t2 = FStar_Syntax_Subst.compress t1 in
                      let no_gen uu____8609 =
                        let expected_t = term_as_mlty g t2 in
                        (lbname_, f_e, (t2, ([], ([], expected_t))), false,
                          e) in
                      if Prims.op_Negation top_level
                      then no_gen ()
                      else
                        (match t2.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                             let uu____8726 = FStar_List.hd bs in
                             FStar_All.pipe_right uu____8726
                               (is_type_binder g)
                             ->
                             let uu____8739 =
                               FStar_Syntax_Subst.open_comp bs c in
                             (match uu____8739 with
                              | (bs1, c1) ->
                                  let uu____8764 =
                                    let uu____8771 =
                                      FStar_Util.prefix_until
                                        (fun x ->
                                           let uu____8807 =
                                             is_type_binder g x in
                                           Prims.op_Negation uu____8807) bs1 in
                                    match uu____8771 with
                                    | FStar_Pervasives_Native.None ->
                                        (bs1,
                                          (FStar_Syntax_Util.comp_result c1))
                                    | FStar_Pervasives_Native.Some
                                        (bs2, b, rest) ->
                                        let uu____8895 =
                                          FStar_Syntax_Util.arrow (b :: rest)
                                            c1 in
                                        (bs2, uu____8895) in
                                  (match uu____8764 with
                                   | (tbinders, tbody) ->
                                       let n_tbinders =
                                         FStar_List.length tbinders in
                                       let e1 =
                                         let uu____8940 = normalize_abs e in
                                         FStar_All.pipe_right uu____8940
                                           FStar_Syntax_Util.unmeta in
                                       (match e1.FStar_Syntax_Syntax.n with
                                        | FStar_Syntax_Syntax.Tm_abs
                                            (bs2, body, copt) ->
                                            let uu____8982 =
                                              FStar_Syntax_Subst.open_term
                                                bs2 body in
                                            (match uu____8982 with
                                             | (bs3, body1) ->
                                                 if
                                                   n_tbinders <=
                                                     (FStar_List.length bs3)
                                                 then
                                                   let uu____9035 =
                                                     FStar_Util.first_N
                                                       n_tbinders bs3 in
                                                   (match uu____9035 with
                                                    | (targs, rest_args) ->
                                                        let expected_source_ty
                                                          =
                                                          let s =
                                                            FStar_List.map2
                                                              (fun uu____9123
                                                                 ->
                                                                 fun
                                                                   uu____9124
                                                                   ->
                                                                   match 
                                                                    (uu____9123,
                                                                    uu____9124)
                                                                   with
                                                                   | 
                                                                   ((x,
                                                                    uu____9142),
                                                                    (y,
                                                                    uu____9144))
                                                                    ->
                                                                    let uu____9153
                                                                    =
                                                                    let uu____9160
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____9160) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9153)
                                                              tbinders targs in
                                                          FStar_Syntax_Subst.subst
                                                            s tbody in
                                                        let env =
                                                          FStar_List.fold_left
                                                            (fun env ->
                                                               fun uu____9171
                                                                 ->
                                                                 match uu____9171
                                                                 with
                                                                 | (a,
                                                                    uu____9177)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    FStar_Pervasives_Native.None)
                                                            g targs in
                                                        let expected_t =
                                                          term_as_mlty env
                                                            expected_source_ty in
                                                        let polytype =
                                                          let uu____9186 =
                                                            FStar_All.pipe_right
                                                              targs
                                                              (FStar_List.map
                                                                 (fun
                                                                    uu____9204
                                                                    ->
                                                                    match uu____9204
                                                                    with
                                                                    | 
                                                                    (x,
                                                                    uu____9210)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                          (uu____9186,
                                                            expected_t) in
                                                        let add_unit =
                                                          match rest_args
                                                          with
                                                          | [] ->
                                                              let uu____9218
                                                                =
                                                                is_fstar_value
                                                                  body1 in
                                                              Prims.op_Negation
                                                                uu____9218
                                                          | uu____9219 ->
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
                                            uu____9288 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env ->
                                                   fun uu____9305 ->
                                                     match uu____9305 with
                                                     | (a, uu____9311) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders in
                                            let expected_t =
                                              term_as_mlty env tbody in
                                            let polytype =
                                              let uu____9320 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9332 ->
                                                        match uu____9332 with
                                                        | (x, uu____9338) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x)) in
                                              (uu____9320, expected_t) in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9354 ->
                                                      match uu____9354 with
                                                      | (bv, uu____9360) ->
                                                          let uu____9361 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv in
                                                          FStar_All.pipe_right
                                                            uu____9361
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
                                            uu____9403 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env ->
                                                   fun uu____9414 ->
                                                     match uu____9414 with
                                                     | (a, uu____9420) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders in
                                            let expected_t =
                                              term_as_mlty env tbody in
                                            let polytype =
                                              let uu____9429 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9441 ->
                                                        match uu____9441 with
                                                        | (x, uu____9447) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x)) in
                                              (uu____9429, expected_t) in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9463 ->
                                                      match uu____9463 with
                                                      | (bv, uu____9469) ->
                                                          let uu____9470 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv in
                                                          FStar_All.pipe_right
                                                            uu____9470
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
                                            uu____9512 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env ->
                                                   fun uu____9523 ->
                                                     match uu____9523 with
                                                     | (a, uu____9529) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders in
                                            let expected_t =
                                              term_as_mlty env tbody in
                                            let polytype =
                                              let uu____9538 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9550 ->
                                                        match uu____9550 with
                                                        | (x, uu____9556) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x)) in
                                              (uu____9538, expected_t) in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9572 ->
                                                      match uu____9572 with
                                                      | (bv, uu____9578) ->
                                                          let uu____9579 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv in
                                                          FStar_All.pipe_right
                                                            uu____9579
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
                                        | uu____9621 ->
                                            err_value_restriction e1)))
                         | uu____9640 -> no_gen ()) in
                let check_lb env uu____9683 =
                  match uu____9683 with
                  | (nm, (lbname, f, (t1, (targs, polytype)), add_unit, e))
                      ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1 ->
                             fun uu____9818 ->
                               match uu____9818 with
                               | (a, uu____9824) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs in
                      let expected_t = FStar_Pervasives_Native.snd polytype in
                      let uu____9826 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____9826 with
                       | (e1, uu____9836) ->
                           let f1 = maybe_downgrade_eff env1 f expected_t in
                           (f1,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (FStar_Pervasives_Native.Some polytype);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e1;
                               FStar_Extraction_ML_Syntax.mllb_meta = [];
                               FStar_Extraction_ML_Syntax.print_typ = true
                             })) in
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize) in
                let uu____9903 =
                  FStar_List.fold_right
                    (fun lb ->
                       fun uu____9994 ->
                         match uu____9994 with
                         | (env, lbs4) ->
                             let uu____10119 = lb in
                             (match uu____10119 with
                              | (lbname, uu____10167,
                                 (t1, (uu____10169, polytype)), add_unit,
                                 uu____10172) ->
                                  let uu____10185 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____10185 with
                                   | (env1, nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, []) in
                (match uu____9903 with
                 | (env_body, lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____10462 = term_as_mlexpr env_body e'1 in
                     (match uu____10462 with
                      | (e'2, f', t') ->
                          let f =
                            let uu____10479 =
                              let uu____10482 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5 in
                              f' :: uu____10482 in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10479 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____10491 =
                            let uu____10492 =
                              let uu____10493 =
                                let uu____10494 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5 in
                                (is_rec1, uu____10494) in
                              mk_MLE_Let top_level uu____10493 e'2 in
                            let uu____10503 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10492 uu____10503 in
                          (uu____10491, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee, pats) ->
           let uu____10542 = term_as_mlexpr g scrutinee in
           (match uu____10542 with
            | (e, f_e, t_e) ->
                let uu____10558 = check_pats_for_ite pats in
                (match uu____10558 with
                 | (b, then_e, else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some then_e1,
                           FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10615 = term_as_mlexpr g then_e1 in
                            (match uu____10615 with
                             | (then_mle, f_then, t_then) ->
                                 let uu____10631 = term_as_mlexpr g else_e1 in
                                 (match uu____10631 with
                                  | (else_mle, f_else, t_else) ->
                                      let uu____10647 =
                                        let uu____10656 =
                                          type_leq g t_then t_else in
                                        if uu____10656
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10670 =
                                             type_leq g t_else t_then in
                                           if uu____10670
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____10647 with
                                       | (t_branch, maybe_lift1) ->
                                           let uu____10704 =
                                             let uu____10705 =
                                               let uu____10706 =
                                                 let uu____10715 =
                                                   maybe_lift1 then_mle
                                                     t_then in
                                                 let uu____10716 =
                                                   let uu____10719 =
                                                     maybe_lift1 else_mle
                                                       t_else in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10719 in
                                                 (e, uu____10715,
                                                   uu____10716) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10706 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10705 in
                                           let uu____10722 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____10704, uu____10722,
                                             t_branch))))
                        | uu____10723 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10739 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat ->
                                  fun br ->
                                    let uu____10848 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____10848 with
                                    | (pat, when_opt, branch1) ->
                                        let uu____10892 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr in
                                        (match uu____10892 with
                                         | (env, p, pat_t_compat) ->
                                             let uu____10950 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let uu____10972 =
                                                     term_as_mlexpr env w in
                                                   (match uu____10972 with
                                                    | (w1, f_w, t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w)) in
                                             (match uu____10950 with
                                              | (when_opt1, f_when) ->
                                                  let uu____11021 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____11021 with
                                                   | (mlbranch, f_branch,
                                                      t_branch) ->
                                                       let uu____11055 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____11132
                                                                 ->
                                                                 match uu____11132
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
                                                         uu____11055)))))
                               true) in
                        match uu____10739 with
                        | (pat_t_compat, mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____11297 ->
                                      let uu____11298 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____11299 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____11298 uu____11299);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____11324 =
                                   let uu____11333 =
                                     let uu____11350 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____11350 in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____11333 in
                                 (match uu____11324 with
                                  | (uu____11393, fw, uu____11395,
                                     uu____11396) ->
                                      let uu____11397 =
                                        let uu____11398 =
                                          let uu____11399 =
                                            let uu____11406 =
                                              let uu____11409 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____11409] in
                                            (fw, uu____11406) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11399 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____11398 in
                                      (uu____11397,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____11412, uu____11413,
                                (uu____11414, f_first, t_first))::rest ->
                                 let uu____11474 =
                                   FStar_List.fold_left
                                     (fun uu____11516 ->
                                        fun uu____11517 ->
                                          match (uu____11516, uu____11517)
                                          with
                                          | ((topt, f),
                                             (uu____11574, uu____11575,
                                              (uu____11576, f_branch,
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
                                                    let uu____11632 =
                                                      type_leq g t1 t_branch in
                                                    if uu____11632
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11636 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____11636
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           t1
                                                       else
                                                         FStar_Pervasives_Native.None) in
                                              (topt1, f1))
                                     ((FStar_Pervasives_Native.Some t_first),
                                       f_first) rest in
                                 (match uu____11474 with
                                  | (topt, f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11731 ->
                                                match uu____11731 with
                                                | (p, (wopt, uu____11760),
                                                   (b1, uu____11762, t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11781 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | FStar_Pervasives_Native.Some t1 ->
                                            t1 in
                                      let uu____11786 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____11786, f_match, t_match)))))))
let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env ->
    fun discName ->
      fun constrName ->
        let uu____11806 =
          let uu____11811 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11811 in
        match uu____11806 with
        | (uu____11836, fstar_disc_type) ->
            let wildcards =
              let uu____11845 =
                let uu____11846 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____11846.FStar_Syntax_Syntax.n in
              match uu____11845 with
              | FStar_Syntax_Syntax.Tm_arrow (binders, uu____11856) ->
                  let uu____11873 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___63_11905 ->
                            match uu___63_11905 with
                            | (uu____11912, FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11913)) ->
                                true
                            | uu____11916 -> false)) in
                  FStar_All.pipe_right uu____11873
                    (FStar_List.map
                       (fun uu____11949 ->
                          let uu____11956 = fresh "_" in
                          (uu____11956, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11957 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____11968 =
                let uu____11969 =
                  let uu____11980 =
                    let uu____11981 =
                      let uu____11982 =
                        let uu____11997 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid)) in
                        let uu____12000 =
                          let uu____12011 =
                            let uu____12020 =
                              let uu____12021 =
                                let uu____12028 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____12028,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____12021 in
                            let uu____12031 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____12020, FStar_Pervasives_Native.None,
                              uu____12031) in
                          let uu____12034 =
                            let uu____12045 =
                              let uu____12054 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____12054) in
                            [uu____12045] in
                          uu____12011 :: uu____12034 in
                        (uu____11997, uu____12000) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11982 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11981 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11980) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11969 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11968 in
            let uu____12109 =
              let uu____12110 =
                let uu____12113 =
                  let uu____12114 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____12114;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____12113] in
              (FStar_Extraction_ML_Syntax.NonRec, uu____12110) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____12109