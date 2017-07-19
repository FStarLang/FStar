open Prims
exception Un_extractable
let uu___is_Un_extractable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____5 -> false
let type_leq:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        FStar_Extraction_ML_Util.type_leq
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
let type_leq_c:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool,FStar_Extraction_ML_Syntax.mlexpr
                        FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        FStar_Extraction_ML_Util.type_leq_c
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
let erasableType:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t  ->
      FStar_Extraction_ML_Util.erasableType
        (FStar_Extraction_ML_Util.udelta_unfold g) t
let eraseTypeDeep:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t  ->
      FStar_Extraction_ML_Util.eraseTypeDeep
        (FStar_Extraction_ML_Util.udelta_unfold g) t
let record_fields fs vs =
  FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
let fail r msg =
  (let uu____112 =
     let uu____113 = FStar_Range.string_of_range r in
     FStar_Util.format2 "%s: %s\n" uu____113 msg in
   FStar_All.pipe_left FStar_Util.print_string uu____112);
  failwith msg
let err_uninst env t uu____152 app =
  match uu____152 with
  | (vars,ty) ->
      let uu____178 =
        let uu____179 = FStar_Syntax_Print.term_to_string t in
        let uu____180 =
          let uu____181 =
            FStar_All.pipe_right vars
              (FStar_List.map FStar_Pervasives_Native.fst) in
          FStar_All.pipe_right uu____181 (FStar_String.concat ", ") in
        let uu____198 =
          FStar_Extraction_ML_Code.string_of_mlty
            env.FStar_Extraction_ML_UEnv.currentModule ty in
        let uu____199 = FStar_Syntax_Print.term_to_string app in
        FStar_Util.format4
          "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
          uu____179 uu____180 uu____198 uu____199 in
      fail t.FStar_Syntax_Syntax.pos uu____178
let err_ill_typed_application env t args ty =
  let uu____242 =
    let uu____243 = FStar_Syntax_Print.term_to_string t in
    let uu____244 =
      let uu____245 =
        FStar_All.pipe_right args
          (FStar_List.map
             (fun uu____263  ->
                match uu____263 with
                | (x,uu____269) -> FStar_Syntax_Print.term_to_string x)) in
      FStar_All.pipe_right uu____245 (FStar_String.concat " ") in
    let uu____272 =
      FStar_Extraction_ML_Code.string_of_mlty
        env.FStar_Extraction_ML_UEnv.currentModule ty in
    FStar_Util.format3
      "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
      uu____243 uu____244 uu____272 in
  fail t.FStar_Syntax_Syntax.pos uu____242
let err_value_restriction t =
  let uu____290 =
    let uu____291 = FStar_Syntax_Print.tag_of_term t in
    let uu____292 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.format2
      "Refusing to generalize because of the value restriction: (%s) %s"
      uu____291 uu____292 in
  fail t.FStar_Syntax_Syntax.pos uu____290
let err_unexpected_eff t f0 f1 =
  let uu____322 =
    let uu____323 = FStar_Syntax_Print.term_to_string t in
    FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s"
      uu____323 (FStar_Extraction_ML_Util.eff_to_string f0)
      (FStar_Extraction_ML_Util.eff_to_string f1) in
  fail t.FStar_Syntax_Syntax.pos uu____322
let effect_as_etag:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  let rec delta_norm_eff g l =
    let uu____340 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
    match uu____340 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____345 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l in
          match uu____345 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____356,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c) in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res) in
  fun g  ->
    fun l  ->
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
           | FStar_Pervasives_Native.Some (ed,qualifiers) ->
               let uu____389 =
                 FStar_All.pipe_right qualifiers
                   (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
               if uu____389
               then FStar_Extraction_ML_Syntax.E_PURE
               else FStar_Extraction_ML_Syntax.E_IMPURE
           | FStar_Pervasives_Native.None  ->
               FStar_Extraction_ML_Syntax.E_IMPURE)
let rec is_arity:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu____408 =
        let uu____409 = FStar_Syntax_Subst.compress t1 in
        uu____409.FStar_Syntax_Syntax.n in
      match uu____408 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____414 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____443 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____478 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_uvar uu____487 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____508 -> false
      | FStar_Syntax_Syntax.Tm_name uu____509 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____510 -> false
      | FStar_Syntax_Syntax.Tm_type uu____511 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____512,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____534 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1 in
          let uu____536 =
            let uu____537 = FStar_Syntax_Subst.compress t2 in
            uu____537.FStar_Syntax_Syntax.n in
          (match uu____536 with
           | FStar_Syntax_Syntax.Tm_fvar uu____542 -> false
           | uu____543 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____544 ->
          let uu____563 = FStar_Syntax_Util.head_and_args t1 in
          (match uu____563 with | (head1,uu____583) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____613) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____623) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____632,body,uu____634) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____659,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____681,branches) ->
          (match branches with
           | (uu____731,uu____732,e)::uu____734 -> is_arity env e
           | uu____797 -> false)
let rec is_type_aux:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____827 ->
          let uu____856 =
            let uu____857 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____857 in
          failwith uu____856
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____858 =
            let uu____859 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Util.format1 "Impossible: %s" uu____859 in
          failwith uu____858
      | FStar_Syntax_Syntax.Tm_constant uu____860 -> false
      | FStar_Syntax_Syntax.Tm_type uu____861 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____862 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____871 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar (uu____888,t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____922;
            FStar_Syntax_Syntax.index = uu____923;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____929;
            FStar_Syntax_Syntax.index = uu____930;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____937,uu____938) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____996) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1007) ->
          let uu____1032 = FStar_Syntax_Subst.open_term bs body in
          (match uu____1032 with
           | (uu____1037,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
          let uu____1058 =
            let uu____1063 =
              let uu____1064 = FStar_Syntax_Syntax.mk_binder x in
              [uu____1064] in
            FStar_Syntax_Subst.open_term uu____1063 body in
          (match uu____1058 with
           | (uu____1065,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1067,lbs),body) ->
          let uu____1088 = FStar_Syntax_Subst.open_let_rec lbs body in
          (match uu____1088 with
           | (uu____1095,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1101,branches) ->
          (match branches with
           | b::uu____1152 ->
               let uu____1209 = FStar_Syntax_Subst.open_branch b in
               (match uu____1209 with
                | (uu____1210,uu____1211,e) -> is_type_aux env e)
           | uu____1237 -> false)
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1259) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1269) ->
          is_type_aux env head1
let is_type:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1310  ->
           let uu____1311 = FStar_Syntax_Print.tag_of_term t in
           let uu____1312 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1311
             uu____1312);
      (let b = is_type_aux env t in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1318  ->
            if b
            then
              let uu____1319 = FStar_Syntax_Print.term_to_string t in
              let uu____1320 = FStar_Syntax_Print.tag_of_term t in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1319 uu____1320
            else
              (let uu____1322 = FStar_Syntax_Print.term_to_string t in
               let uu____1323 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1322 uu____1323));
       b)
let is_type_binder env x =
  is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
let is_constructor: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1351 =
      let uu____1352 = FStar_Syntax_Subst.compress t in
      uu____1352.FStar_Syntax_Syntax.n in
    match uu____1351 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1357;
          FStar_Syntax_Syntax.fv_delta = uu____1358;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1359;
          FStar_Syntax_Syntax.fv_delta = uu____1360;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1361);_}
        -> true
    | uu____1368 -> false
let rec is_fstar_value: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1373 =
      let uu____1374 = FStar_Syntax_Subst.compress t in
      uu____1374.FStar_Syntax_Syntax.n in
    match uu____1373 with
    | FStar_Syntax_Syntax.Tm_constant uu____1379 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1380 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1381 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1382 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1431 = is_constructor head1 in
        if uu____1431
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1449  ->
                  match uu____1449 with
                  | (te,uu____1455) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1458) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1468,uu____1469) ->
        is_fstar_value t1
    | uu____1526 -> false
let rec is_ml_value: FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1531 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1532 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1533 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1534 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1545,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1554,fields) ->
        FStar_Util.for_all
          (fun uu____1579  ->
             match uu____1579 with | (uu____1584,e1) -> is_ml_value e1)
          fields
    | uu____1586 -> false
let normalize_abs: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1649 ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu____1651 = FStar_Syntax_Util.is_fun e' in
          if uu____1651
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 FStar_Pervasives_Native.None
let unit_binder: FStar_Syntax_Syntax.binder =
  let uu____1657 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_TypeChecker_Common.t_unit in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1657
let check_pats_for_ite:
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3
  =
  fun l  ->
    let def =
      (false, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) in
    if (FStar_List.length l) <> (Prims.parse_int "2")
    then def
    else
      (let uu____1736 = FStar_List.hd l in
       match uu____1736 with
       | (p1,w1,e1) ->
           let uu____1770 =
             let uu____1779 = FStar_List.tl l in FStar_List.hd uu____1779 in
           (match uu____1770 with
            | (p2,w2,e2) ->
                (match (w1, w2, (p1.FStar_Syntax_Syntax.v),
                         (p2.FStar_Syntax_Syntax.v))
                 with
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None
                    ,FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool
                    (true )),FStar_Syntax_Syntax.Pat_constant
                    (FStar_Const.Const_bool (false ))) ->
                     (true, (FStar_Pervasives_Native.Some e1),
                       (FStar_Pervasives_Native.Some e2))
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None
                    ,FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool
                    (false )),FStar_Syntax_Syntax.Pat_constant
                    (FStar_Const.Const_bool (true ))) ->
                     (true, (FStar_Pervasives_Native.Some e2),
                       (FStar_Pervasives_Native.Some e1))
                 | uu____1853 -> def)))
let instantiate:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  = fun s  -> fun args  -> FStar_Extraction_ML_Util.subst s args
let erasable:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun f  ->
      fun t  ->
        (f = FStar_Extraction_ML_Syntax.E_GHOST) ||
          ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))
let erase:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.e_tag ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
            FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun e  ->
      fun ty  ->
        fun f  ->
          let e1 =
            let uu____1919 = erasable g f ty in
            if uu____1919
            then
              let uu____1920 =
                type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty in
              (if uu____1920
               then FStar_Extraction_ML_Syntax.ml_unit
               else
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                      (FStar_Extraction_ML_Syntax.ml_unit,
                        FStar_Extraction_ML_Syntax.ml_unit_ty, ty)))
            else e in
          (e1, f, ty)
let maybe_coerce:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun g  ->
    fun e  ->
      fun ty  ->
        fun expect  ->
          let ty1 = eraseTypeDeep g ty in
          let uu____1940 =
            type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect in
          match uu____1940 with
          | (true ,FStar_Pervasives_Native.Some e') -> e'
          | uu____1950 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1962  ->
                    let uu____1963 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e in
                    let uu____1964 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1 in
                    let uu____1965 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1963 uu____1964 uu____1965);
               FStar_All.pipe_left
                 (FStar_Extraction_ML_Syntax.with_ty expect)
                 (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect)))
let bv_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun bv  ->
      let uu____1974 = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu____1974 with
      | FStar_Util.Inl (uu____1975,t) -> t
      | uu____1989 -> FStar_Extraction_ML_Syntax.MLTY_Top
let rec term_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun t0  ->
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____2032 ->
            let uu____2039 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu____2039 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____2043 -> false in
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.Iota;
          FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses]
          g.FStar_Extraction_ML_UEnv.tcenv t0 in
      let mlt = term_as_mlty' g t in
      let uu____2046 = is_top_ty mlt in
      if uu____2046
      then
        let t1 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.Delta_constant;
            FStar_TypeChecker_Normalize.Iota;
            FStar_TypeChecker_Normalize.Zeta;
            FStar_TypeChecker_Normalize.EraseUniverses;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses]
            g.FStar_Extraction_ML_UEnv.tcenv t0 in
        term_as_mlty' g t1
      else mlt
and term_as_mlty':
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar uu____2052 ->
          let uu____2053 =
            let uu____2054 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2054 in
          failwith uu____2053
      | FStar_Syntax_Syntax.Tm_delayed uu____2055 ->
          let uu____2084 =
            let uu____2085 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2085 in
          failwith uu____2084
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2086 =
            let uu____2087 = FStar_Syntax_Print.term_to_string t1 in
            FStar_Util.format1 "Impossible: Unexpected term %s" uu____2087 in
          failwith uu____2086
      | FStar_Syntax_Syntax.Tm_constant uu____2088 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_uvar uu____2089 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____2111) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____2120;
             FStar_Syntax_Syntax.index = uu____2121;
             FStar_Syntax_Syntax.sort = t2;_},uu____2123)
          -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2137) -> term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2147,uu____2148) ->
          term_as_mlty' env t2
      | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
      | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____2237 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____2237 with
           | (bs1,c1) ->
               let uu____2244 = binders_as_ml_binders env bs1 in
               (match uu____2244 with
                | (mlbs,env1) ->
                    let t_ret =
                      let eff =
                        FStar_TypeChecker_Env.norm_eff_name
                          env1.FStar_Extraction_ML_UEnv.tcenv
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let uu____2271 =
                        let uu____2278 =
                          FStar_TypeChecker_Env.effect_decl_opt
                            env1.FStar_Extraction_ML_UEnv.tcenv eff in
                        FStar_Util.must uu____2278 in
                      match uu____2271 with
                      | (ed,qualifiers) ->
                          let uu____2299 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable) in
                          if uu____2299
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
                    let uu____2306 =
                      FStar_List.fold_right
                        (fun uu____2325  ->
                           fun uu____2326  ->
                             match (uu____2325, uu____2326) with
                             | ((uu____2347,t2),(tag,t')) ->
                                 (FStar_Extraction_ML_Syntax.E_PURE,
                                   (FStar_Extraction_ML_Syntax.MLTY_Fun
                                      (t2, tag, t')))) mlbs (erase1, t_ret) in
                    (match uu____2306 with | (uu____2359,t2) -> t2)))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let res =
            let uu____2392 =
              let uu____2393 = FStar_Syntax_Util.un_uinst head1 in
              uu____2393.FStar_Syntax_Syntax.n in
            match uu____2392 with
            | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
            | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
            | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                let uu____2430 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (head2, (FStar_List.append args' args)))
                    FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos in
                term_as_mlty' env uu____2430
            | uu____2453 -> FStar_Extraction_ML_UEnv.unknownType in
          res
      | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2456) ->
          let uu____2481 = FStar_Syntax_Subst.open_term bs ty in
          (match uu____2481 with
           | (bs1,ty1) ->
               let uu____2488 = binders_as_ml_binders env bs1 in
               (match uu____2488 with | (bts,env1) -> term_as_mlty' env1 ty1))
      | FStar_Syntax_Syntax.Tm_type uu____2513 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_let uu____2514 ->
          FStar_Extraction_ML_UEnv.unknownType
      | FStar_Syntax_Syntax.Tm_match uu____2529 ->
          FStar_Extraction_ML_UEnv.unknownType
and arg_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun uu____2559  ->
      match uu____2559 with
      | (a,uu____2565) ->
          let uu____2566 = is_type g a in
          if uu____2566
          then term_as_mlty' g a
          else FStar_Extraction_ML_UEnv.erasedContent
and fv_app_as_mlty:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.args -> FStar_Extraction_ML_Syntax.mlty
  =
  fun g  ->
    fun fv  ->
      fun args  ->
        let uu____2571 =
          let uu____2586 =
            FStar_TypeChecker_Env.lookup_lid g.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____2586 with
          | ((uu____2609,fvty),uu____2611) ->
              let fvty1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant]
                  g.FStar_Extraction_ML_UEnv.tcenv fvty in
              FStar_Syntax_Util.arrow_formals fvty1 in
        match uu____2571 with
        | (formals,uu____2618) ->
            let mlargs = FStar_List.map (arg_as_mlty g) args in
            let mlargs1 =
              let n_args = FStar_List.length args in
              if (FStar_List.length formals) > n_args
              then
                let uu____2668 = FStar_Util.first_N n_args formals in
                match uu____2668 with
                | (uu____2695,rest) ->
                    let uu____2721 =
                      FStar_List.map
                        (fun uu____2729  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest in
                    FStar_List.append mlargs uu____2721
              else mlargs in
            let nm =
              let uu____2736 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv in
              match uu____2736 with
              | FStar_Pervasives_Native.Some p -> p
              | FStar_Pervasives_Native.None  ->
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)
and binders_as_ml_binders:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Extraction_ML_UEnv.env)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun bs  ->
      let uu____2754 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2809  ->
                fun b  ->
                  match uu____2809 with
                  | (ml_bs,env) ->
                      let uu____2865 = is_type_binder g b in
                      if uu____2865
                      then
                        let b1 = FStar_Pervasives_Native.fst b in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top) in
                        let ml_b =
                          let uu____2891 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1 in
                          (uu____2891, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b in
                         let t = term_as_mlty env b1.FStar_Syntax_Syntax.sort in
                         let uu____2921 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false in
                         match uu____2921 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2953 =
                                 FStar_Extraction_ML_UEnv.removeTick b2 in
                               (uu____2953, t) in
                             ((ml_b :: ml_bs), env1))) ([], g)) in
      match uu____2754 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)
let mk_MLE_Seq:
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun e1  ->
    fun e2  ->
      match ((e1.FStar_Extraction_ML_Syntax.expr),
              (e2.FStar_Extraction_ML_Syntax.expr))
      with
      | (FStar_Extraction_ML_Syntax.MLE_Seq
         es1,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 es2)
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____3063) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____3066,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____3070 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
let mk_MLE_Let:
  Prims.bool ->
    FStar_Extraction_ML_Syntax.mlletbinding ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun top_level  ->
    fun lbs  ->
      fun body  ->
        match lbs with
        | (FStar_Extraction_ML_Syntax.NonRec ,quals,lb::[]) when
            Prims.op_Negation top_level ->
            (match lb.FStar_Extraction_ML_Syntax.mllb_tysc with
             | FStar_Pervasives_Native.Some ([],t) when
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
                    | uu____3102 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____3103 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____3104 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____3107 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
let resugar_pat:
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____3126 = FStar_Extraction_ML_Util.is_xtuple d in
          (match uu____3126 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____3130 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns in
                    let fs = record_fields fns pats in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____3157 -> p))
      | uu____3160 -> p
let rec extract_one_pat:
  Prims.bool ->
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.pat ->
        FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option ->
          (FStar_Extraction_ML_UEnv.env,(FStar_Extraction_ML_Syntax.mlpattern,
                                          FStar_Extraction_ML_Syntax.mlexpr
                                            Prims.list)
                                          FStar_Pervasives_Native.tuple2
                                          FStar_Pervasives_Native.option,
            Prims.bool) FStar_Pervasives_Native.tuple3
  =
  fun imp  ->
    fun g  ->
      fun p  ->
        fun expected_topt  ->
          let ok t =
            match expected_topt with
            | FStar_Pervasives_Native.None  -> true
            | FStar_Pervasives_Native.Some t' ->
                let ok = type_leq g t t' in
                (if Prims.op_Negation ok
                 then
                   FStar_Extraction_ML_UEnv.debug g
                     (fun uu____3219  ->
                        let uu____3220 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t' in
                        let uu____3221 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule t in
                        FStar_Util.print2
                          "Expected pattern type %s; got pattern type %s\n"
                          uu____3220 uu____3221)
                 else ();
                 ok) in
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
              (c,FStar_Pervasives_Native.None )) ->
              let i = FStar_Const.Const_int (c, FStar_Pervasives_Native.None) in
              let x = FStar_Extraction_ML_Syntax.gensym () in
              let when_clause =
                let uu____3261 =
                  let uu____3262 =
                    let uu____3269 =
                      let uu____3272 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty)
                          (FStar_Extraction_ML_Syntax.MLE_Var x) in
                      let uu____3273 =
                        let uu____3276 =
                          let uu____3277 =
                            let uu____3278 =
                              FStar_Extraction_ML_Util.mlconst_of_const'
                                p.FStar_Syntax_Syntax.p i in
                            FStar_All.pipe_left
                              (fun _0_41  ->
                                 FStar_Extraction_ML_Syntax.MLE_Const _0_41)
                              uu____3278 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_int_ty)
                            uu____3277 in
                        [uu____3276] in
                      uu____3272 :: uu____3273 in
                    (FStar_Extraction_ML_Util.prims_op_equality, uu____3269) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____3262 in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3261 in
              let uu____3281 = ok FStar_Extraction_ML_Syntax.ml_int_ty in
              (g,
                (FStar_Pervasives_Native.Some
                   ((FStar_Extraction_ML_Syntax.MLP_Var x), [when_clause])),
                uu____3281)
          | FStar_Syntax_Syntax.Pat_constant s ->
              let t =
                FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s in
              let mlty = term_as_mlty g t in
              let uu____3301 =
                let uu____3310 =
                  let uu____3317 =
                    let uu____3318 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        p.FStar_Syntax_Syntax.p s in
                    FStar_Extraction_ML_Syntax.MLP_Const uu____3318 in
                  (uu____3317, []) in
                FStar_Pervasives_Native.Some uu____3310 in
              let uu____3327 = ok mlty in (g, uu____3301, uu____3327)
          | FStar_Syntax_Syntax.Pat_var x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____3338 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____3338 with
               | (g1,x1) ->
                   let uu____3361 = ok mlty in
                   (g1,
                     (if imp
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____3361))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort in
              let uu____3395 =
                FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false false
                  imp in
              (match uu____3395 with
               | (g1,x1) ->
                   let uu____3418 = ok mlty in
                   (g1,
                     (if imp
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                     uu____3418))
          | FStar_Syntax_Syntax.Pat_dot_term uu____3450 ->
              (g, FStar_Pervasives_Native.None, true)
          | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
              let uu____3491 =
                let uu____3496 = FStar_Extraction_ML_UEnv.lookup_fv g f in
                match uu____3496 with
                | FStar_Util.Inr
                    (uu____3501,{
                                  FStar_Extraction_ML_Syntax.expr =
                                    FStar_Extraction_ML_Syntax.MLE_Name n1;
                                  FStar_Extraction_ML_Syntax.mlty =
                                    uu____3503;
                                  FStar_Extraction_ML_Syntax.loc = uu____3504;_},ttys,uu____3506)
                    -> (n1, ttys)
                | uu____3519 -> failwith "Expected a constructor" in
              (match uu____3491 with
               | (d,tys) ->
                   let nTyVars =
                     FStar_List.length (FStar_Pervasives_Native.fst tys) in
                   let uu____3541 = FStar_Util.first_N nTyVars pats in
                   (match uu____3541 with
                    | (tysVarPats,restPats) ->
                        let f_ty_opt =
                          try
                            let mlty_args =
                              FStar_All.pipe_right tysVarPats
                                (FStar_List.map
                                   (fun uu____3674  ->
                                      match uu____3674 with
                                      | (p1,uu____3682) ->
                                          (match p1.FStar_Syntax_Syntax.v
                                           with
                                           | FStar_Syntax_Syntax.Pat_dot_term
                                               (uu____3687,t) ->
                                               term_as_mlty g t
                                           | uu____3697 ->
                                               (FStar_Extraction_ML_UEnv.debug
                                                  g
                                                  (fun uu____3701  ->
                                                     let uu____3702 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1 in
                                                     FStar_Util.print1
                                                       "Pattern %s is not extractable"
                                                       uu____3702);
                                                raise Un_extractable)))) in
                            let f_ty =
                              FStar_Extraction_ML_Util.subst tys mlty_args in
                            let uu____3704 =
                              FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty in
                            FStar_Pervasives_Native.Some uu____3704
                          with
                          | Un_extractable  -> FStar_Pervasives_Native.None in
                        let uu____3733 =
                          FStar_Util.fold_map
                            (fun g1  ->
                               fun uu____3769  ->
                                 match uu____3769 with
                                 | (p1,imp1) ->
                                     let uu____3788 =
                                       extract_one_pat true g1 p1
                                         FStar_Pervasives_Native.None in
                                     (match uu____3788 with
                                      | (g2,p2,uu____3817) -> (g2, p2))) g
                            tysVarPats in
                        (match uu____3733 with
                         | (g1,tyMLPats) ->
                             let uu____3878 =
                               FStar_Util.fold_map
                                 (fun uu____3942  ->
                                    fun uu____3943  ->
                                      match (uu____3942, uu____3943) with
                                      | ((g2,f_ty_opt1),(p1,imp1)) ->
                                          let uu____4036 =
                                            match f_ty_opt1 with
                                            | FStar_Pervasives_Native.Some
                                                (hd1::rest,res) ->
                                                ((FStar_Pervasives_Native.Some
                                                    (rest, res)),
                                                  (FStar_Pervasives_Native.Some
                                                     hd1))
                                            | uu____4096 ->
                                                (FStar_Pervasives_Native.None,
                                                  FStar_Pervasives_Native.None) in
                                          (match uu____4036 with
                                           | (f_ty_opt2,expected_ty) ->
                                               let uu____4167 =
                                                 extract_one_pat false g2 p1
                                                   expected_ty in
                                               (match uu____4167 with
                                                | (g3,p2,uu____4208) ->
                                                    ((g3, f_ty_opt2), p2))))
                                 (g1, f_ty_opt) restPats in
                             (match uu____3878 with
                              | ((g2,f_ty_opt1),restMLPats) ->
                                  let uu____4326 =
                                    let uu____4337 =
                                      FStar_All.pipe_right
                                        (FStar_List.append tyMLPats
                                           restMLPats)
                                        (FStar_List.collect
                                           (fun uu___139_4388  ->
                                              match uu___139_4388 with
                                              | FStar_Pervasives_Native.Some
                                                  x -> [x]
                                              | uu____4430 -> [])) in
                                    FStar_All.pipe_right uu____4337
                                      FStar_List.split in
                                  (match uu____4326 with
                                   | (mlPats,when_clauses) ->
                                       let pat_ty_compat =
                                         match f_ty_opt1 with
                                         | FStar_Pervasives_Native.Some
                                             ([],t) -> ok t
                                         | uu____4503 -> false in
                                       let uu____4512 =
                                         let uu____4521 =
                                           let uu____4528 =
                                             resugar_pat
                                               f.FStar_Syntax_Syntax.fv_qual
                                               (FStar_Extraction_ML_Syntax.MLP_CTor
                                                  (d, mlPats)) in
                                           let uu____4531 =
                                             FStar_All.pipe_right
                                               when_clauses
                                               FStar_List.flatten in
                                           (uu____4528, uu____4531) in
                                         FStar_Pervasives_Native.Some
                                           uu____4521 in
                                       (g2, uu____4512, pat_ty_compat))))))
let extract_pat:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_UEnv.env,(FStar_Extraction_ML_Syntax.mlpattern,
                                        FStar_Extraction_ML_Syntax.mlexpr
                                          FStar_Pervasives_Native.option)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list,Prims.bool)
          FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun p  ->
      fun expected_t  ->
        let extract_one_pat1 g1 p1 expected_t1 =
          let uu____4622 = extract_one_pat false g1 p1 expected_t1 in
          match uu____4622 with
          | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
          | uu____4679 -> failwith "Impossible: Unable to translate pattern" in
        let mk_when_clause whens =
          match whens with
          | [] -> FStar_Pervasives_Native.None
          | hd1::tl1 ->
              let uu____4722 =
                FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1 in
              FStar_Pervasives_Native.Some uu____4722 in
        let uu____4723 =
          extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t) in
        match uu____4723 with
        | (g1,(p1,whens),b) ->
            let when_clause = mk_when_clause whens in
            (g1, [(p1, when_clause)], b)
let maybe_eta_data_and_project_record:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          FStar_Extraction_ML_Syntax.mlexpr
  =
  fun g  ->
    fun qual  ->
      fun residualType  ->
        fun mlAppExpr  ->
          let rec eta_args more_args t =
            match t with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4865,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym () in
                let uu____4868 =
                  let uu____4879 =
                    let uu____4888 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x) in
                    ((x, t0), uu____4888) in
                  uu____4879 :: more_args in
                eta_args uu____4868 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4901,uu____4902)
                -> ((FStar_List.rev more_args), t)
            | uu____4925 -> failwith "Impossible: Head type is not an arrow" in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____4953,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns in
                let fields1 = record_fields fields args in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____4985 -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu____5003 = eta_args [] residualType in
            match uu____5003 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____5056 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu____5056
                 | uu____5057 ->
                     let uu____5068 = FStar_List.unzip eargs in
                     (match uu____5068 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____5110 =
                                   let uu____5111 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1))) in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____5111 in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____5110 in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____5120 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____5123,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5127;
                FStar_Extraction_ML_Syntax.loc = uu____5128;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f]) in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu____5155 ->
                    let uu____5158 =
                      let uu____5165 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu____5165, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5158 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5169;
                FStar_Extraction_ML_Syntax.loc = uu____5170;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5178 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5178
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5182;
                FStar_Extraction_ML_Syntax.loc = uu____5183;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5185)) ->
              let uu____5198 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5198
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5204 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5204
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5208)) ->
              let uu____5217 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5217
          | uu____5220 -> mlAppExpr
let maybe_downgrade_eff:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let uu____5239 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) &&
            (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty) in
        if uu____5239 then FStar_Extraction_ML_Syntax.E_PURE else f
let rec term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun t  ->
      let uu____5293 = term_as_mlexpr' g t in
      match uu____5293 with
      | (e,tag,ty) ->
          let tag1 = maybe_downgrade_eff g tag ty in
          (FStar_Extraction_ML_UEnv.debug g
             (fun u  ->
                let uu____5314 =
                  let uu____5315 = FStar_Syntax_Print.tag_of_term t in
                  let uu____5316 = FStar_Syntax_Print.term_to_string t in
                  let uu____5317 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule ty in
                  FStar_Util.format4
                    "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
                    uu____5315 uu____5316 uu____5317
                    (FStar_Extraction_ML_Util.eff_to_string tag1) in
                FStar_Util.print_string uu____5314);
           erase g e ty tag1)
and check_term_as_mlexpr:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlty)
            FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun t  ->
      fun f  ->
        fun ty  ->
          let uu____5326 = check_term_as_mlexpr' g t f ty in
          match uu____5326 with
          | (e,t1) ->
              let uu____5337 = erase g e t1 f in
              (match uu____5337 with | (r,uu____5349,t2) -> (r, t2))
and check_term_as_mlexpr':
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlty)
            FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun e0  ->
      fun f  ->
        fun ty  ->
          let uu____5359 = term_as_mlexpr g e0 in
          match uu____5359 with
          | (e,tag,t) ->
              let tag1 = maybe_downgrade_eff g tag t in
              if FStar_Extraction_ML_Util.eff_leq tag1 f
              then let uu____5378 = maybe_coerce g e t ty in (uu____5378, ty)
              else err_unexpected_eff e0 f tag1
and term_as_mlexpr':
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3
  =
  fun g  ->
    fun top  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____5396 =
             let uu____5397 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos in
             let uu____5398 = FStar_Syntax_Print.tag_of_term top in
             let uu____5399 = FStar_Syntax_Print.term_to_string top in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5397 uu____5398 uu____5399 in
           FStar_Util.print_string uu____5396);
      (let t = FStar_Syntax_Subst.compress top in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5407 =
             let uu____5408 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5408 in
           failwith uu____5407
       | FStar_Syntax_Syntax.Tm_delayed uu____5415 ->
           let uu____5444 =
             let uu____5445 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5445 in
           failwith uu____5444
       | FStar_Syntax_Syntax.Tm_uvar uu____5452 ->
           let uu____5473 =
             let uu____5474 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5474 in
           failwith uu____5473
       | FStar_Syntax_Syntax.Tm_bvar uu____5481 ->
           let uu____5482 =
             let uu____5483 = FStar_Syntax_Print.tag_of_term t in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5483 in
           failwith uu____5482
       | FStar_Syntax_Syntax.Tm_type uu____5490 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5491 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5500 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           let uu____5524 = term_as_mlexpr' g t1 in
           (match uu____5524 with
            | ({
                 FStar_Extraction_ML_Syntax.expr =
                   FStar_Extraction_ML_Syntax.MLE_Let
                   ((FStar_Extraction_ML_Syntax.NonRec ,flags,bodies),continuation);
                 FStar_Extraction_ML_Syntax.mlty = mlty;
                 FStar_Extraction_ML_Syntax.loc = loc;_},tag,typ)
                ->
                ({
                   FStar_Extraction_ML_Syntax.expr =
                     (FStar_Extraction_ML_Syntax.MLE_Let
                        ((FStar_Extraction_ML_Syntax.NonRec,
                           (FStar_Extraction_ML_Syntax.Mutable :: flags),
                           bodies), continuation));
                   FStar_Extraction_ML_Syntax.mlty = mlty;
                   FStar_Extraction_ML_Syntax.loc = loc
                 }, tag, typ)
            | uu____5570 -> failwith "impossible")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____5585)) ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____5627 =
                  let uu____5634 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m in
                  FStar_Util.must uu____5634 in
                (match uu____5627 with
                 | (ed,qualifiers) ->
                     let uu____5661 =
                       let uu____5662 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                       FStar_All.pipe_right uu____5662 Prims.op_Negation in
                     if uu____5661
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____5678 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5680) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5690) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____5700 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t in
           (match uu____5700 with
            | (uu____5713,ty,uu____5715) ->
                let ml_ty = term_as_mlty g ty in
                let uu____5717 =
                  let uu____5718 =
                    let uu____5719 =
                      FStar_Extraction_ML_Util.mlconst_of_const'
                        t.FStar_Syntax_Syntax.pos c in
                    FStar_All.pipe_left
                      (fun _0_42  ->
                         FStar_Extraction_ML_Syntax.MLE_Const _0_42)
                      uu____5719 in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5718 in
                (uu____5717, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____5720 ->
           let uu____5721 = is_type g t in
           if uu____5721
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5729 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____5729 with
              | (FStar_Util.Inl uu____5742,uu____5743) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5780,x,mltys,uu____5783),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5829 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____5829, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5830 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar uu____5837 ->
           let uu____5838 = is_type g t in
           if uu____5838
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5846 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu____5846 with
              | (FStar_Util.Inl uu____5859,uu____5860) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5897,x,mltys,uu____5900),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____5946 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu____5946, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____5947 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____5981 = FStar_Syntax_Subst.open_term bs body in
           (match uu____5981 with
            | (bs1,body1) ->
                let uu____5994 = binders_as_ml_binders g bs1 in
                (match uu____5994 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____6027 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c in
                           if uu____6027
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____6032  ->
                                 let uu____6033 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____6033);
                            body1) in
                     let uu____6034 = term_as_mlexpr env body2 in
                     (match uu____6034 with
                      | (ml_body,f,t1) ->
                          let uu____6050 =
                            FStar_List.fold_right
                              (fun uu____6069  ->
                                 fun uu____6070  ->
                                   match (uu____6069, uu____6070) with
                                   | ((uu____6091,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu____6050 with
                           | (f1,tfun) ->
                               let uu____6111 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu____6111, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6118);
              FStar_Syntax_Syntax.tk = uu____6119;
              FStar_Syntax_Syntax.pos = uu____6120;
              FStar_Syntax_Syntax.vars = uu____6121;_},uu____6122)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,uu____6158::(v1,uu____6160)::[])
           when (FStar_Syntax_Util.is_fstar_tactics_embed head1) && false ->
           let uu____6219 =
             let uu____6222 = FStar_Syntax_Print.term_to_string v1 in
             FStar_Util.format2 "Trying to extract a quotation of %s"
               uu____6222 in
           let s =
             let uu____6224 =
               let uu____6225 =
                 let uu____6226 =
                   let uu____6229 = FStar_Util.marshal v1 in
                   FStar_Util.bytes_of_string uu____6229 in
                 FStar_Extraction_ML_Syntax.MLC_Bytes uu____6226 in
               FStar_Extraction_ML_Syntax.MLE_Const uu____6225 in
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_string_ty uu____6224 in
           let zero1 =
             FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.ml_int_ty
               (FStar_Extraction_ML_Syntax.MLE_Const
                  (FStar_Extraction_ML_Syntax.MLC_Int
                     ("0", FStar_Pervasives_Native.None))) in
           let term_ty =
             let uu____6246 =
               FStar_Syntax_Syntax.fvar
                 FStar_Parser_Const.fstar_syntax_syntax_term
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             term_as_mlty g uu____6246 in
           let marshal_from_string =
             let string_to_term_ty =
               FStar_Extraction_ML_Syntax.MLTY_Fun
                 (FStar_Extraction_ML_Syntax.ml_string_ty,
                   FStar_Extraction_ML_Syntax.E_PURE, term_ty) in
             FStar_Extraction_ML_Syntax.with_ty string_to_term_ty
               (FStar_Extraction_ML_Syntax.MLE_Name
                  (["Marshal"], "from_string")) in
           let uu____6251 =
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty term_ty)
               (FStar_Extraction_ML_Syntax.MLE_App
                  (marshal_from_string, [s; zero1])) in
           (uu____6251, FStar_Extraction_ML_Syntax.E_PURE, term_ty)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___140_6291  ->
                        match uu___140_6291 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____6292 -> false))) in
           let uu____6293 =
             let uu____6298 =
               let uu____6299 = FStar_Syntax_Subst.compress head1 in
               uu____6299.FStar_Syntax_Syntax.n in
             ((head1.FStar_Syntax_Syntax.n), uu____6298) in
           (match uu____6293 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6310,uu____6311) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t in
                term_as_mlexpr' g t1
            | (uu____6333,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6335,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____6360,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6362 = FStar_List.hd args in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6362 in
                let tm =
                  let uu____6376 =
                    let uu____6377 = FStar_TypeChecker_Util.remove_reify e in
                    let uu____6378 = FStar_List.tl args in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6377 uu____6378 in
                  uu____6376 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos in
                term_as_mlexpr' g tm
            | uu____6389 ->
                let rec extract_app is_data uu____6434 uu____6435 restArgs =
                  match (uu____6434, uu____6435) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6525) ->
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
                                | uu____6547 -> false) in
                           let uu____6548 =
                             if evaluation_order_guaranteed
                             then
                               let uu____6573 =
                                 FStar_All.pipe_right
                                   (FStar_List.rev mlargs_f)
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ([], uu____6573)
                             else
                               FStar_List.fold_left
                                 (fun uu____6627  ->
                                    fun uu____6628  ->
                                      match (uu____6627, uu____6628) with
                                      | ((lbs,out_args),(arg,f1)) ->
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
                                             let uu____6731 =
                                               let uu____6734 =
                                                 FStar_All.pipe_left
                                                   (FStar_Extraction_ML_Syntax.with_ty
                                                      arg.FStar_Extraction_ML_Syntax.mlty)
                                                   (FStar_Extraction_ML_Syntax.MLE_Var
                                                      x) in
                                               uu____6734 :: out_args in
                                             (((x, arg) :: lbs), uu____6731)))
                                 ([], []) mlargs_f in
                           (match uu____6548 with
                            | (lbs,mlargs) ->
                                let app =
                                  let uu____6784 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty t1)
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (mlhead, mlargs)) in
                                  FStar_All.pipe_left
                                    (maybe_eta_data_and_project_record g
                                       is_data t1) uu____6784 in
                                let l_app =
                                  FStar_List.fold_right
                                    (fun uu____6796  ->
                                       fun out  ->
                                         match uu____6796 with
                                         | (x,arg) ->
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  out.FStar_Extraction_ML_Syntax.mlty)
                                               (mk_MLE_Let false
                                                  (FStar_Extraction_ML_Syntax.NonRec,
                                                    [],
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
                                                       FStar_Extraction_ML_Syntax.print_typ
                                                         = true
                                                     }]) out)) lbs app in
                                (l_app, f, t1))
                       | ((arg,uu____6817)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____6848 =
                             let uu____6853 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f' in
                             (uu____6853, t2) in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____6848 rest
                       | ((e0,uu____6865)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos in
                           let uu____6897 = term_as_mlexpr g e0 in
                           (match uu____6897 with
                            | (e01,f0,tInferred) ->
                                let e02 =
                                  maybe_coerce g e01 tInferred tExpected in
                                let uu____6914 =
                                  let uu____6919 =
                                    FStar_Extraction_ML_Util.join_l r
                                      [f; f'; f0] in
                                  (uu____6919, t2) in
                                extract_app is_data
                                  (mlhead, ((e02, f0) :: mlargs_f))
                                  uu____6914 rest)
                       | uu____6930 ->
                           let uu____6943 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1 in
                           (match uu____6943 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                err_ill_typed_application g top restArgs t1)) in
                let extract_app_maybe_projector is_data mlhead uu____7002
                  args1 =
                  match uu____7002 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____7036)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____7124))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____7126,f',t3)) ->
                                 let uu____7173 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu____7173 t3
                             | uu____7174 -> (args2, f1, t2) in
                           let uu____7203 = remove_implicits args1 f t1 in
                           (match uu____7203 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____7265 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let uu____7278 = is_type g t in
                if uu____7278
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let head2 = FStar_Syntax_Util.un_uinst head1 in
                   match head2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_fvar fv when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.fstar_refl_embed_lid)
                         &&
                         (let uu____7295 =
                            let uu____7296 =
                              FStar_Extraction_ML_Syntax.string_of_mlpath
                                g.FStar_Extraction_ML_UEnv.currentModule in
                            uu____7296 = "FStar.Tactics.Builtins" in
                          Prims.op_Negation uu____7295)
                       ->
                       (match args with
                        | a::b::[] ->
                            term_as_mlexpr g (FStar_Pervasives_Native.fst a)
                        | uu____7349 ->
                            let uu____7360 =
                              FStar_Syntax_Print.args_to_string args in
                            failwith uu____7360)
                   | FStar_Syntax_Syntax.Tm_name uu____7367 ->
                       let uu____7368 =
                         let uu____7381 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____7381 with
                         | (FStar_Util.Inr (uu____7400,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7445 -> failwith "FIXME Ty" in
                       (match uu____7368 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7495)::uu____7496 -> is_type g a
                              | uu____7523 -> false in
                            let uu____7534 =
                              match vars with
                              | uu____7567::uu____7568 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____7581 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____7613 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____7613 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____7718  ->
                                                match uu____7718 with
                                                | (x,uu____7724) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____7727 ->
                                               let uu___144_7728 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_7728.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_7728.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____7729 ->
                                               let uu___144_7730 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_7730.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_7730.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____7732;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____7733;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___145_7739 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___145_7739.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___145_7739.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____7740 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____7534 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____7811 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____7811,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____7812 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | FStar_Syntax_Syntax.Tm_fvar uu____7823 ->
                       let uu____7824 =
                         let uu____7837 =
                           FStar_Extraction_ML_UEnv.lookup_term g head2 in
                         match uu____7837 with
                         | (FStar_Util.Inr (uu____7856,x1,x2,x3),q) ->
                             ((x1, x2, x3), q)
                         | uu____7901 -> failwith "FIXME Ty" in
                       (match uu____7824 with
                        | ((head_ml,(vars,t1),inst_ok),qual) ->
                            let has_typ_apps =
                              match args with
                              | (a,uu____7951)::uu____7952 -> is_type g a
                              | uu____7979 -> false in
                            let uu____7990 =
                              match vars with
                              | uu____8023::uu____8024 when
                                  (Prims.op_Negation has_typ_apps) && inst_ok
                                  -> (head_ml, t1, args)
                              | uu____8037 ->
                                  let n1 = FStar_List.length vars in
                                  if n1 <= (FStar_List.length args)
                                  then
                                    let uu____8069 =
                                      FStar_Util.first_N n1 args in
                                    (match uu____8069 with
                                     | (prefix1,rest) ->
                                         let prefixAsMLTypes =
                                           FStar_List.map
                                             (fun uu____8174  ->
                                                match uu____8174 with
                                                | (x,uu____8180) ->
                                                    term_as_mlty g x) prefix1 in
                                         let t2 =
                                           instantiate (vars, t1)
                                             prefixAsMLTypes in
                                         let head3 =
                                           match head_ml.FStar_Extraction_ML_Syntax.expr
                                           with
                                           | FStar_Extraction_ML_Syntax.MLE_Name
                                               uu____8183 ->
                                               let uu___144_8184 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_8184.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_8184.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_Var
                                               uu____8185 ->
                                               let uu___144_8186 = head_ml in
                                               {
                                                 FStar_Extraction_ML_Syntax.expr
                                                   =
                                                   (uu___144_8186.FStar_Extraction_ML_Syntax.expr);
                                                 FStar_Extraction_ML_Syntax.mlty
                                                   = t2;
                                                 FStar_Extraction_ML_Syntax.loc
                                                   =
                                                   (uu___144_8186.FStar_Extraction_ML_Syntax.loc)
                                               }
                                           | FStar_Extraction_ML_Syntax.MLE_App
                                               (head3,{
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          FStar_Extraction_ML_Syntax.MLE_Const
                                                          (FStar_Extraction_ML_Syntax.MLC_Unit
                                                          );
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          = uu____8188;
                                                        FStar_Extraction_ML_Syntax.loc
                                                          = uu____8189;_}::[])
                                               ->
                                               FStar_All.pipe_right
                                                 (FStar_Extraction_ML_Syntax.MLE_App
                                                    ((let uu___145_8195 =
                                                        head3 in
                                                      {
                                                        FStar_Extraction_ML_Syntax.expr
                                                          =
                                                          (uu___145_8195.FStar_Extraction_ML_Syntax.expr);
                                                        FStar_Extraction_ML_Syntax.mlty
                                                          =
                                                          (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                             (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                               FStar_Extraction_ML_Syntax.E_PURE,
                                                               t2));
                                                        FStar_Extraction_ML_Syntax.loc
                                                          =
                                                          (uu___145_8195.FStar_Extraction_ML_Syntax.loc)
                                                      }),
                                                      [FStar_Extraction_ML_Syntax.ml_unit]))
                                                 (FStar_Extraction_ML_Syntax.with_ty
                                                    t2)
                                           | uu____8196 ->
                                               failwith
                                                 "Impossible: Unexpected head term" in
                                         (head3, t2, rest))
                                  else err_uninst g head2 (vars, t1) top in
                            (match uu____7990 with
                             | (head_ml1,head_t,args1) ->
                                 (match args1 with
                                  | [] ->
                                      let uu____8267 =
                                        maybe_eta_data_and_project_record g
                                          qual head_t head_ml1 in
                                      (uu____8267,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        head_t)
                                  | uu____8268 ->
                                      extract_app_maybe_projector qual
                                        head_ml1
                                        (FStar_Extraction_ML_Syntax.E_PURE,
                                          head_t) args1)))
                   | uu____8279 ->
                       let uu____8280 = term_as_mlexpr g head2 in
                       (match uu____8280 with
                        | (head3,f,t1) ->
                            extract_app_maybe_projector
                              FStar_Pervasives_Native.None head3 (f, t1) args)))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____8298),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c) in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l in
           let uu____8399 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu____8399 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu____8434 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8448 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu____8448
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs in
                   let x =
                     let uu____8464 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu____8464 in
                   let lb1 =
                     let uu___146_8466 = lb in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___146_8466.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___146_8466.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___146_8466.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___146_8466.FStar_Syntax_Syntax.lbdef)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e' in
                   ([lb1], e'1))) in
           (match uu____8434 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8498 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8498 in
                            FStar_Extraction_ML_UEnv.debug g
                              (fun uu____8505  ->
                                 FStar_Options.set_option "debug_level"
                                   (FStar_Options.List
                                      [FStar_Options.String "Norm";
                                      FStar_Options.String "Extraction"]));
                            (let lbdef =
                               let uu____8511 = FStar_Options.ml_ish () in
                               if uu____8511
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
                             let uu___147_8517 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___147_8517.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___147_8517.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___147_8517.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___147_8517.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })))
                  else lbs1 in
                let maybe_generalize uu____8540 =
                  match uu____8540 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8560;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;_} ->
                      let f_e = effect_as_etag g lbeff in
                      let t2 = FStar_Syntax_Subst.compress t1 in
                      (match t2.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                           let uu____8638 = FStar_List.hd bs in
                           FStar_All.pipe_right uu____8638 (is_type_binder g)
                           ->
                           let uu____8651 = FStar_Syntax_Subst.open_comp bs c in
                           (match uu____8651 with
                            | (bs1,c1) ->
                                let uu____8676 =
                                  let uu____8685 =
                                    FStar_Util.prefix_until
                                      (fun x  ->
                                         let uu____8721 = is_type_binder g x in
                                         Prims.op_Negation uu____8721) bs1 in
                                  match uu____8685 with
                                  | FStar_Pervasives_Native.None  ->
                                      (bs1,
                                        (FStar_Syntax_Util.comp_result c1))
                                  | FStar_Pervasives_Native.Some (bs2,b,rest)
                                      ->
                                      let uu____8813 =
                                        FStar_Syntax_Util.arrow (b :: rest)
                                          c1 in
                                      (bs2, uu____8813) in
                                (match uu____8676 with
                                 | (tbinders,tbody) ->
                                     let n_tbinders =
                                       FStar_List.length tbinders in
                                     let e1 =
                                       let uu____8866 = normalize_abs e in
                                       FStar_All.pipe_right uu____8866
                                         FStar_Syntax_Util.unmeta in
                                     (match e1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_abs
                                          (bs2,body,copt) ->
                                          let uu____8912 =
                                            FStar_Syntax_Subst.open_term bs2
                                              body in
                                          (match uu____8912 with
                                           | (bs3,body1) ->
                                               if
                                                 n_tbinders <=
                                                   (FStar_List.length bs3)
                                               then
                                                 let uu____8965 =
                                                   FStar_Util.first_N
                                                     n_tbinders bs3 in
                                                 (match uu____8965 with
                                                  | (targs,rest_args) ->
                                                      let expected_source_ty
                                                        =
                                                        let s =
                                                          FStar_List.map2
                                                            (fun uu____9053 
                                                               ->
                                                               fun uu____9054
                                                                  ->
                                                                 match 
                                                                   (uu____9053,
                                                                    uu____9054)
                                                                 with
                                                                 | ((x,uu____9072),
                                                                    (y,uu____9074))
                                                                    ->
                                                                    let uu____9083
                                                                    =
                                                                    let uu____9092
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y in
                                                                    (x,
                                                                    uu____9092) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9083)
                                                            tbinders targs in
                                                        FStar_Syntax_Subst.subst
                                                          s tbody in
                                                      let env =
                                                        FStar_List.fold_left
                                                          (fun env  ->
                                                             fun uu____9103 
                                                               ->
                                                               match uu____9103
                                                               with
                                                               | (a,uu____9109)
                                                                   ->
                                                                   FStar_Extraction_ML_UEnv.extend_ty
                                                                    env a
                                                                    FStar_Pervasives_Native.None)
                                                          g targs in
                                                      let expected_t =
                                                        term_as_mlty env
                                                          expected_source_ty in
                                                      let polytype =
                                                        let uu____9122 =
                                                          FStar_All.pipe_right
                                                            targs
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____9152 
                                                                  ->
                                                                  match uu____9152
                                                                  with
                                                                  | (x,uu____9162)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x)) in
                                                        (uu____9122,
                                                          expected_t) in
                                                      let add_unit =
                                                        match rest_args with
                                                        | [] ->
                                                            let uu____9174 =
                                                              is_fstar_value
                                                                body1 in
                                                            Prims.op_Negation
                                                              uu____9174
                                                        | uu____9175 -> false in
                                                      let rest_args1 =
                                                        if add_unit
                                                        then unit_binder ::
                                                          rest_args
                                                        else rest_args in
                                                      let body2 =
                                                        match rest_args1 with
                                                        | [] -> body1
                                                        | uu____9189 ->
                                                            FStar_Syntax_Util.abs
                                                              rest_args1
                                                              body1 copt in
                                                      (lbname_, f_e,
                                                        (t2,
                                                          (targs, polytype)),
                                                        add_unit, body2))
                                               else
                                                 failwith
                                                   "Not enough type binders")
                                      | FStar_Syntax_Syntax.Tm_uinst
                                          uu____9275 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____9294  ->
                                                   match uu____9294 with
                                                   | (a,uu____9300) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____9313 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9337  ->
                                                      match uu____9337 with
                                                      | (x,uu____9347) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____9313, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9367  ->
                                                    match uu____9367 with
                                                    | (bv,uu____9373) ->
                                                        let uu____9374 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____9374
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
                                          uu____9432 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____9443  ->
                                                   match uu____9443 with
                                                   | (a,uu____9449) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____9462 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9486  ->
                                                      match uu____9486 with
                                                      | (x,uu____9496) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____9462, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9516  ->
                                                    match uu____9516 with
                                                    | (bv,uu____9522) ->
                                                        let uu____9523 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            bv in
                                                        FStar_All.pipe_right
                                                          uu____9523
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
                                          uu____9581 ->
                                          let env =
                                            FStar_List.fold_left
                                              (fun env  ->
                                                 fun uu____9592  ->
                                                   match uu____9592 with
                                                   | (a,uu____9598) ->
                                                       FStar_Extraction_ML_UEnv.extend_ty
                                                         env a
                                                         FStar_Pervasives_Native.None)
                                              g tbinders in
                                          let expected_t =
                                            term_as_mlty env tbody in
                                          let polytype =
                                            let uu____9611 =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9635  ->
                                                      match uu____9635 with
                                                      | (x,uu____9645) ->
                                                          FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                            x)) in
                                            (uu____9611, expected_t) in
                                          let args =
                                            FStar_All.pipe_right tbinders
                                              (FStar_List.map
                                                 (fun uu____9665  ->
                                                    match uu____9665 with
                                                    | (bv,uu____9671) ->
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
                                      | uu____9730 ->
                                          err_value_restriction e1)))
                       | uu____9749 ->
                           let expected_t = term_as_mlty g t2 in
                           (lbname_, f_e, (t2, ([], ([], expected_t))),
                             false, e)) in
                let check_lb env uu____9855 =
                  match uu____9855 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9990  ->
                               match uu____9990 with
                               | (a,uu____9996) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs in
                      let expected_t =
                        if add_unit
                        then
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              (FStar_Pervasives_Native.snd polytype))
                        else FStar_Pervasives_Native.snd polytype in
                      let uu____9999 =
                        check_term_as_mlexpr env1 e f expected_t in
                      (match uu____9999 with
                       | (e1,uu____10009) ->
                           let f1 = maybe_downgrade_eff env1 f expected_t in
                           (f1,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (FStar_Pervasives_Native.Some polytype);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e1;
                               FStar_Extraction_ML_Syntax.print_typ = true
                             })) in
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize) in
                let uu____10076 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____10167  ->
                         match uu____10167 with
                         | (env,lbs4) ->
                             let uu____10292 = lb in
                             (match uu____10292 with
                              | (lbname,uu____10340,(t1,(uu____10342,polytype)),add_unit,uu____10345)
                                  ->
                                  let uu____10358 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true in
                                  (match uu____10358 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, []) in
                (match uu____10076 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu____10635 = term_as_mlexpr env_body e'1 in
                     (match uu____10635 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____10652 =
                              let uu____10655 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5 in
                              f' :: uu____10655 in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10652 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu____10664 =
                            let uu____10665 =
                              let uu____10666 =
                                let uu____10667 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5 in
                                (is_rec1, [], uu____10667) in
                              mk_MLE_Let top_level uu____10666 e'2 in
                            let uu____10678 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10665 uu____10678 in
                          (uu____10664, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10729 = term_as_mlexpr g scrutinee in
           (match uu____10729 with
            | (e,f_e,t_e) ->
                let uu____10745 = check_pats_for_ite pats in
                (match uu____10745 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10802 = term_as_mlexpr g then_e1 in
                            (match uu____10802 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10818 = term_as_mlexpr g else_e1 in
                                 (match uu____10818 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10834 =
                                        let uu____10843 =
                                          type_leq g t_then t_else in
                                        if uu____10843
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10857 =
                                             type_leq g t_else t_then in
                                           if uu____10857
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu____10834 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10891 =
                                             let uu____10892 =
                                               let uu____10893 =
                                                 let uu____10902 =
                                                   maybe_lift1 then_mle
                                                     t_then in
                                                 let uu____10903 =
                                                   let uu____10906 =
                                                     maybe_lift1 else_mle
                                                       t_else in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10906 in
                                                 (e, uu____10902,
                                                   uu____10903) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10893 in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10892 in
                                           let uu____10909 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu____10891, uu____10909,
                                             t_branch))))
                        | uu____10910 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10926 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____11039 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu____11039 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____11091 =
                                          extract_pat g pat t_e in
                                        (match uu____11091 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____11149 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let uu____11177 =
                                                     term_as_mlexpr env w in
                                                   (match uu____11177 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w)) in
                                             (match uu____11149 with
                                              | (when_opt1,f_when) ->
                                                  let uu____11226 =
                                                    term_as_mlexpr env
                                                      branch1 in
                                                  (match uu____11226 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____11260 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____11337 
                                                                 ->
                                                                 match uu____11337
                                                                 with
                                                                 | (p1,wopt)
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
                                                         uu____11260)))))
                               true) in
                        match uu____10926 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____11502  ->
                                      let uu____11503 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e in
                                      let uu____11504 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____11503 uu____11504);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____11529 =
                                   let uu____11538 =
                                     let uu____11555 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____11555 in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____11538 in
                                 (match uu____11529 with
                                  | (uu____11598,fw,uu____11600,uu____11601)
                                      ->
                                      let uu____11602 =
                                        let uu____11603 =
                                          let uu____11604 =
                                            let uu____11611 =
                                              let uu____11614 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu____11614] in
                                            (fw, uu____11611) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11604 in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_unit_ty)
                                          uu____11603 in
                                      (uu____11602,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_unit_ty))
                             | (uu____11617,uu____11618,(uu____11619,f_first,t_first))::rest
                                 ->
                                 let uu____11679 =
                                   FStar_List.fold_left
                                     (fun uu____11721  ->
                                        fun uu____11722  ->
                                          match (uu____11721, uu____11722)
                                          with
                                          | ((topt,f),(uu____11779,uu____11780,
                                                       (uu____11781,f_branch,t_branch)))
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
                                                    let uu____11837 =
                                                      type_leq g t1 t_branch in
                                                    if uu____11837
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11841 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu____11841
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           t1
                                                       else
                                                         FStar_Pervasives_Native.None) in
                                              (topt1, f1))
                                     ((FStar_Pervasives_Native.Some t_first),
                                       f_first) rest in
                                 (match uu____11679 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11936  ->
                                                match uu____11936 with
                                                | (p,(wopt,uu____11965),
                                                   (b1,uu____11967,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11986 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | FStar_Pervasives_Native.Some t1 ->
                                            t1 in
                                      let uu____11991 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu____11991, f_match, t_match)))))))
let fresh:
  Prims.string -> (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2 =
  let c = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun x  ->
    FStar_Util.incr c;
    (let uu____12017 = FStar_ST.read c in (x, uu____12017))
let ind_discriminator_body:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____12032 =
          let uu____12037 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12037 in
        match uu____12032 with
        | (uu____12062,fstar_disc_type) ->
            let wildcards =
              let uu____12075 =
                let uu____12076 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu____12076.FStar_Syntax_Syntax.n in
              match uu____12075 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____12092) ->
                  let uu____12113 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___141_12145  ->
                            match uu___141_12145 with
                            | (uu____12152,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____12153)) ->
                                true
                            | uu____12156 -> false)) in
                  FStar_All.pipe_right uu____12113
                    (FStar_List.map
                       (fun uu____12197  ->
                          let uu____12204 = fresh "_" in
                          (uu____12204, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____12213 -> failwith "Discriminator must be a function" in
            let mlid = fresh "_discr_" in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
            let discrBody =
              let uu____12232 =
                let uu____12233 =
                  let uu____12244 =
                    let uu____12245 =
                      let uu____12246 =
                        let uu____12261 =
                          let uu____12262 =
                            let uu____12263 =
                              let uu____12264 =
                                FStar_Extraction_ML_Syntax.idsym mlid in
                              ([], uu____12264) in
                            FStar_Extraction_ML_Syntax.MLE_Name uu____12263 in
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            uu____12262 in
                        let uu____12267 =
                          let uu____12278 =
                            let uu____12287 =
                              let uu____12288 =
                                let uu____12295 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName in
                                (uu____12295,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____12288 in
                            let uu____12298 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true)) in
                            (uu____12287, FStar_Pervasives_Native.None,
                              uu____12298) in
                          let uu____12301 =
                            let uu____12312 =
                              let uu____12321 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false)) in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____12321) in
                            [uu____12312] in
                          uu____12278 :: uu____12301 in
                        (uu____12261, uu____12267) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____12246 in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____12245 in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____12244) in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____12233 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____12232 in
            let uu____12396 =
              let uu____12397 =
                let uu____12400 =
                  let uu____12401 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____12401;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.print_typ = false
                  } in
                [uu____12400] in
              (FStar_Extraction_ML_Syntax.NonRec, [], uu____12397) in
            FStar_Extraction_ML_Syntax.MLM_Let uu____12396