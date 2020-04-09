open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____8 -> false
  
let (type_leq :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
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
  fun g  ->
    fun t1  ->
      fun t2  ->
        FStar_Extraction_ML_Util.type_leq_c
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
  
let (eraseTypeDeep :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      FStar_Extraction_ML_Util.eraseTypeDeep
        (FStar_Extraction_ML_Util.udelta_unfold g) t
  
let fail :
  'Auu____77 .
    FStar_Range.range ->
      (FStar_Errors.raw_error * Prims.string) -> 'Auu____77
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_ill_typed_application :
  'Auu____113 'Auu____114 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'Auu____113) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'Auu____114
  =
  fun env  ->
    fun t  ->
      fun mlhead  ->
        fun args  ->
          fun ty  ->
            let uu____152 =
              let uu____158 =
                let uu____160 = FStar_Syntax_Print.term_to_string t  in
                let uu____162 =
                  let uu____164 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
                  FStar_Extraction_ML_Code.string_of_mlexpr uu____164 mlhead
                   in
                let uu____165 =
                  let uu____167 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
                  FStar_Extraction_ML_Code.string_of_mlty uu____167 ty  in
                let uu____168 =
                  let uu____170 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____191  ->
                            match uu____191 with
                            | (x,uu____198) ->
                                FStar_Syntax_Print.term_to_string x))
                     in
                  FStar_All.pipe_right uu____170 (FStar_String.concat " ")
                   in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____160 uu____162 uu____165 uu____168
                 in
              (FStar_Errors.Fatal_IllTyped, uu____158)  in
            fail t.FStar_Syntax_Syntax.pos uu____152
  
let err_ill_typed_erasure :
  'Auu____215 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____215
  =
  fun env  ->
    fun pos  ->
      fun ty  ->
        let uu____231 =
          let uu____237 =
            let uu____239 =
              let uu____241 =
                FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
              FStar_Extraction_ML_Code.string_of_mlty uu____241 ty  in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____239
             in
          (FStar_Errors.Fatal_IllTyped, uu____237)  in
        fail pos uu____231
  
let err_value_restriction :
  'Auu____249 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____249
  =
  fun t  ->
    let uu____259 =
      let uu____265 =
        let uu____267 = FStar_Syntax_Print.tag_of_term t  in
        let uu____269 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____267 uu____269
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____265)  in
    fail t.FStar_Syntax_Syntax.pos uu____259
  
let (err_unexpected_eff :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.e_tag ->
          FStar_Extraction_ML_Syntax.e_tag -> unit)
  =
  fun env  ->
    fun t  ->
      fun ty  ->
        fun f0  ->
          fun f1  ->
            let uu____303 =
              let uu____309 =
                let uu____311 = FStar_Syntax_Print.term_to_string t  in
                let uu____313 =
                  let uu____315 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
                  FStar_Extraction_ML_Code.string_of_mlty uu____315 ty  in
                let uu____316 = FStar_Extraction_ML_Util.eff_to_string f0  in
                let uu____318 = FStar_Extraction_ML_Util.eff_to_string f1  in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____311 uu____313 uu____316 uu____318
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____309)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____303
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.of_int (20))  in
  let rec delta_norm_eff g l =
    let uu____346 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____346 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____351 =
            let uu____358 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
            FStar_TypeChecker_Env.lookup_effect_abbrev uu____358
              [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____351 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____363,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____373 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____373
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____378 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____378
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              let uu____392 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Env.effect_decl_opt uu____392 l1  in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____405 =
                  let uu____407 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_Env.is_reifiable_effect uu____407
                    ed.FStar_Syntax_Syntax.mname
                   in
                if uu____405
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____430 =
        let uu____431 = FStar_Syntax_Subst.compress t1  in
        uu____431.FStar_Syntax_Syntax.n  in
      match uu____430 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____437 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____454 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____483 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____493 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____493
      | FStar_Syntax_Syntax.Tm_uvar uu____494 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____508 -> false
      | FStar_Syntax_Syntax.Tm_name uu____510 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____512 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____520 -> false
      | FStar_Syntax_Syntax.Tm_type uu____522 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____524,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let topt =
            let uu____554 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] uu____554
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match topt with
           | FStar_Pervasives_Native.None  -> false
           | FStar_Pervasives_Native.Some (uu____561,t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____567 ->
          let uu____584 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____584 with | (head1,uu____603) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____629) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____635) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____640,body,uu____642) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____667,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____687,branches) ->
          (match branches with
           | (uu____726,uu____727,e)::uu____729 -> is_arity env e
           | uu____776 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____808 ->
          let uu____823 =
            let uu____825 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____825  in
          failwith uu____823
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____829 =
            let uu____831 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____831  in
          failwith uu____829
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____836 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____836
      | FStar_Syntax_Syntax.Tm_constant uu____837 -> false
      | FStar_Syntax_Syntax.Tm_type uu____839 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____841 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____849 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____868;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____869;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____870;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____872;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____873;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____874;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____875;_},s)
          ->
          let uu____924 = FStar_Syntax_Subst.subst' s t2  in
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
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____938,uu____939) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____981) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____988) ->
          let uu____1013 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____1013 with
           | (uu____1019,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____1039 =
            let uu____1044 =
              let uu____1045 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1045]  in
            FStar_Syntax_Subst.open_term uu____1044 body  in
          (match uu____1039 with
           | (uu____1065,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1067,lbs),body) ->
          let uu____1087 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____1087 with
           | (uu____1095,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1101,branches) ->
          (match branches with
           | b::uu____1141 ->
               let uu____1186 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1186 with
                | (uu____1188,uu____1189,e) -> is_type_aux env e)
           | uu____1207 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1225 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1234) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1240) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1281  ->
           let uu____1282 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1284 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1282
             uu____1284);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1293  ->
            if b
            then
              let uu____1295 = FStar_Syntax_Print.term_to_string t  in
              let uu____1297 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1295
                uu____1297
            else
              (let uu____1302 = FStar_Syntax_Print.term_to_string t  in
               let uu____1304 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1302 uu____1304));
       b)
  
let is_type_binder :
  'Auu____1314 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____1314) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1341 =
      let uu____1342 = FStar_Syntax_Subst.compress t  in
      uu____1342.FStar_Syntax_Syntax.n  in
    match uu____1341 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1346;
          FStar_Syntax_Syntax.fv_delta = uu____1347;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1349;
          FStar_Syntax_Syntax.fv_delta = uu____1350;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1351);_}
        -> true
    | uu____1359 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1368 =
      let uu____1369 = FStar_Syntax_Subst.compress t  in
      uu____1369.FStar_Syntax_Syntax.n  in
    match uu____1368 with
    | FStar_Syntax_Syntax.Tm_constant uu____1373 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1375 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1377 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1379 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1425 = is_constructor head1  in
        if uu____1425
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1447  ->
                  match uu____1447 with
                  | (te,uu____1456) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1465) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1471,uu____1472) ->
        is_fstar_value t1
    | uu____1513 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1523 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1525 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1528 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1530 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1543,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1552,fields) ->
        FStar_Util.for_all
          (fun uu____1582  ->
             match uu____1582 with | (uu____1589,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1594) -> is_ml_value h
    | uu____1599 -> false
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1681 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1683 = FStar_Syntax_Util.is_fun e'  in
          if uu____1683
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : unit -> FStar_Syntax_Syntax.binder) =
  fun uu____1701  ->
    let uu____1702 =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.t_unit
       in
    FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1702
  
let (check_pats_for_ite :
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list ->
    (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option))
  =
  fun l  ->
    let def =
      (false, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)  in
    if (FStar_List.length l) <> (Prims.of_int (2))
    then def
    else
      (let uu____1793 = FStar_List.hd l  in
       match uu____1793 with
       | (p1,w1,e1) ->
           let uu____1828 =
             let uu____1837 = FStar_List.tl l  in FStar_List.hd uu____1837
              in
           (match uu____1828 with
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
                 | uu____1921 -> def)))
  
let (instantiate_tyscheme :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  = fun s  -> fun args  -> FStar_Extraction_ML_Util.subst s args 
let (fresh_mlidents :
  FStar_Extraction_ML_Syntax.mlty Prims.list ->
    FStar_Extraction_ML_UEnv.uenv ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun ts  ->
    fun g  ->
      let uu____1986 =
        FStar_List.fold_right
          (fun t  ->
             fun uu____2017  ->
               match uu____2017 with
               | (uenv,vs) ->
                   let uu____2056 = FStar_Extraction_ML_UEnv.new_mlident uenv
                      in
                   (match uu____2056 with
                    | (uenv1,v1) -> (uenv1, ((v1, t) :: vs)))) ts (g, [])
         in
      match uu____1986 with | (g1,vs_ts) -> (vs_ts, g1)
  
let (instantiate_maybe_partial :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        FStar_Extraction_ML_Syntax.mlty Prims.list ->
          (FStar_Extraction_ML_Syntax.mlexpr *
            FStar_Extraction_ML_Syntax.e_tag *
            FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      fun s  ->
        fun tyargs  ->
          let uu____2173 = s  in
          match uu____2173 with
          | (vars,t) ->
              let n_vars = FStar_List.length vars  in
              let n_args = FStar_List.length tyargs  in
              if n_args = n_vars
              then
                (if n_args = Prims.int_zero
                 then (e, FStar_Extraction_ML_Syntax.E_PURE, t)
                 else
                   (let ts = instantiate_tyscheme (vars, t) tyargs  in
                    let tapp =
                      let uu___372_2205 = e  in
                      {
                        FStar_Extraction_ML_Syntax.expr =
                          (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                        FStar_Extraction_ML_Syntax.mlty = ts;
                        FStar_Extraction_ML_Syntax.loc =
                          (uu___372_2205.FStar_Extraction_ML_Syntax.loc)
                      }  in
                    (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
              else
                if n_args < n_vars
                then
                  (let extra_tyargs =
                     let uu____2220 = FStar_Util.first_N n_args vars  in
                     match uu____2220 with
                     | (uu____2234,rest_vars) ->
                         FStar_All.pipe_right rest_vars
                           (FStar_List.map
                              (fun uu____2255  ->
                                 FStar_Extraction_ML_Syntax.MLTY_Erased))
                      in
                   let tyargs1 = FStar_List.append tyargs extra_tyargs  in
                   let ts = instantiate_tyscheme (vars, t) tyargs1  in
                   let tapp =
                     let uu___383_2262 = e  in
                     {
                       FStar_Extraction_ML_Syntax.expr =
                         (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                       FStar_Extraction_ML_Syntax.mlty = ts;
                       FStar_Extraction_ML_Syntax.loc =
                         (uu___383_2262.FStar_Extraction_ML_Syntax.loc)
                     }  in
                   let t1 =
                     FStar_List.fold_left
                       (fun out  ->
                          fun t1  ->
                            FStar_Extraction_ML_Syntax.MLTY_Fun
                              (t1, FStar_Extraction_ML_Syntax.E_PURE, out))
                       ts extra_tyargs
                      in
                   let uu____2270 = fresh_mlidents extra_tyargs g  in
                   match uu____2270 with
                   | (vs_ts,g1) ->
                       let f =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty t1)
                           (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, tapp))
                          in
                       (f, FStar_Extraction_ML_Syntax.E_PURE, t1))
                else
                  failwith
                    "Impossible: instantiate_maybe_partial called with too many arguments"
  
let (eta_expand :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g  ->
    fun t  ->
      fun e  ->
        let uu____2337 = FStar_Extraction_ML_Util.doms_and_cod t  in
        match uu____2337 with
        | (ts,r) ->
            if ts = []
            then e
            else
              (let uu____2355 = fresh_mlidents ts g  in
               match uu____2355 with
               | (vs_ts,g1) ->
                   let vs_es =
                     FStar_List.map
                       (fun uu____2394  ->
                          match uu____2394 with
                          | (v1,t1) ->
                              FStar_Extraction_ML_Syntax.with_ty t1
                                (FStar_Extraction_ML_Syntax.MLE_Var v1))
                       vs_ts
                      in
                   let body =
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty r)
                       (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es))
                      in
                   FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
                     (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
  
let (default_value_for_ty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g  ->
    fun t  ->
      let uu____2425 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2425 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____2445 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____2445 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2449 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let uu____2455 = fresh_mlidents ts g  in
             match uu____2455 with
             | (vs_ts,g1) ->
                 let uu____2483 =
                   let uu____2484 =
                     let uu____2496 = body r  in (vs_ts, uu____2496)  in
                   FStar_Extraction_ML_Syntax.MLE_Fun uu____2484  in
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
                   uu____2483)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g  ->
    fun expect  ->
      fun e  ->
        let uu____2520 =
          (FStar_Options.ml_no_eta_expand_coertions ()) ||
            (let uu____2523 = FStar_Options.codegen ()  in
             uu____2523 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
           in
        if uu____2520 then e else eta_expand g expect e
  
let (apply_coercion :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g  ->
    fun e  ->
      fun ty  ->
        fun expect  ->
          let mk_fun binder body =
            match body.FStar_Extraction_ML_Syntax.expr with
            | FStar_Extraction_ML_Syntax.MLE_Fun (binders,body1) ->
                FStar_Extraction_ML_Syntax.MLE_Fun
                  ((binder :: binders), body1)
            | uu____2601 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____2656 =
              match uu____2656 with
              | (pat,w,b) ->
                  let uu____2680 = aux b ty1 expect1  in (pat, w, uu____2680)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____2687,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____2690,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____2722 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____2738 = type_leq g s0 t0  in
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
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____2753, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____2746  in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____2745  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____2744;
                       FStar_Extraction_ML_Syntax.mllb_meta = [];
                       FStar_Extraction_ML_Syntax.print_typ = false
                     }  in
                   let body3 =
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty s1)
                       (FStar_Extraction_ML_Syntax.MLE_Let
                          ((FStar_Extraction_ML_Syntax.NonRec, [lb]), body2))
                      in
                   FStar_Extraction_ML_Syntax.with_ty expect1
                     (mk_fun ((FStar_Pervasives_Native.fst arg), s0) body3))
            | (FStar_Extraction_ML_Syntax.MLE_Let
               (lbs,body),uu____2772,uu____2773) ->
                let uu____2786 =
                  let uu____2787 =
                    let uu____2798 = aux body ty1 expect1  in
                    (lbs, uu____2798)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____2787  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2786
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____2807,uu____2808) ->
                let uu____2829 =
                  let uu____2830 =
                    let uu____2845 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2845)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____2830  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2829
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____2885,uu____2886) ->
                let uu____2891 =
                  let uu____2892 =
                    let uu____2901 = aux b1 ty1 expect1  in
                    let uu____2902 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____2901, uu____2902)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____2892  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2891
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____2910,uu____2911)
                ->
                let uu____2914 = FStar_Util.prefix es  in
                (match uu____2914 with
                 | (prefix1,last1) ->
                     let uu____2927 =
                       let uu____2928 =
                         let uu____2931 =
                           let uu____2934 = aux last1 ty1 expect1  in
                           [uu____2934]  in
                         FStar_List.append prefix1 uu____2931  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____2928  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____2927)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____2937,uu____2938) ->
                let uu____2959 =
                  let uu____2960 =
                    let uu____2975 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2975)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____2960  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2959
            | uu____3012 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'Auu____3032 .
    'Auu____3032 ->
      FStar_Extraction_ML_UEnv.uenv ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          FStar_Extraction_ML_Syntax.mlty ->
            FStar_Extraction_ML_Syntax.mlty ->
              FStar_Extraction_ML_Syntax.mlexpr
  =
  fun pos  ->
    fun g  ->
      fun e  ->
        fun ty  ->
          fun expect  ->
            let ty1 = eraseTypeDeep g ty  in
            let uu____3059 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____3059 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____3072 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____3080 ->
                     let uu____3081 =
                       let uu____3083 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____3084 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____3083 uu____3084  in
                     if uu____3081
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3090  ->
                             let uu____3091 =
                               let uu____3093 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3093 e
                                in
                             let uu____3094 =
                               let uu____3096 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3096 ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____3091 uu____3094);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3105  ->
                             let uu____3106 =
                               let uu____3108 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3108 e
                                in
                             let uu____3109 =
                               let uu____3111 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3111 ty1
                                in
                             let uu____3112 =
                               let uu____3114 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3114 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____3106 uu____3109 uu____3112);
                        (let uu____3116 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand g expect uu____3116)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____3128 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
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
  fun uu____3144  ->
    let uu____3145 = FStar_Options.use_nbe_for_extraction ()  in
    if uu____3145
    then extraction_norm_steps_nbe
    else extraction_norm_steps_core
  
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____3166 -> c
    | FStar_Syntax_Syntax.GTotal uu____3175 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____3211  ->
               match uu____3211 with
               | (uu____3226,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___550_3239 = ct  in
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
          }  in
        let c1 =
          let uu___553_3243 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___553_3243.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___553_3243.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let maybe_reify_comp :
  'Auu____3255 .
    'Auu____3255 ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun g  ->
    fun env  ->
      fun c  ->
        let c1 = comp_no_args c  in
        let uu____3274 =
          let uu____3276 =
            let uu____3277 =
              FStar_All.pipe_right c1 FStar_Syntax_Util.comp_effect_name  in
            FStar_All.pipe_right uu____3277
              (FStar_TypeChecker_Env.norm_eff_name env)
             in
          FStar_All.pipe_right uu____3276
            (FStar_TypeChecker_Env.is_reifiable_effect env)
           in
        if uu____3274
        then
          FStar_TypeChecker_Env.reify_comp env c1
            FStar_Syntax_Syntax.U_unknown
        else FStar_Syntax_Util.comp_result c1
  
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let arg_as_mlty g1 uu____3330 =
        match uu____3330 with
        | (a,uu____3338) ->
            let uu____3343 = is_type g1 a  in
            if uu____3343
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_Syntax.MLTY_Erased
         in
      let fv_app_as_mlty g1 fv args =
        let uu____3364 =
          let uu____3366 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____3366  in
        if uu____3364
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____3371 =
             let uu____3378 =
               let uu____3387 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
               FStar_TypeChecker_Env.lookup_lid uu____3387
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____3378 with
             | ((uu____3394,fvty),uu____3396) ->
                 let fvty1 =
                   let uu____3402 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1
                      in
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant] uu____3402 fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____3371 with
           | (formals,uu____3404) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3441 = FStar_Util.first_N n_args formals  in
                   match uu____3441 with
                   | (uu____3470,rest) ->
                       let uu____3504 =
                         FStar_List.map
                           (fun uu____3514  ->
                              FStar_Extraction_ML_Syntax.MLTY_Erased) rest
                          in
                       FStar_List.append mlargs uu____3504
                 else mlargs  in
               let nm =
                 FStar_Extraction_ML_UEnv.mlpath_of_lident g1
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm))
         in
      let aux env t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_type uu____3538 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3539 ->
            let uu____3540 =
              let uu____3542 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3542
               in
            failwith uu____3540
        | FStar_Syntax_Syntax.Tm_delayed uu____3545 ->
            let uu____3560 =
              let uu____3562 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3562
               in
            failwith uu____3560
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3565 =
              let uu____3567 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3567
               in
            failwith uu____3565
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3571 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____3571
        | FStar_Syntax_Syntax.Tm_constant uu____3572 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_quoted uu____3573 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_uvar uu____3580 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____3594) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3599;
               FStar_Syntax_Syntax.index = uu____3600;
               FStar_Syntax_Syntax.sort = t2;_},uu____3602)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3611) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3617,uu____3618) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____3691 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____3691 with
             | (bs1,c1) ->
                 let uu____3698 = binders_as_ml_binders env bs1  in
                 (match uu____3698 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let uu____3727 =
                          let uu____3728 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv env1  in
                          maybe_reify_comp env1 uu____3728 c1  in
                        translate_term_to_mlty env1 uu____3727  in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____3730 =
                        FStar_List.fold_right
                          (fun uu____3750  ->
                             fun uu____3751  ->
                               match (uu____3750, uu____3751) with
                               | ((uu____3774,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____3730 with | (uu____3789,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____3818 =
                let uu____3819 = FStar_Syntax_Util.un_uinst head1  in
                uu____3819.FStar_Syntax_Syntax.n  in
              match uu____3818 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____3850 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____3850
              | uu____3871 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____3874) ->
            let uu____3899 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____3899 with
             | (bs1,ty1) ->
                 let uu____3906 = binders_as_ml_binders env bs1  in
                 (match uu____3906 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____3934 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_match uu____3948 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____3980 ->
            let uu____3987 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____3987 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____3993 -> false  in
      let uu____3995 =
        let uu____3997 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Util.must_erase_for_extraction uu____3997 t0  in
      if uu____3995
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____4002 = is_top_ty mlt  in
         if uu____4002 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____4020 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____4077  ->
                fun b  ->
                  match uu____4077 with
                  | (ml_bs,env) ->
                      let uu____4123 = is_type_binder g b  in
                      if uu____4123
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1 true  in
                        let ml_b =
                          let uu____4146 =
                            FStar_Extraction_ML_UEnv.lookup_ty env1 b1  in
                          uu____4146.FStar_Extraction_ML_UEnv.ty_b_name  in
                        let ml_b1 =
                          (ml_b, FStar_Extraction_ML_Syntax.ml_unit_ty)  in
                        ((ml_b1 :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____4172 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false
                            in
                         match uu____4172 with
                         | (env1,b2,uu____4196) ->
                             let ml_b = (b2, t)  in ((ml_b :: ml_bs), env1)))
             ([], g))
         in
      match uu____4020 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        let uu____4281 = extraction_norm_steps ()  in
        let uu____4282 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Normalize.normalize uu____4281 uu____4282 t0  in
      translate_term_to_mlty g t
  
let (mk_MLE_Seq :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun e1  ->
    fun e2  ->
      match ((e1.FStar_Extraction_ML_Syntax.expr),
              (e2.FStar_Extraction_ML_Syntax.expr))
      with
      | (FStar_Extraction_ML_Syntax.MLE_Seq
         es1,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 es2)
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____4301) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4304,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4308 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
let (mk_MLE_Let :
  Prims.bool ->
    FStar_Extraction_ML_Syntax.mlletbinding ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun top_level  ->
    fun lbs  ->
      fun body  ->
        match lbs with
        | (FStar_Extraction_ML_Syntax.NonRec ,lb::[]) when
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
  fun g  ->
    fun ty  ->
      fun fns  ->
        fun xs  ->
          let fns1 =
            FStar_List.map
              (fun x  ->
                 FStar_Extraction_ML_UEnv.lookup_record_field_name g (ty, x))
              fns
             in
          FStar_List.map2
            (fun uu____4429  ->
               fun x  -> match uu____4429 with | (p,s) -> (s, x)) fns1 xs
  
let (resugar_pat :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlpattern ->
        FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun g  ->
    fun q  ->
      fun p  ->
        match p with
        | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
            let uu____4481 = FStar_Extraction_ML_Util.is_xtuple d  in
            (match uu____4481 with
             | FStar_Pervasives_Native.Some n1 ->
                 FStar_Extraction_ML_Syntax.MLP_Tuple pats
             | uu____4488 ->
                 (match q with
                  | FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                      let path =
                        FStar_List.map FStar_Ident.text_of_id
                          ty.FStar_Ident.ns
                         in
                      let fs = record_fields g ty fns pats  in
                      FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                  | uu____4521 -> p))
        | uu____4524 -> p
  
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
  fun imp  ->
    fun g  ->
      fun p  ->
        fun expected_topt  ->
          fun term_as_mlexpr  ->
            let ok t =
              match expected_topt with
              | FStar_Pervasives_Native.None  -> true
              | FStar_Pervasives_Native.Some t' ->
                  let ok = type_leq g t t'  in
                  (if Prims.op_Negation ok
                   then
                     FStar_Extraction_ML_UEnv.debug g
                       (fun uu____4626  ->
                          let uu____4627 =
                            let uu____4629 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4629 t'
                             in
                          let uu____4630 =
                            let uu____4632 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4632 t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4627 uu____4630)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____4667 = FStar_Options.codegen ()  in
                uu____4667 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4672 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4685 =
                        let uu____4686 =
                          let uu____4687 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4687  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4686
                         in
                      (uu____4685, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        let uu____4709 =
                          let uu____4710 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                          uu____4710.FStar_TypeChecker_Env.dsenv  in
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          uu____4709 c sw FStar_Range.dummyRange
                         in
                      let uu____4711 = term_as_mlexpr g source_term  in
                      (match uu____4711 with
                       | (mlterm,uu____4723,mlty) -> (mlterm, mlty))
                   in
                (match uu____4672 with
                 | (mlc,ml_ty) ->
                     let uu____4742 = FStar_Extraction_ML_UEnv.new_mlident g
                        in
                     (match uu____4742 with
                      | (g1,x) ->
                          let when_clause =
                            let uu____4768 =
                              let uu____4769 =
                                let uu____4776 =
                                  let uu____4779 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         ml_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Var x)
                                     in
                                  [uu____4779; mlc]  in
                                (FStar_Extraction_ML_Util.prims_op_equality,
                                  uu____4776)
                                 in
                              FStar_Extraction_ML_Syntax.MLE_App uu____4769
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_bool_ty)
                              uu____4768
                             in
                          let uu____4782 = ok ml_ty  in
                          (g1,
                            (FStar_Pervasives_Native.Some
                               ((FStar_Extraction_ML_Syntax.MLP_Var x),
                                 [when_clause])), uu____4782)))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  let uu____4803 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_TcTerm.tc_constant uu____4803
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____4805 =
                  let uu____4814 =
                    let uu____4821 =
                      let uu____4822 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4822  in
                    (uu____4821, [])  in
                  FStar_Pervasives_Native.Some uu____4814  in
                let uu____4831 = ok mlty  in (g, uu____4805, uu____4831)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4844 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false imp
                   in
                (match uu____4844 with
                 | (g1,x1,uu____4871) ->
                     let uu____4874 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4874))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4912 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false imp
                   in
                (match uu____4912 with
                 | (g1,x1,uu____4939) ->
                     let uu____4942 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4942))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4978 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____5021 =
                  let uu____5030 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____5030 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____5039;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____5041;
                          FStar_Extraction_ML_Syntax.loc = uu____5042;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;_} ->
                      (n1, ttys)
                  | uu____5049 -> failwith "Expected a constructor"  in
                (match uu____5021 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____5086 = FStar_Util.first_N nTyVars pats  in
                     (match uu____5086 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___852_5190  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____5221  ->
                                               match uu____5221 with
                                               | (p1,uu____5228) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5231,t) ->
                                                        term_as_mlty g t
                                                    | uu____5237 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5241 
                                                              ->
                                                              let uu____5242
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5242);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____5246 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____5246)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____5275 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____5312  ->
                                   match uu____5312 with
                                   | (p1,imp1) ->
                                       let uu____5334 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____5334 with
                                        | (g2,p2,uu____5365) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____5275 with
                           | (g1,tyMLPats) ->
                               let uu____5429 =
                                 FStar_Util.fold_map
                                   (fun uu____5494  ->
                                      fun uu____5495  ->
                                        match (uu____5494, uu____5495) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____5593 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____5653 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____5593 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____5724 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____5724 with
                                                  | (g3,p2,uu____5767) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____5429 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____5888 =
                                      let uu____5899 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5950  ->
                                                match uu___0_5950 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____5992 -> []))
                                         in
                                      FStar_All.pipe_right uu____5899
                                        FStar_List.split
                                       in
                                    (match uu____5888 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____6068 -> false  in
                                         let uu____6078 =
                                           let uu____6087 =
                                             let uu____6094 =
                                               resugar_pat g2
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____6097 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____6094, uu____6097)  in
                                           FStar_Pervasives_Native.Some
                                             uu____6087
                                            in
                                         (g2, uu____6078, pat_ty_compat))))))
  
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
  fun g  ->
    fun p  ->
      fun expected_t  ->
        fun term_as_mlexpr  ->
          let extract_one_pat1 g1 p1 expected_t1 =
            let uu____6229 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____6229 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____6292 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____6340 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____6340
             in
          let uu____6341 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____6341 with
          | (g1,(p1,whens),b) ->
              let when_clause = mk_when_clause whens  in
              (g1, [(p1, when_clause)], b)
  
let (maybe_eta_data_and_project_record :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g  ->
    fun qual  ->
      fun residualType  ->
        fun mlAppExpr  ->
          let rec eta_args g1 more_args t =
            match t with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____6506,t1) ->
                let uu____6508 = FStar_Extraction_ML_UEnv.new_mlident g1  in
                (match uu____6508 with
                 | (g2,x) ->
                     let uu____6533 =
                       let uu____6545 =
                         let uu____6555 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty t0)
                             (FStar_Extraction_ML_Syntax.MLE_Var x)
                            in
                         ((x, t0), uu____6555)  in
                       uu____6545 :: more_args  in
                     eta_args g2 uu____6533 t1)
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6571,uu____6572)
                -> ((FStar_List.rev more_args), t)
            | uu____6597 ->
                let uu____6598 =
                  let uu____6600 =
                    let uu____6602 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu____6602
                      mlAppExpr
                     in
                  let uu____6603 =
                    let uu____6605 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlty uu____6605 t  in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6600 uu____6603
                   in
                failwith uu____6598
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____6639,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields g tyname fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6676 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____6698 = eta_args g [] residualType  in
            match uu____6698 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____6756 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____6756
                 | uu____6757 ->
                     let uu____6769 = FStar_List.unzip eargs  in
                     (match uu____6769 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____6815 =
                                   let uu____6816 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6816
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6815
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6826 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6830,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6834;
                FStar_Extraction_ML_Syntax.loc = uu____6835;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let fn =
                let uu____6847 =
                  let uu____6852 =
                    let uu____6853 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6853
                      constrname
                     in
                  (uu____6852, f)  in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6847
                 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____6856 ->
                    let uu____6859 =
                      let uu____6866 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6866, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6859
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6870;
                     FStar_Extraction_ML_Syntax.loc = uu____6871;_},uu____6872);
                FStar_Extraction_ML_Syntax.mlty = uu____6873;
                FStar_Extraction_ML_Syntax.loc = uu____6874;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let fn =
                let uu____6890 =
                  let uu____6895 =
                    let uu____6896 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6896
                      constrname
                     in
                  (uu____6895, f)  in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6890
                 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____6899 ->
                    let uu____6902 =
                      let uu____6909 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6909, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6902
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6913;
                FStar_Extraction_ML_Syntax.loc = uu____6914;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6922 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6922
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6926;
                FStar_Extraction_ML_Syntax.loc = uu____6927;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6929)) ->
              let uu____6942 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6942
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6946;
                     FStar_Extraction_ML_Syntax.loc = uu____6947;_},uu____6948);
                FStar_Extraction_ML_Syntax.mlty = uu____6949;
                FStar_Extraction_ML_Syntax.loc = uu____6950;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6962 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6962
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6966;
                     FStar_Extraction_ML_Syntax.loc = uu____6967;_},uu____6968);
                FStar_Extraction_ML_Syntax.mlty = uu____6969;
                FStar_Extraction_ML_Syntax.loc = uu____6970;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6972)) ->
              let uu____6989 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6989
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____6995 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6995
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6999)) ->
              let uu____7008 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7008
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7012;
                FStar_Extraction_ML_Syntax.loc = uu____7013;_},uu____7014),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____7021 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7021
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7025;
                FStar_Extraction_ML_Syntax.loc = uu____7026;_},uu____7027),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7028)) ->
              let uu____7041 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7041
          | uu____7044 -> mlAppExpr
  
let (maybe_promote_effect :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_Syntax.mlexpr *
          FStar_Extraction_ML_Syntax.e_tag))
  =
  fun ml_e  ->
    fun tag  ->
      fun t  ->
        match (tag, t) with
        | (FStar_Extraction_ML_Syntax.E_GHOST
           ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
            (FStar_Extraction_ML_Syntax.ml_unit,
              FStar_Extraction_ML_Syntax.E_PURE)
        | (FStar_Extraction_ML_Syntax.E_PURE
           ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
            (FStar_Extraction_ML_Syntax.ml_unit,
              FStar_Extraction_ML_Syntax.E_PURE)
        | uu____7075 -> (ml_e, tag)
  
let (extract_lb_sig :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.letbindings ->
      (FStar_Syntax_Syntax.lbname * FStar_Extraction_ML_Syntax.e_tag *
        (FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.binders *
        FStar_Extraction_ML_Syntax.mltyscheme)) * Prims.bool *
        FStar_Syntax_Syntax.term) Prims.list)
  =
  fun g  ->
    fun lbs  ->
      let maybe_generalize uu____7136 =
        match uu____7136 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____7157;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____7162;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____7243 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____7320 =
              let uu____7322 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Util.must_erase_for_extraction uu____7322
                lbtyp1
               in
            if uu____7320
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____7407 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____7407 (is_type_binder g) ->
                   let uu____7429 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____7429 with
                    | (bs1,c1) ->
                        let uu____7455 =
                          let uu____7468 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____7514 = is_type_binder g x  in
                                 Prims.op_Negation uu____7514) bs1
                             in
                          match uu____7468 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____7641 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____7641)
                           in
                        (match uu____7455 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____7703 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____7703
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____7752 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____7752 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7804 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____7804 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7907  ->
                                                       fun uu____7908  ->
                                                         match (uu____7907,
                                                                 uu____7908)
                                                         with
                                                         | ((x,uu____7934),
                                                            (y,uu____7936))
                                                             ->
                                                             let uu____7957 =
                                                               let uu____7964
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____7964)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7957)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____7981  ->
                                                       match uu____7981 with
                                                       | (a,uu____7989) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a false) g
                                                  targs
                                                 in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty
                                                 in
                                              let polytype =
                                                let uu____8001 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____8021  ->
                                                          match uu____8021
                                                          with
                                                          | (x,uu____8030) ->
                                                              let uu____8035
                                                                =
                                                                FStar_Extraction_ML_UEnv.lookup_ty
                                                                  env x
                                                                 in
                                                              uu____8035.FStar_Extraction_ML_UEnv.ty_b_name))
                                                   in
                                                (uu____8001, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____8047 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____8047)
                                                      ||
                                                      (let uu____8050 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____8050)
                                                | uu____8052 -> false  in
                                              let rest_args1 =
                                                if add_unit
                                                then
                                                  let uu____8064 =
                                                    unit_binder ()  in
                                                  uu____8064 :: rest_args
                                                else rest_args  in
                                              let polytype1 =
                                                if add_unit
                                                then
                                                  FStar_Extraction_ML_Syntax.push_unit
                                                    polytype
                                                else polytype  in
                                              let body2 =
                                                FStar_Syntax_Util.abs
                                                  rest_args1 body1 copt
                                                 in
                                              (lbname_, f_e,
                                                (lbtyp1, (targs, polytype1)),
                                                add_unit, body2))
                                       else
                                         failwith "Not enough type binders")
                              | FStar_Syntax_Syntax.Tm_uinst uu____8121 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8140  ->
                                           match uu____8140 with
                                           | (a,uu____8148) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8160 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8180  ->
                                              match uu____8180 with
                                              | (x,uu____8189) ->
                                                  let uu____8194 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8194.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8160, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8234  ->
                                            match uu____8234 with
                                            | (bv,uu____8242) ->
                                                let uu____8247 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8247
                                                  FStar_Syntax_Syntax.as_arg))
                                     in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      FStar_Pervasives_Native.None
                                      lbdef1.FStar_Syntax_Syntax.pos
                                     in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | FStar_Syntax_Syntax.Tm_fvar uu____8277 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8290  ->
                                           match uu____8290 with
                                           | (a,uu____8298) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8310 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8330  ->
                                              match uu____8330 with
                                              | (x,uu____8339) ->
                                                  let uu____8344 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8344.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8310, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8384  ->
                                            match uu____8384 with
                                            | (bv,uu____8392) ->
                                                let uu____8397 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8397
                                                  FStar_Syntax_Syntax.as_arg))
                                     in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      FStar_Pervasives_Native.None
                                      lbdef1.FStar_Syntax_Syntax.pos
                                     in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | FStar_Syntax_Syntax.Tm_name uu____8427 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8440  ->
                                           match uu____8440 with
                                           | (a,uu____8448) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8460 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8480  ->
                                              match uu____8480 with
                                              | (x,uu____8489) ->
                                                  let uu____8494 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8494.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8460, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8534  ->
                                            match uu____8534 with
                                            | (bv,uu____8542) ->
                                                let uu____8547 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8547
                                                  FStar_Syntax_Syntax.as_arg))
                                     in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (lbdef1, args))
                                      FStar_Pervasives_Native.None
                                      lbdef1.FStar_Syntax_Syntax.pos
                                     in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | uu____8577 -> err_value_restriction lbdef1)))
               | uu____8597 -> no_gen ())
         in
      FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
        (FStar_List.map maybe_generalize)
  
let (extract_lb_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.letbindings ->
      (FStar_Extraction_ML_UEnv.uenv * (FStar_Syntax_Syntax.fv *
        FStar_Extraction_ML_UEnv.exp_binding) Prims.list))
  =
  fun g  ->
    fun lbs  ->
      let is_top =
        FStar_Syntax_Syntax.is_top_level (FStar_Pervasives_Native.snd lbs)
         in
      let is_rec =
        (Prims.op_Negation is_top) && (FStar_Pervasives_Native.fst lbs)  in
      let lbs1 = extract_lb_sig g lbs  in
      FStar_Util.fold_map
        (fun env  ->
           fun uu____8748  ->
             match uu____8748 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____8809 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit
                    in
                 (match uu____8809 with
                  | (env1,uu____8826,exp_binding) ->
                      let uu____8830 =
                        let uu____8835 = FStar_Util.right lbname  in
                        (uu____8835, exp_binding)  in
                      (env1, uu____8830))) g lbs1
  
let rec (check_term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr *
            FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      fun f  ->
        fun ty  ->
          FStar_Extraction_ML_UEnv.debug g
            (fun uu____8902  ->
               let uu____8903 = FStar_Syntax_Print.term_to_string e  in
               let uu____8905 =
                 let uu____8907 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g  in
                 FStar_Extraction_ML_Code.string_of_mlty uu____8907 ty  in
               let uu____8908 = FStar_Extraction_ML_Util.eff_to_string f  in
               FStar_Util.print3 "Checking %s at type %s and eff %s\n"
                 uu____8903 uu____8905 uu____8908);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____8915) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8916 ->
               let uu____8921 = term_as_mlexpr g e  in
               (match uu____8921 with
                | (ml_e,tag,t) ->
                    let uu____8935 = FStar_Extraction_ML_Util.eff_leq tag f
                       in
                    if uu____8935
                    then
                      let uu____8942 =
                        maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t ty
                         in
                      (uu____8942, ty)
                    else
                      (match (tag, f, ty) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST
                          ,FStar_Extraction_ML_Syntax.E_PURE
                          ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                           let uu____8949 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t
                               ty
                              in
                           (uu____8949, ty)
                       | uu____8950 ->
                           (err_unexpected_eff g e ty f tag;
                            (let uu____8958 =
                               maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e
                                 t ty
                                in
                             (uu____8958, ty))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____8967 = term_as_mlexpr' g e  in
      match uu____8967 with
      | (e1,f,t) ->
          let uu____8983 = maybe_promote_effect e1 f t  in
          (match uu____8983 with | (e2,f1) -> (e2, f1, t))

and (term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun top  ->
      let top1 = FStar_Syntax_Subst.compress top  in
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____9009 =
             let uu____9011 =
               FStar_Range.string_of_range top1.FStar_Syntax_Syntax.pos  in
             let uu____9013 = FStar_Syntax_Print.tag_of_term top1  in
             let uu____9015 = FStar_Syntax_Print.term_to_string top1  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____9011 uu____9013 uu____9015
              in
           FStar_Util.print_string uu____9009);
      (let is_match t =
         let uu____9025 =
           let uu____9026 =
             let uu____9029 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9029 FStar_Syntax_Util.unascribe  in
           uu____9026.FStar_Syntax_Syntax.n  in
         match uu____9025 with
         | FStar_Syntax_Syntax.Tm_match uu____9033 -> true
         | uu____9057 -> false  in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____9076  ->
              match uu____9076 with
              | (t,uu____9085) ->
                  let uu____9090 =
                    let uu____9091 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
                    uu____9091.FStar_Syntax_Syntax.n  in
                  (match uu____9090 with
                   | FStar_Syntax_Syntax.Tm_name uu____9097 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____9099 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____9101 -> true
                   | uu____9103 -> false))
          in
       let apply_to_match_branches head1 args =
         let uu____9142 =
           let uu____9143 =
             let uu____9146 =
               FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9146 FStar_Syntax_Util.unascribe  in
           uu____9143.FStar_Syntax_Syntax.n  in
         match uu____9142 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee,branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____9270  ->
                       match uu____9270 with
                       | (pat,when_opt,body) ->
                           (pat, when_opt,
                             (let uu___1319_9327 = body  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1319_9327.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1319_9327.FStar_Syntax_Syntax.vars)
                              }))))
                in
             let uu___1322_9342 = head1  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1322_9342.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1322_9342.FStar_Syntax_Syntax.vars)
             }
         | uu____9363 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match"
          in
       let t = FStar_Syntax_Subst.compress top1  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9374 =
             let uu____9376 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9376
              in
           failwith uu____9374
       | FStar_Syntax_Syntax.Tm_delayed uu____9385 ->
           let uu____9400 =
             let uu____9402 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9402
              in
           failwith uu____9400
       | FStar_Syntax_Syntax.Tm_uvar uu____9411 ->
           let uu____9424 =
             let uu____9426 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9426
              in
           failwith uu____9424
       | FStar_Syntax_Syntax.Tm_bvar uu____9435 ->
           let uu____9436 =
             let uu____9438 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9438
              in
           failwith uu____9436
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9448 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____9448
       | FStar_Syntax_Syntax.Tm_type uu____9449 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9450 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9457 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____9473;_})
           ->
           let uu____9486 =
             let uu____9487 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9487  in
           (match uu____9486 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9494;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9496;_} ->
                let uu____9498 =
                  let uu____9499 =
                    let uu____9500 =
                      let uu____9507 =
                        let uu____9510 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____9510]  in
                      (fw, uu____9507)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9500  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9499
                   in
                (uu____9498, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9528 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____9528 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9536 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____9536 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____9547 =
                         let uu____9554 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____9554
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____9547 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____9562 =
                         let uu____9573 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____9573]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9562
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9600 =
                    let uu____9607 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____9607 tv  in
                  uu____9600 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____9615 =
                    let uu____9626 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____9626]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9615
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____9653)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9686 =
                  let uu____9693 =
                    let uu____9702 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.effect_decl_opt uu____9702 m  in
                  FStar_Util.must uu____9693  in
                (match uu____9686 with
                 | (ed,qualifiers) ->
                     let uu____9721 =
                       let uu____9723 =
                         let uu____9725 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                         FStar_TypeChecker_Env.is_reifiable_effect uu____9725
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____9723  in
                     if uu____9721
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9742 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9744) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9750) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9756 =
             let uu____9763 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_TcTerm.type_of_tot_term uu____9763 t  in
           (match uu____9756 with
            | (uu____9770,ty,uu____9772) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____9774 =
                  let uu____9775 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9775  in
                (uu____9774, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9776 ->
           let uu____9777 = is_type g t  in
           if uu____9777
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9788 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____9788 with
              | (FStar_Util.Inl uu____9801,uu____9802) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9807;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____9826 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____9826, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9827 -> instantiate_maybe_partial g x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9829 = is_type g t  in
           if uu____9829
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9840 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____9840 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9849;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9858  ->
                        let uu____9859 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____9861 =
                          let uu____9863 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            uu____9863 x
                           in
                        let uu____9864 =
                          let uu____9866 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlty uu____9866
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9859 uu____9861 uu____9864);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____9878 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____9878, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9879 -> instantiate_maybe_partial g x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____9907 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____9907 with
            | (bs1,body1) ->
                let uu____9920 = binders_as_ml_binders g bs1  in
                (match uu____9920 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9956 =
                             let uu____9958 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Env.is_reifiable_rc uu____9958
                               rc
                              in
                           if uu____9956
                           then
                             let uu____9960 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Util.reify_body uu____9960
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Unascribe] body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9966  ->
                                 let uu____9967 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9967);
                            body1)
                        in
                     let uu____9970 = term_as_mlexpr env body2  in
                     (match uu____9970 with
                      | (ml_body,f,t1) ->
                          let uu____9986 =
                            FStar_List.fold_right
                              (fun uu____10006  ->
                                 fun uu____10007  ->
                                   match (uu____10006, uu____10007) with
                                   | ((uu____10030,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____9986 with
                           | (f1,tfun) ->
                               let uu____10053 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____10053, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____10061;
              FStar_Syntax_Syntax.vars = uu____10062;_},(a1,uu____10064)::[])
           ->
           let ty =
             let uu____10104 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____10104  in
           let uu____10105 =
             let uu____10106 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____10106
              in
           (uu____10105, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____10107;
              FStar_Syntax_Syntax.vars = uu____10108;_},(t1,uu____10110)::
            (r,uu____10112)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____10167);
              FStar_Syntax_Syntax.pos = uu____10168;
              FStar_Syntax_Syntax.vars = uu____10169;_},uu____10170)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (is_match head1) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____10229 =
             FStar_All.pipe_right args (apply_to_match_branches head1)  in
           FStar_All.pipe_right uu____10229 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_10283  ->
                        match uu___1_10283 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____10286 -> false)))
              in
           let uu____10288 =
             let uu____10289 =
               let uu____10292 =
                 FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
               FStar_All.pipe_right uu____10292 FStar_Syntax_Util.unascribe
                in
             uu____10289.FStar_Syntax_Syntax.n  in
           (match uu____10288 with
            | FStar_Syntax_Syntax.Tm_abs (bs,uu____10302,_rc) ->
                let uu____10328 =
                  let uu____10329 =
                    let uu____10334 =
                      FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses]
                      uu____10334
                     in
                  FStar_All.pipe_right t uu____10329  in
                FStar_All.pipe_right uu____10328 (term_as_mlexpr g)
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                let e =
                  let uu____10342 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  let uu____10343 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg uu____10342
                    [FStar_TypeChecker_Env.Inlining;
                    FStar_TypeChecker_Env.Unascribe] head1 uu____10343
                   in
                let tm =
                  let uu____10355 =
                    let uu____10360 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____10361 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____10360 uu____10361  in
                  uu____10355 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____10370 ->
                let rec extract_app is_data uu____10419 uu____10420 restArgs
                  =
                  match (uu____10419, uu____10420) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____10501 =
                        let mlargs =
                          FStar_All.pipe_right (FStar_List.rev mlargs_f)
                            (FStar_List.map FStar_Pervasives_Native.fst)
                           in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty t1)
                          (FStar_Extraction_ML_Syntax.MLE_App
                             (mlhead, mlargs))
                         in
                      (FStar_Extraction_ML_UEnv.debug g
                         (fun uu____10528  ->
                            let uu____10529 =
                              let uu____10531 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              let uu____10532 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____10531 uu____10532
                               in
                            let uu____10533 =
                              let uu____10535 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlty
                                uu____10535 t1
                               in
                            let uu____10536 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____10547)::uu____10548 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10529 uu____10533 uu____10536);
                       (match (restArgs, t1) with
                        | ([],uu____10582) ->
                            let app =
                              let uu____10598 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10598
                               in
                            (app, f, t1)
                        | ((arg,uu____10600)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10631 =
                              let uu____10636 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____10636, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10631 rest
                        | ((e0,uu____10648)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____10681 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____10681
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____10686 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____10686 with
                             | (e01,tInferred) ->
                                 let uu____10699 =
                                   let uu____10704 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____10704, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10699 rest)
                        | uu____10715 ->
                            let uu____10728 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____10728 with
                             | FStar_Pervasives_Native.Some t2 ->
                                 extract_app is_data (mlhead, mlargs_f)
                                   (f, t2) restArgs
                             | FStar_Pervasives_Native.None  ->
                                 (match t1 with
                                  | FStar_Extraction_ML_Syntax.MLTY_Erased 
                                      ->
                                      (FStar_Extraction_ML_Syntax.ml_unit,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        t1)
                                  | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                                      let t2 =
                                        FStar_List.fold_right
                                          (fun t2  ->
                                             fun out  ->
                                               FStar_Extraction_ML_Syntax.MLTY_Fun
                                                 (FStar_Extraction_ML_Syntax.MLTY_Top,
                                                   FStar_Extraction_ML_Syntax.E_PURE,
                                                   out)) restArgs
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                         in
                                      let mlhead1 =
                                        let mlargs =
                                          FStar_All.pipe_right
                                            (FStar_List.rev mlargs_f)
                                            (FStar_List.map
                                               FStar_Pervasives_Native.fst)
                                           in
                                        let head2 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.MLTY_Top)
                                            (FStar_Extraction_ML_Syntax.MLE_App
                                               (mlhead, mlargs))
                                           in
                                        maybe_coerce
                                          top1.FStar_Syntax_Syntax.pos g
                                          head2
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t2
                                         in
                                      extract_app is_data (mlhead1, [])
                                        (f, t2) restArgs
                                  | uu____10800 ->
                                      let mlhead1 =
                                        let mlargs =
                                          FStar_All.pipe_right
                                            (FStar_List.rev mlargs_f)
                                            (FStar_List.map
                                               FStar_Pervasives_Native.fst)
                                           in
                                        let head2 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.MLTY_Top)
                                            (FStar_Extraction_ML_Syntax.MLE_App
                                               (mlhead, mlargs))
                                           in
                                        maybe_coerce
                                          top1.FStar_Syntax_Syntax.pos g
                                          head2
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t1
                                         in
                                      err_ill_typed_application g top1
                                        mlhead1 restArgs t1))))
                   in
                let extract_app_maybe_projector is_data mlhead uu____10871
                  args1 =
                  match uu____10871 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10901)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10985))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____10987,f',t3)) ->
                                 let uu____11025 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____11025 t3
                             | uu____11026 -> (args2, f1, t2)  in
                           let uu____11051 = remove_implicits args1 f t1  in
                           (match uu____11051 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____11107 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____11131 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____11139 ->
                      let uu____11140 =
                        let uu____11155 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____11155 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11187  ->
                                  let uu____11188 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____11190 =
                                    let uu____11192 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11192
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11193 =
                                    let uu____11195 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11195
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  FStar_Util.print3
                                    "@@@looked up %s: got %s at %s\n"
                                    uu____11188 uu____11190 uu____11193);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu____11211 -> failwith "FIXME Ty"  in
                      (match uu____11140 with
                       | ((head_ml,(vars,t1)),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11263)::uu____11264 -> is_type g a
                             | uu____11291 -> false  in
                           let uu____11303 =
                             let n1 = FStar_List.length vars  in
                             let uu____11320 =
                               if (FStar_List.length args) <= n1
                               then
                                 let uu____11358 =
                                   FStar_List.map
                                     (fun uu____11370  ->
                                        match uu____11370 with
                                        | (x,uu____11378) -> term_as_mlty g x)
                                     args
                                    in
                                 (uu____11358, [])
                               else
                                 (let uu____11401 =
                                    FStar_Util.first_N n1 args  in
                                  match uu____11401 with
                                  | (prefix1,rest) ->
                                      let uu____11490 =
                                        FStar_List.map
                                          (fun uu____11502  ->
                                             match uu____11502 with
                                             | (x,uu____11510) ->
                                                 term_as_mlty g x) prefix1
                                         in
                                      (uu____11490, rest))
                                in
                             match uu____11320 with
                             | (provided_type_args,rest) ->
                                 let uu____11561 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu____11570 ->
                                       let uu____11571 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____11571 with
                                        | (head3,uu____11583,t2) ->
                                            (head3, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu____11585 ->
                                       let uu____11587 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____11587 with
                                        | (head3,uu____11599,t2) ->
                                            (head3, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head3,{
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  FStar_Extraction_ML_Syntax.MLE_Const
                                                  (FStar_Extraction_ML_Syntax.MLC_Unit
                                                  );
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = uu____11602;
                                                FStar_Extraction_ML_Syntax.loc
                                                  = uu____11603;_}::[])
                                       ->
                                       let uu____11606 =
                                         instantiate_maybe_partial g head3
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____11606 with
                                        | (head4,uu____11618,t2) ->
                                            let uu____11620 =
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head4,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                               in
                                            (uu____11620, t2))
                                   | uu____11623 ->
                                       failwith
                                         "Impossible: Unexpected head term"
                                    in
                                 (match uu____11561 with
                                  | (head3,t2) -> (head3, t2, rest))
                              in
                           (match uu____11303 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11690 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____11690,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11691 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11700 ->
                      let uu____11701 =
                        let uu____11716 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____11716 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11748  ->
                                  let uu____11749 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____11751 =
                                    let uu____11753 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11753
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11754 =
                                    let uu____11756 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11756
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  FStar_Util.print3
                                    "@@@looked up %s: got %s at %s\n"
                                    uu____11749 uu____11751 uu____11754);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu____11772 -> failwith "FIXME Ty"  in
                      (match uu____11701 with
                       | ((head_ml,(vars,t1)),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11824)::uu____11825 -> is_type g a
                             | uu____11852 -> false  in
                           let uu____11864 =
                             let n1 = FStar_List.length vars  in
                             let uu____11881 =
                               if (FStar_List.length args) <= n1
                               then
                                 let uu____11919 =
                                   FStar_List.map
                                     (fun uu____11931  ->
                                        match uu____11931 with
                                        | (x,uu____11939) -> term_as_mlty g x)
                                     args
                                    in
                                 (uu____11919, [])
                               else
                                 (let uu____11962 =
                                    FStar_Util.first_N n1 args  in
                                  match uu____11962 with
                                  | (prefix1,rest) ->
                                      let uu____12051 =
                                        FStar_List.map
                                          (fun uu____12063  ->
                                             match uu____12063 with
                                             | (x,uu____12071) ->
                                                 term_as_mlty g x) prefix1
                                         in
                                      (uu____12051, rest))
                                in
                             match uu____11881 with
                             | (provided_type_args,rest) ->
                                 let uu____12122 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu____12131 ->
                                       let uu____12132 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____12132 with
                                        | (head3,uu____12144,t2) ->
                                            (head3, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu____12146 ->
                                       let uu____12148 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____12148 with
                                        | (head3,uu____12160,t2) ->
                                            (head3, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head3,{
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  FStar_Extraction_ML_Syntax.MLE_Const
                                                  (FStar_Extraction_ML_Syntax.MLC_Unit
                                                  );
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = uu____12163;
                                                FStar_Extraction_ML_Syntax.loc
                                                  = uu____12164;_}::[])
                                       ->
                                       let uu____12167 =
                                         instantiate_maybe_partial g head3
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____12167 with
                                        | (head4,uu____12179,t2) ->
                                            let uu____12181 =
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head4,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                               in
                                            (uu____12181, t2))
                                   | uu____12184 ->
                                       failwith
                                         "Impossible: Unexpected head term"
                                    in
                                 (match uu____12122 with
                                  | (head3,t2) -> (head3, t2, rest))
                              in
                           (match uu____11864 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12251 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____12251,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12252 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12261 ->
                      let uu____12262 = term_as_mlexpr g head2  in
                      (match uu____12262 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____12278 = is_type g t  in
                if uu____12278
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12289 =
                     let uu____12290 = FStar_Syntax_Util.un_uinst head1  in
                     uu____12290.FStar_Syntax_Syntax.n  in
                   match uu____12289 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12300 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____12300 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12309 -> extract_app_with_instantiations ())
                   | uu____12312 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____12315),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12380 =
                   let uu____12381 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                      in
                   maybe_reify_comp g uu____12381 c  in
                 term_as_mlty g uu____12380
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____12385 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____12385 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e') when
           (let uu____12417 = FStar_Syntax_Syntax.is_top_level [lb]  in
            Prims.op_Negation uu____12417) &&
             (let uu____12420 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs
                 in
              FStar_Util.is_some uu____12420)
           ->
           let b =
             let uu____12430 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                in
             (uu____12430, FStar_Pervasives_Native.None)  in
           let uu____12433 = FStar_Syntax_Subst.open_term_1 b e'  in
           (match uu____12433 with
            | ((x,uu____12445),body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str,uu____12460)::[]) ->
                      let uu____12485 =
                        let uu____12486 = FStar_Syntax_Subst.compress str  in
                        uu____12486.FStar_Syntax_Syntax.n  in
                      (match uu____12485 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s,uu____12492)) ->
                           let id1 =
                             let uu____12496 =
                               let uu____12502 =
                                 FStar_Syntax_Syntax.range_of_bv x  in
                               (s, uu____12502)  in
                             FStar_Ident.mk_ident uu____12496  in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id1;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             }  in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv  in
                           FStar_Pervasives_Native.Some bv1
                       | uu____12507 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____12508 ->
                      (FStar_Errors.log_issue top1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `rename_let`");
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                   in
                let remove_attr1 attrs =
                  let uu____12528 =
                    FStar_List.partition
                      (fun attr  ->
                         let uu____12540 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr]
                            in
                         FStar_Util.is_some uu____12540)
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match uu____12528 with
                  | (uu____12545,other_attrs) -> other_attrs  in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None  ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1774_12573 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1774_12573.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1774_12573.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1774_12573.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1774_12573.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1774_12573.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1774_12573.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      let rename =
                        let uu____12581 =
                          let uu____12582 =
                            let uu____12589 =
                              FStar_Syntax_Syntax.bv_to_name y  in
                            (x, uu____12589)  in
                          FStar_Syntax_Syntax.NT uu____12582  in
                        [uu____12581]  in
                      let body1 =
                        let uu____12595 =
                          FStar_Syntax_Subst.subst rename body  in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____12595
                         in
                      let lb1 =
                        let uu___1781_12611 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1781_12611.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1781_12611.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1781_12611.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1781_12611.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1781_12611.FStar_Syntax_Syntax.lbpos)
                        }  in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1)
                   in
                let top2 =
                  let uu___1785_12628 = top1  in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1785_12628.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1785_12628.FStar_Syntax_Syntax.vars)
                  }  in
                term_as_mlexpr' g top2)
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____12651 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12667 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____12667
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____12682 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____12682  in
                   let lb1 =
                     let uu___1799_12684 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1799_12684.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1799_12684.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1799_12684.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1799_12684.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1799_12684.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1799_12684.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____12651 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____12709 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      let uu____12710 =
                        let uu____12711 =
                          let uu____12712 =
                            let uu____12716 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Pervasives_Native.fst uu____12716  in
                          let uu____12729 =
                            let uu____12733 =
                              let uu____12735 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Pervasives_Native.snd uu____12735  in
                            [uu____12733]  in
                          FStar_List.append uu____12712 uu____12729  in
                        FStar_Ident.lid_of_path uu____12711
                          FStar_Range.dummyRange
                         in
                      FStar_TypeChecker_Env.set_current_module uu____12709
                        uu____12710
                       in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let lbdef =
                              let uu____12762 = FStar_Options.ml_ish ()  in
                              if uu____12762
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____12774 =
                                   let uu____12775 =
                                     let uu____12776 =
                                       extraction_norm_steps ()  in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____12776
                                      in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____12775 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____12779 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____12779
                                 then
                                   ((let uu____12789 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____12789);
                                    (let a =
                                       let uu____12795 =
                                         let uu____12797 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____12797
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____12795 norm_call
                                        in
                                     a))
                                 else norm_call ())
                               in
                            let uu___1816_12804 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1816_12804.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1816_12804.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1816_12804.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1816_12804.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1816_12804.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1816_12804.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____12857 =
                  match uu____12857 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____13013  ->
                               match uu____13013 with
                               | (a,uu____13021) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     false) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____13028 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____13028 with
                       | (e1,ty) ->
                           let uu____13039 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____13039 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____13051 -> []  in
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
                                  })))
                   in
                let lbs3 = extract_lb_sig g (is_rec, lbs2)  in
                let uu____13082 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____13179  ->
                         match uu____13179 with
                         | (env,lbs4) ->
                             let uu____13313 = lb  in
                             (match uu____13313 with
                              | (lbname,uu____13364,(t1,(uu____13366,polytype)),add_unit,uu____13369)
                                  ->
                                  let uu____13384 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit
                                     in
                                  (match uu____13384 with
                                   | (env1,nm,uu____13424) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____13082 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____13703 = term_as_mlexpr env_body e'1  in
                     (match uu____13703 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____13720 =
                              let uu____13723 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____13723  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13720
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____13736 =
                            let uu____13737 =
                              let uu____13738 =
                                let uu____13739 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____13739)  in
                              mk_MLE_Let top_level uu____13738 e'2  in
                            let uu____13748 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13737 uu____13748
                             in
                          (uu____13736, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____13787 = term_as_mlexpr g scrutinee  in
           (match uu____13787 with
            | (e,f_e,t_e) ->
                let uu____13803 = check_pats_for_ite pats  in
                (match uu____13803 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____13868 = term_as_mlexpr g then_e1  in
                            (match uu____13868 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____13884 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____13884 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____13900 =
                                        let uu____13911 =
                                          type_leq g t_then t_else  in
                                        if uu____13911
                                        then (t_else, no_lift)
                                        else
                                          (let uu____13932 =
                                             type_leq g t_else t_then  in
                                           if uu____13932
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____13900 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____13979 =
                                             let uu____13980 =
                                               let uu____13981 =
                                                 let uu____13990 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____13991 =
                                                   let uu____13994 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____13994
                                                    in
                                                 (e, uu____13990,
                                                   uu____13991)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____13981
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____13980
                                              in
                                           let uu____13997 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____13979, uu____13997,
                                             t_branch))))
                        | uu____13998 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____14016 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____14115 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____14115 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____14160 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____14160 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____14222 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let w_pos =
                                                     w.FStar_Syntax_Syntax.pos
                                                      in
                                                   let uu____14245 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____14245 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____14222 with
                                              | (when_opt1,f_when) ->
                                                  let uu____14295 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____14295 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____14330 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14407 
                                                                 ->
                                                                 match uu____14407
                                                                 with
                                                                 | (p1,wopt)
                                                                    ->
                                                                    let when_clause
                                                                    =
                                                                    FStar_Extraction_ML_Util.conjoin_opt
                                                                    wopt
                                                                    when_opt1
                                                                     in
                                                                    (p1,
                                                                    (when_clause,
                                                                    f_when),
                                                                    (mlbranch,
                                                                    f_branch,
                                                                    t_branch))))
                                                          in
                                                       ((compat &&
                                                           pat_t_compat),
                                                         uu____14330)))))
                               true)
                           in
                        match uu____14016 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14578  ->
                                      let uu____14579 =
                                        let uu____14581 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu____14581 e
                                         in
                                      let uu____14582 =
                                        let uu____14584 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu____14584 t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14579 uu____14582);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14610 =
                                   let uu____14611 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14611
                                    in
                                 (match uu____14610 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14618;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14620;_}
                                      ->
                                      let uu____14622 =
                                        let uu____14623 =
                                          let uu____14624 =
                                            let uu____14631 =
                                              let uu____14634 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____14634]  in
                                            (fw, uu____14631)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14624
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14623
                                         in
                                      (uu____14622,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14638,uu____14639,(uu____14640,f_first,t_first))::rest
                                 ->
                                 let uu____14700 =
                                   FStar_List.fold_left
                                     (fun uu____14742  ->
                                        fun uu____14743  ->
                                          match (uu____14742, uu____14743)
                                          with
                                          | ((topt,f),(uu____14800,uu____14801,
                                                       (uu____14802,f_branch,t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top1.FStar_Syntax_Syntax.pos
                                                  f f_branch
                                                 in
                                              let topt1 =
                                                match topt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    t1 ->
                                                    let uu____14858 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____14858
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____14865 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____14865
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           t1
                                                       else
                                                         FStar_Pervasives_Native.None)
                                                 in
                                              (topt1, f1))
                                     ((FStar_Pervasives_Native.Some t_first),
                                       f_first) rest
                                    in
                                 (match uu____14700 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____14963  ->
                                                match uu____14963 with
                                                | (p,(wopt,uu____14992),
                                                   (b1,uu____14994,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____15013 -> b1
                                                       in
                                                    (p, wopt, b2)))
                                         in
                                      let t_match =
                                        match topt with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | FStar_Pervasives_Native.Some t1 ->
                                            t1
                                         in
                                      let uu____15018 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____15018, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____15045 =
          let uu____15050 =
            let uu____15059 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_lid uu____15059 discName  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15050  in
        match uu____15045 with
        | (uu____15076,fstar_disc_type) ->
            let uu____15078 =
              let uu____15090 =
                let uu____15091 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____15091.FStar_Syntax_Syntax.n  in
              match uu____15090 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15106) ->
                  let binders1 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_15161  ->
                            match uu___2_15161 with
                            | (uu____15169,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15170)) ->
                                true
                            | uu____15175 -> false))
                     in
                  FStar_List.fold_right
                    (fun uu____15207  ->
                       fun uu____15208  ->
                         match uu____15208 with
                         | (g,vs) ->
                             let uu____15253 =
                               FStar_Extraction_ML_UEnv.new_mlident g  in
                             (match uu____15253 with
                              | (g1,v1) ->
                                  (g1,
                                    ((v1,
                                       FStar_Extraction_ML_Syntax.MLTY_Top)
                                    :: vs)))) binders1 (env, [])
              | uu____15299 -> failwith "Discriminator must be a function"
               in
            (match uu____15078 with
             | (g,wildcards) ->
                 let uu____15328 = FStar_Extraction_ML_UEnv.new_mlident g  in
                 (match uu____15328 with
                  | (g1,mlid) ->
                      let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let discrBody =
                        let uu____15341 =
                          let uu____15342 =
                            let uu____15354 =
                              let uu____15355 =
                                let uu____15356 =
                                  let uu____15371 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         targ)
                                      (FStar_Extraction_ML_Syntax.MLE_Name
                                         ([], mlid))
                                     in
                                  let uu____15377 =
                                    let uu____15388 =
                                      let uu____15397 =
                                        let uu____15398 =
                                          let uu____15405 =
                                            FStar_Extraction_ML_UEnv.mlpath_of_lident
                                              g1 constrName
                                             in
                                          (uu____15405,
                                            [FStar_Extraction_ML_Syntax.MLP_Wild])
                                           in
                                        FStar_Extraction_ML_Syntax.MLP_CTor
                                          uu____15398
                                         in
                                      let uu____15408 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_bool_ty)
                                          (FStar_Extraction_ML_Syntax.MLE_Const
                                             (FStar_Extraction_ML_Syntax.MLC_Bool
                                                true))
                                         in
                                      (uu____15397,
                                        FStar_Pervasives_Native.None,
                                        uu____15408)
                                       in
                                    let uu____15412 =
                                      let uu____15423 =
                                        let uu____15432 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.ml_bool_ty)
                                            (FStar_Extraction_ML_Syntax.MLE_Const
                                               (FStar_Extraction_ML_Syntax.MLC_Bool
                                                  false))
                                           in
                                        (FStar_Extraction_ML_Syntax.MLP_Wild,
                                          FStar_Pervasives_Native.None,
                                          uu____15432)
                                         in
                                      [uu____15423]  in
                                    uu____15388 :: uu____15412  in
                                  (uu____15371, uu____15377)  in
                                FStar_Extraction_ML_Syntax.MLE_Match
                                  uu____15356
                                 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                uu____15355
                               in
                            ((FStar_List.append wildcards [(mlid, targ)]),
                              uu____15354)
                             in
                          FStar_Extraction_ML_Syntax.MLE_Fun uu____15342  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty disc_ty)
                          uu____15341
                         in
                      let uu____15493 =
                        FStar_Extraction_ML_UEnv.mlpath_of_lident env
                          discName
                         in
                      (match uu____15493 with
                       | (uu____15494,name) ->
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
  