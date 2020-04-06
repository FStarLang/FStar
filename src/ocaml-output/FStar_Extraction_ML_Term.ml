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
  'uuuuuu77 .
    FStar_Range.range -> (FStar_Errors.raw_error * Prims.string) -> 'uuuuuu77
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_ill_typed_application :
  'uuuuuu113 'uuuuuu114 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'uuuuuu113) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'uuuuuu114
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
  'uuuuuu215 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'uuuuuu215
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
  'uuuuuu249 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'uuuuuu249
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
          (match uu____584 with | (head,uu____603) -> is_arity env head)
      | FStar_Syntax_Syntax.Tm_uinst (head,uu____629) -> is_arity env head
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
      | FStar_Syntax_Syntax.Tm_app (head,uu____1240) -> is_type_aux env head
  
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
  'uuuuuu1314 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu1314) -> Prims.bool
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
    | FStar_Syntax_Syntax.Tm_app (head,args) ->
        let uu____1425 = is_constructor head  in
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
                    | (uenv1,v) -> (uenv1, ((v, t) :: vs)))) ts (g, [])
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
                          | (v,t1) ->
                              FStar_Extraction_ML_Syntax.with_ty t1
                                (FStar_Extraction_ML_Syntax.MLE_Var v)) vs_ts
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
                 | (prefix,last) ->
                     let uu____2927 =
                       let uu____2928 =
                         let uu____2931 =
                           let uu____2934 = aux last ty1 expect1  in
                           [uu____2934]  in
                         FStar_List.append prefix uu____2931  in
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
  'uuuuuu3032 .
    'uuuuuu3032 ->
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
  'uuuuuu3255 .
    'uuuuuu3255 ->
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
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let res =
              let uu____3818 =
                let uu____3819 = FStar_Syntax_Util.un_uinst head  in
                uu____3819.FStar_Syntax_Syntax.n  in
              match uu____3818 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head1,args') ->
                  let uu____3850 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head1, (FStar_List.append args' args)))
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
                             ([], t) false false false
                            in
                         match uu____4172 with
                         | (env1,b2,uu____4197) ->
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
        let uu____4282 = extraction_norm_steps ()  in
        let uu____4283 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Normalize.normalize uu____4282 uu____4283 t0  in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____4302) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4305,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4309 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____4343 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4344 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4345 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4354 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
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
            (fun uu____4430  ->
               fun x  -> match uu____4430 with | (p,s) -> (s, x)) fns1 xs
  
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
            let uu____4482 = FStar_Extraction_ML_Util.is_xtuple d  in
            (match uu____4482 with
             | FStar_Pervasives_Native.Some n ->
                 FStar_Extraction_ML_Syntax.MLP_Tuple pats
             | uu____4489 ->
                 (match q with
                  | FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                      let path =
                        FStar_List.map FStar_Ident.text_of_id
                          ty.FStar_Ident.ns
                         in
                      let fs = record_fields g ty fns pats  in
                      FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                  | uu____4522 -> p))
        | uu____4525 -> p
  
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
                       (fun uu____4627  ->
                          let uu____4628 =
                            let uu____4630 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4630 t'
                             in
                          let uu____4631 =
                            let uu____4633 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4633 t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4628 uu____4631)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____4668 = FStar_Options.codegen ()  in
                uu____4668 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4673 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4686 =
                        let uu____4687 =
                          let uu____4688 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4688  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4687
                         in
                      (uu____4686, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        let uu____4710 =
                          let uu____4711 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                          uu____4711.FStar_TypeChecker_Env.dsenv  in
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          uu____4710 c sw FStar_Range.dummyRange
                         in
                      let uu____4712 = term_as_mlexpr g source_term  in
                      (match uu____4712 with
                       | (mlterm,uu____4724,mlty) -> (mlterm, mlty))
                   in
                (match uu____4673 with
                 | (mlc,ml_ty) ->
                     let uu____4743 = FStar_Extraction_ML_UEnv.new_mlident g
                        in
                     (match uu____4743 with
                      | (g1,x) ->
                          let when_clause =
                            let uu____4769 =
                              let uu____4770 =
                                let uu____4777 =
                                  let uu____4780 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         ml_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Var x)
                                     in
                                  [uu____4780; mlc]  in
                                (FStar_Extraction_ML_Util.prims_op_equality,
                                  uu____4777)
                                 in
                              FStar_Extraction_ML_Syntax.MLE_App uu____4770
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_bool_ty)
                              uu____4769
                             in
                          let uu____4783 = ok ml_ty  in
                          (g1,
                            (FStar_Pervasives_Native.Some
                               ((FStar_Extraction_ML_Syntax.MLP_Var x),
                                 [when_clause])), uu____4783)))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  let uu____4804 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_TcTerm.tc_constant uu____4804
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____4806 =
                  let uu____4815 =
                    let uu____4822 =
                      let uu____4823 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4823  in
                    (uu____4822, [])  in
                  FStar_Pervasives_Native.Some uu____4815  in
                let uu____4832 = ok mlty  in (g, uu____4806, uu____4832)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4845 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4845 with
                 | (g1,x1,uu____4873) ->
                     let uu____4876 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4876))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4914 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4914 with
                 | (g1,x1,uu____4942) ->
                     let uu____4945 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4945))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4981 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____5024 =
                  let uu____5033 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____5033 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____5042;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n;
                          FStar_Extraction_ML_Syntax.mlty = uu____5044;
                          FStar_Extraction_ML_Syntax.loc = uu____5045;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____5047;_}
                      -> (n, ttys)
                  | uu____5054 -> failwith "Expected a constructor"  in
                (match uu____5024 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____5091 = FStar_Util.first_N nTyVars pats  in
                     (match uu____5091 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___853_5195  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____5226  ->
                                               match uu____5226 with
                                               | (p1,uu____5233) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5236,t) ->
                                                        term_as_mlty g t
                                                    | uu____5242 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5246 
                                                              ->
                                                              let uu____5247
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5247);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____5251 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____5251)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____5280 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____5317  ->
                                   match uu____5317 with
                                   | (p1,imp1) ->
                                       let uu____5339 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____5339 with
                                        | (g2,p2,uu____5370) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____5280 with
                           | (g1,tyMLPats) ->
                               let uu____5434 =
                                 FStar_Util.fold_map
                                   (fun uu____5499  ->
                                      fun uu____5500  ->
                                        match (uu____5499, uu____5500) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____5598 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd))
                                              | uu____5658 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____5598 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____5729 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____5729 with
                                                  | (g3,p2,uu____5772) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____5434 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____5893 =
                                      let uu____5904 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5955  ->
                                                match uu___0_5955 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____5997 -> []))
                                         in
                                      FStar_All.pipe_right uu____5904
                                        FStar_List.split
                                       in
                                    (match uu____5893 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____6073 -> false  in
                                         let uu____6083 =
                                           let uu____6092 =
                                             let uu____6099 =
                                               resugar_pat g2
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____6102 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____6099, uu____6102)  in
                                           FStar_Pervasives_Native.Some
                                             uu____6092
                                            in
                                         (g2, uu____6083, pat_ty_compat))))))
  
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
            let uu____6234 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____6234 with
            | (g2,FStar_Pervasives_Native.Some (x,v),b) -> (g2, (x, v), b)
            | uu____6297 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd::tl ->
                let uu____6345 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl
                   in
                FStar_Pervasives_Native.Some uu____6345
             in
          let uu____6346 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____6346 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____6511,t1) ->
                let uu____6513 = FStar_Extraction_ML_UEnv.new_mlident g1  in
                (match uu____6513 with
                 | (g2,x) ->
                     let uu____6538 =
                       let uu____6550 =
                         let uu____6560 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty t0)
                             (FStar_Extraction_ML_Syntax.MLE_Var x)
                            in
                         ((x, t0), uu____6560)  in
                       uu____6550 :: more_args  in
                     eta_args g2 uu____6538 t1)
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6576,uu____6577)
                -> ((FStar_List.rev more_args), t)
            | uu____6602 ->
                let uu____6603 =
                  let uu____6605 =
                    let uu____6607 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu____6607
                      mlAppExpr
                     in
                  let uu____6608 =
                    let uu____6610 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlty uu____6610 t  in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6605 uu____6608
                   in
                failwith uu____6603
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____6644,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields g tyname fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6681 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____6703 = eta_args g [] residualType  in
            match uu____6703 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____6761 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____6761
                 | uu____6762 ->
                     let uu____6774 = FStar_List.unzip eargs  in
                     (match uu____6774 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head,args)
                               ->
                               let body =
                                 let uu____6820 =
                                   let uu____6821 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6821
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6820
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6831 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6835,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6839;
                FStar_Extraction_ML_Syntax.loc = uu____6840;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let fn =
                let uu____6852 =
                  let uu____6857 =
                    let uu____6858 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6858
                      constrname
                     in
                  (uu____6857, f)  in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6852
                 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____6861 ->
                    let uu____6864 =
                      let uu____6871 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6871, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6864
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
                     FStar_Extraction_ML_Syntax.mlty = uu____6875;
                     FStar_Extraction_ML_Syntax.loc = uu____6876;_},uu____6877);
                FStar_Extraction_ML_Syntax.mlty = uu____6878;
                FStar_Extraction_ML_Syntax.loc = uu____6879;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let fn =
                let uu____6895 =
                  let uu____6900 =
                    let uu____6901 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6901
                      constrname
                     in
                  (uu____6900, f)  in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6895
                 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____6904 ->
                    let uu____6907 =
                      let uu____6914 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6914, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6907
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6918;
                FStar_Extraction_ML_Syntax.loc = uu____6919;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6927 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6927
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6931;
                FStar_Extraction_ML_Syntax.loc = uu____6932;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6934)) ->
              let uu____6947 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6947
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6951;
                     FStar_Extraction_ML_Syntax.loc = uu____6952;_},uu____6953);
                FStar_Extraction_ML_Syntax.mlty = uu____6954;
                FStar_Extraction_ML_Syntax.loc = uu____6955;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6967 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6967
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6971;
                     FStar_Extraction_ML_Syntax.loc = uu____6972;_},uu____6973);
                FStar_Extraction_ML_Syntax.mlty = uu____6974;
                FStar_Extraction_ML_Syntax.loc = uu____6975;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6977)) ->
              let uu____6994 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6994
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____7000 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7000
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7004)) ->
              let uu____7013 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7013
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7017;
                FStar_Extraction_ML_Syntax.loc = uu____7018;_},uu____7019),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____7026 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7026
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7030;
                FStar_Extraction_ML_Syntax.loc = uu____7031;_},uu____7032),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7033)) ->
              let uu____7046 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7046
          | uu____7049 -> mlAppExpr
  
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
        | uu____7080 -> (ml_e, tag)
  
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
      let maybe_generalize uu____7141 =
        match uu____7141 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____7162;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____7167;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____7248 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____7325 =
              let uu____7327 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Util.must_erase_for_extraction uu____7327
                lbtyp1
               in
            if uu____7325
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____7412 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____7412 (is_type_binder g) ->
                   let uu____7434 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____7434 with
                    | (bs1,c1) ->
                        let uu____7460 =
                          let uu____7473 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____7519 = is_type_binder g x  in
                                 Prims.op_Negation uu____7519) bs1
                             in
                          match uu____7473 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____7646 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____7646)
                           in
                        (match uu____7460 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____7708 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____7708
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____7757 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____7757 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7809 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____7809 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7912  ->
                                                       fun uu____7913  ->
                                                         match (uu____7912,
                                                                 uu____7913)
                                                         with
                                                         | ((x,uu____7939),
                                                            (y,uu____7941))
                                                             ->
                                                             let uu____7962 =
                                                               let uu____7969
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____7969)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7962)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____7986  ->
                                                       match uu____7986 with
                                                       | (a,uu____7994) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a false) g
                                                  targs
                                                 in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty
                                                 in
                                              let polytype =
                                                let uu____8006 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____8026  ->
                                                          match uu____8026
                                                          with
                                                          | (x,uu____8035) ->
                                                              let uu____8040
                                                                =
                                                                FStar_Extraction_ML_UEnv.lookup_ty
                                                                  env x
                                                                 in
                                                              uu____8040.FStar_Extraction_ML_UEnv.ty_b_name))
                                                   in
                                                (uu____8006, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____8052 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____8052)
                                                      ||
                                                      (let uu____8055 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____8055)
                                                | uu____8057 -> false  in
                                              let rest_args1 =
                                                if add_unit
                                                then
                                                  let uu____8069 =
                                                    unit_binder ()  in
                                                  uu____8069 :: rest_args
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____8126 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8145  ->
                                           match uu____8145 with
                                           | (a,uu____8153) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8165 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8185  ->
                                              match uu____8185 with
                                              | (x,uu____8194) ->
                                                  let uu____8199 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8199.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8165, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8239  ->
                                            match uu____8239 with
                                            | (bv,uu____8247) ->
                                                let uu____8252 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8252
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____8282 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8295  ->
                                           match uu____8295 with
                                           | (a,uu____8303) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8315 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8335  ->
                                              match uu____8335 with
                                              | (x,uu____8344) ->
                                                  let uu____8349 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8349.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8315, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8389  ->
                                            match uu____8389 with
                                            | (bv,uu____8397) ->
                                                let uu____8402 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8402
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
                              | FStar_Syntax_Syntax.Tm_name uu____8432 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8445  ->
                                           match uu____8445 with
                                           | (a,uu____8453) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8465 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8485  ->
                                              match uu____8485 with
                                              | (x,uu____8494) ->
                                                  let uu____8499 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8499.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8465, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8539  ->
                                            match uu____8539 with
                                            | (bv,uu____8547) ->
                                                let uu____8552 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8552
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
                              | uu____8582 -> err_value_restriction lbdef1)))
               | uu____8602 -> no_gen ())
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
           fun uu____8753  ->
             match uu____8753 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____8814 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____8814 with
                  | (env1,uu____8831,exp_binding) ->
                      let uu____8835 =
                        let uu____8840 = FStar_Util.right lbname  in
                        (uu____8840, exp_binding)  in
                      (env1, uu____8835))) g lbs1
  
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
            (fun uu____8907  ->
               let uu____8908 = FStar_Syntax_Print.term_to_string e  in
               let uu____8910 =
                 let uu____8912 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g  in
                 FStar_Extraction_ML_Code.string_of_mlty uu____8912 ty  in
               let uu____8913 = FStar_Extraction_ML_Util.eff_to_string f  in
               FStar_Util.print3 "Checking %s at type %s and eff %s\n"
                 uu____8908 uu____8910 uu____8913);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____8920) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8921 ->
               let uu____8926 = term_as_mlexpr g e  in
               (match uu____8926 with
                | (ml_e,tag,t) ->
                    let uu____8940 = FStar_Extraction_ML_Util.eff_leq tag f
                       in
                    if uu____8940
                    then
                      let uu____8947 =
                        maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t ty
                         in
                      (uu____8947, ty)
                    else
                      (match (tag, f, ty) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST
                          ,FStar_Extraction_ML_Syntax.E_PURE
                          ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                           let uu____8954 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t
                               ty
                              in
                           (uu____8954, ty)
                       | uu____8955 ->
                           (err_unexpected_eff g e ty f tag;
                            (let uu____8963 =
                               maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e
                                 t ty
                                in
                             (uu____8963, ty))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____8972 = term_as_mlexpr' g e  in
      match uu____8972 with
      | (e1,f,t) ->
          let uu____8988 = maybe_promote_effect e1 f t  in
          (match uu____8988 with | (e2,f1) -> (e2, f1, t))

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
           let uu____9014 =
             let uu____9016 =
               FStar_Range.string_of_range top1.FStar_Syntax_Syntax.pos  in
             let uu____9018 = FStar_Syntax_Print.tag_of_term top1  in
             let uu____9020 = FStar_Syntax_Print.term_to_string top1  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____9016 uu____9018 uu____9020
              in
           FStar_Util.print_string uu____9014);
      (let is_match t =
         let uu____9030 =
           let uu____9031 =
             let uu____9034 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9034 FStar_Syntax_Util.unascribe  in
           uu____9031.FStar_Syntax_Syntax.n  in
         match uu____9030 with
         | FStar_Syntax_Syntax.Tm_match uu____9038 -> true
         | uu____9062 -> false  in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____9081  ->
              match uu____9081 with
              | (t,uu____9090) ->
                  let uu____9095 =
                    let uu____9096 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
                    uu____9096.FStar_Syntax_Syntax.n  in
                  (match uu____9095 with
                   | FStar_Syntax_Syntax.Tm_name uu____9102 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____9104 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____9106 -> true
                   | uu____9108 -> false))
          in
       let apply_to_match_branches head args =
         let uu____9147 =
           let uu____9148 =
             let uu____9151 =
               FStar_All.pipe_right head FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9151 FStar_Syntax_Util.unascribe  in
           uu____9148.FStar_Syntax_Syntax.n  in
         match uu____9147 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee,branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____9275  ->
                       match uu____9275 with
                       | (pat,when_opt,body) ->
                           (pat, when_opt,
                             (let uu___1320_9332 = body  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1320_9332.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1320_9332.FStar_Syntax_Syntax.vars)
                              }))))
                in
             let uu___1323_9347 = head  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1323_9347.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1323_9347.FStar_Syntax_Syntax.vars)
             }
         | uu____9368 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match"
          in
       let t = FStar_Syntax_Subst.compress top1  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9379 =
             let uu____9381 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9381
              in
           failwith uu____9379
       | FStar_Syntax_Syntax.Tm_delayed uu____9390 ->
           let uu____9405 =
             let uu____9407 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9407
              in
           failwith uu____9405
       | FStar_Syntax_Syntax.Tm_uvar uu____9416 ->
           let uu____9429 =
             let uu____9431 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9431
              in
           failwith uu____9429
       | FStar_Syntax_Syntax.Tm_bvar uu____9440 ->
           let uu____9441 =
             let uu____9443 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9443
              in
           failwith uu____9441
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9453 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____9453
       | FStar_Syntax_Syntax.Tm_type uu____9454 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9455 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9462 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____9478;_})
           ->
           let uu____9491 =
             let uu____9492 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9492  in
           (match uu____9491 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9499;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9501;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9502;_} ->
                let uu____9505 =
                  let uu____9506 =
                    let uu____9507 =
                      let uu____9514 =
                        let uu____9517 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____9517]  in
                      (fw, uu____9514)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9507  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9506
                   in
                (uu____9505, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9535 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____9535 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9543 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____9543 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____9554 =
                         let uu____9561 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____9561
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____9554 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____9569 =
                         let uu____9580 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____9580]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9569
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9607 =
                    let uu____9614 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____9614 tv  in
                  uu____9607 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____9622 =
                    let uu____9633 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____9633]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9622
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____9660)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9693 =
                  let uu____9700 =
                    let uu____9709 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.effect_decl_opt uu____9709 m  in
                  FStar_Util.must uu____9700  in
                (match uu____9693 with
                 | (ed,qualifiers) ->
                     let uu____9728 =
                       let uu____9730 =
                         let uu____9732 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                         FStar_TypeChecker_Env.is_reifiable_effect uu____9732
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____9730  in
                     if uu____9728
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9749 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9751) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9757) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9763 =
             let uu____9770 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_TcTerm.type_of_tot_term uu____9770 t  in
           (match uu____9763 with
            | (uu____9777,ty,uu____9779) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____9781 =
                  let uu____9782 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9782  in
                (uu____9781, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9783 ->
           let uu____9784 = is_type g t  in
           if uu____9784
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9795 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____9795 with
              | (FStar_Util.Inl uu____9808,uu____9809) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9814;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9817;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____9835 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____9835, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9836 -> instantiate_maybe_partial g x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9838 = is_type g t  in
           if uu____9838
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9849 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____9849 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9858;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9861;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9869  ->
                        let uu____9870 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____9872 =
                          let uu____9874 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            uu____9874 x
                           in
                        let uu____9875 =
                          let uu____9877 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlty uu____9877
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9870 uu____9872 uu____9875);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____9889 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____9889, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9890 -> instantiate_maybe_partial g x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____9918 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____9918 with
            | (bs1,body1) ->
                let uu____9931 = binders_as_ml_binders g bs1  in
                (match uu____9931 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9967 =
                             let uu____9969 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Env.is_reifiable_rc uu____9969
                               rc
                              in
                           if uu____9967
                           then
                             let uu____9971 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Util.reify_body uu____9971
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Unascribe] body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9977  ->
                                 let uu____9978 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9978);
                            body1)
                        in
                     let uu____9981 = term_as_mlexpr env body2  in
                     (match uu____9981 with
                      | (ml_body,f,t1) ->
                          let uu____9997 =
                            FStar_List.fold_right
                              (fun uu____10017  ->
                                 fun uu____10018  ->
                                   match (uu____10017, uu____10018) with
                                   | ((uu____10041,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____9997 with
                           | (f1,tfun) ->
                               let uu____10064 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____10064, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____10072;
              FStar_Syntax_Syntax.vars = uu____10073;_},(a1,uu____10075)::[])
           ->
           let ty =
             let uu____10115 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____10115  in
           let uu____10116 =
             let uu____10117 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____10117
              in
           (uu____10116, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____10118;
              FStar_Syntax_Syntax.vars = uu____10119;_},(t1,uu____10121)::
            (r,uu____10123)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____10178);
              FStar_Syntax_Syntax.pos = uu____10179;
              FStar_Syntax_Syntax.vars = uu____10180;_},uu____10181)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head,args) when
           (is_match head) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____10240 =
             FStar_All.pipe_right args (apply_to_match_branches head)  in
           FStar_All.pipe_right uu____10240 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_10294  ->
                        match uu___1_10294 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____10297 -> false)))
              in
           let uu____10299 =
             let uu____10300 =
               let uu____10303 =
                 FStar_All.pipe_right head FStar_Syntax_Subst.compress  in
               FStar_All.pipe_right uu____10303 FStar_Syntax_Util.unascribe
                in
             uu____10300.FStar_Syntax_Syntax.n  in
           (match uu____10299 with
            | FStar_Syntax_Syntax.Tm_abs (bs,uu____10313,_rc) ->
                let uu____10339 =
                  let uu____10340 =
                    let uu____10345 =
                      FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses]
                      uu____10345
                     in
                  FStar_All.pipe_right t uu____10340  in
                FStar_All.pipe_right uu____10339 (term_as_mlexpr g)
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                let e =
                  let uu____10353 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  let uu____10354 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg uu____10353
                    [FStar_TypeChecker_Env.Inlining;
                    FStar_TypeChecker_Env.Unascribe] head uu____10354
                   in
                let tm =
                  let uu____10366 =
                    let uu____10371 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____10372 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____10371 uu____10372  in
                  uu____10366 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____10381 ->
                let rec extract_app is_data uu____10430 uu____10431 restArgs
                  =
                  match (uu____10430, uu____10431) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____10512 =
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
                         (fun uu____10539  ->
                            let uu____10540 =
                              let uu____10542 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              let uu____10543 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____10542 uu____10543
                               in
                            let uu____10544 =
                              let uu____10546 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlty
                                uu____10546 t1
                               in
                            let uu____10547 =
                              match restArgs with
                              | [] -> "none"
                              | (hd,uu____10558)::uu____10559 ->
                                  FStar_Syntax_Print.term_to_string hd
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10540 uu____10544 uu____10547);
                       (match (restArgs, t1) with
                        | ([],uu____10593) ->
                            let app =
                              let uu____10609 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10609
                               in
                            (app, f, t1)
                        | ((arg,uu____10611)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10642 =
                              let uu____10647 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____10647, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10642 rest
                        | ((e0,uu____10659)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____10692 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head)
                                 in
                              if uu____10692
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____10697 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____10697 with
                             | (e01,tInferred) ->
                                 let uu____10710 =
                                   let uu____10715 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____10715, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10710 rest)
                        | uu____10726 ->
                            let uu____10739 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____10739 with
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
                                        let head1 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.MLTY_Top)
                                            (FStar_Extraction_ML_Syntax.MLE_App
                                               (mlhead, mlargs))
                                           in
                                        maybe_coerce
                                          top1.FStar_Syntax_Syntax.pos g
                                          head1
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t2
                                         in
                                      extract_app is_data (mlhead1, [])
                                        (f, t2) restArgs
                                  | uu____10811 ->
                                      let mlhead1 =
                                        let mlargs =
                                          FStar_All.pipe_right
                                            (FStar_List.rev mlargs_f)
                                            (FStar_List.map
                                               FStar_Pervasives_Native.fst)
                                           in
                                        let head1 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.MLTY_Top)
                                            (FStar_Extraction_ML_Syntax.MLE_App
                                               (mlhead, mlargs))
                                           in
                                        maybe_coerce
                                          top1.FStar_Syntax_Syntax.pos g
                                          head1
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t1
                                         in
                                      err_ill_typed_application g top1
                                        mlhead1 restArgs t1))))
                   in
                let extract_app_maybe_projector is_data mlhead uu____10882
                  args1 =
                  match uu____10882 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10912)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10996))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____10998,f',t3)) ->
                                 let uu____11036 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____11036 t3
                             | uu____11037 -> (args2, f1, t2)  in
                           let uu____11062 = remove_implicits args1 f t1  in
                           (match uu____11062 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____11118 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____11142 =
                  let head1 = FStar_Syntax_Util.un_uinst head  in
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____11150 ->
                      let uu____11151 =
                        let uu____11172 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1  in
                        match uu____11172 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11211  ->
                                  let uu____11212 =
                                    FStar_Syntax_Print.term_to_string head1
                                     in
                                  let uu____11214 =
                                    let uu____11216 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11216
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11217 =
                                    let uu____11219 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11219
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11220 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11212 uu____11214 uu____11217
                                    uu____11220);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11247 -> failwith "FIXME Ty"  in
                      (match uu____11151 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11323)::uu____11324 -> is_type g a
                             | uu____11351 -> false  in
                           let uu____11363 =
                             match vars with
                             | uu____11392::uu____11393 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11407 ->
                                 let n = FStar_List.length vars  in
                                 let uu____11413 =
                                   if (FStar_List.length args) <= n
                                   then
                                     let uu____11451 =
                                       FStar_List.map
                                         (fun uu____11463  ->
                                            match uu____11463 with
                                            | (x,uu____11471) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____11451, [])
                                   else
                                     (let uu____11494 =
                                        FStar_Util.first_N n args  in
                                      match uu____11494 with
                                      | (prefix,rest) ->
                                          let uu____11583 =
                                            FStar_List.map
                                              (fun uu____11595  ->
                                                 match uu____11595 with
                                                 | (x,uu____11603) ->
                                                     term_as_mlty g x) prefix
                                             in
                                          (uu____11583, rest))
                                    in
                                 (match uu____11413 with
                                  | (provided_type_args,rest) ->
                                      let uu____11654 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____11663 ->
                                            let uu____11664 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11664 with
                                             | (head2,uu____11676,t2) ->
                                                 (head2, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____11678 ->
                                            let uu____11680 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11680 with
                                             | (head2,uu____11692,t2) ->
                                                 (head2, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head2,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____11695;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____11696;_}::[])
                                            ->
                                            let uu____11699 =
                                              instantiate_maybe_partial g
                                                head2 (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11699 with
                                             | (head3,uu____11711,t2) ->
                                                 let uu____11713 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head3,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____11713, t2))
                                        | uu____11716 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____11654 with
                                       | (head2,t2) -> (head2, t2, rest)))
                              in
                           (match uu____11363 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11783 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____11783,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11784 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11793 ->
                      let uu____11794 =
                        let uu____11815 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1  in
                        match uu____11815 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11854  ->
                                  let uu____11855 =
                                    FStar_Syntax_Print.term_to_string head1
                                     in
                                  let uu____11857 =
                                    let uu____11859 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11859
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11860 =
                                    let uu____11862 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11862
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11863 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11855 uu____11857 uu____11860
                                    uu____11863);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11890 -> failwith "FIXME Ty"  in
                      (match uu____11794 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11966)::uu____11967 -> is_type g a
                             | uu____11994 -> false  in
                           let uu____12006 =
                             match vars with
                             | uu____12035::uu____12036 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____12050 ->
                                 let n = FStar_List.length vars  in
                                 let uu____12056 =
                                   if (FStar_List.length args) <= n
                                   then
                                     let uu____12094 =
                                       FStar_List.map
                                         (fun uu____12106  ->
                                            match uu____12106 with
                                            | (x,uu____12114) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____12094, [])
                                   else
                                     (let uu____12137 =
                                        FStar_Util.first_N n args  in
                                      match uu____12137 with
                                      | (prefix,rest) ->
                                          let uu____12226 =
                                            FStar_List.map
                                              (fun uu____12238  ->
                                                 match uu____12238 with
                                                 | (x,uu____12246) ->
                                                     term_as_mlty g x) prefix
                                             in
                                          (uu____12226, rest))
                                    in
                                 (match uu____12056 with
                                  | (provided_type_args,rest) ->
                                      let uu____12297 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____12306 ->
                                            let uu____12307 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12307 with
                                             | (head2,uu____12319,t2) ->
                                                 (head2, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____12321 ->
                                            let uu____12323 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12323 with
                                             | (head2,uu____12335,t2) ->
                                                 (head2, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head2,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____12338;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____12339;_}::[])
                                            ->
                                            let uu____12342 =
                                              instantiate_maybe_partial g
                                                head2 (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12342 with
                                             | (head3,uu____12354,t2) ->
                                                 let uu____12356 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head3,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____12356, t2))
                                        | uu____12359 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____12297 with
                                       | (head2,t2) -> (head2, t2, rest)))
                              in
                           (match uu____12006 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12426 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____12426,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12427 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12436 ->
                      let uu____12437 = term_as_mlexpr g head1  in
                      (match uu____12437 with
                       | (head2,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head2 (f, t1) args)
                   in
                let uu____12453 = is_type g t  in
                if uu____12453
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12464 =
                     let uu____12465 = FStar_Syntax_Util.un_uinst head  in
                     uu____12465.FStar_Syntax_Syntax.n  in
                   match uu____12464 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12475 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____12475 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12484 -> extract_app_with_instantiations ())
                   | uu____12487 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____12490),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12555 =
                   let uu____12556 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                      in
                   maybe_reify_comp g uu____12556 c  in
                 term_as_mlty g uu____12555
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____12560 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____12560 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e') when
           (let uu____12592 = FStar_Syntax_Syntax.is_top_level [lb]  in
            Prims.op_Negation uu____12592) &&
             (let uu____12595 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs
                 in
              FStar_Util.is_some uu____12595)
           ->
           let b =
             let uu____12605 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                in
             (uu____12605, FStar_Pervasives_Native.None)  in
           let uu____12608 = FStar_Syntax_Subst.open_term_1 b e'  in
           (match uu____12608 with
            | ((x,uu____12620),body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str,uu____12635)::[]) ->
                      let uu____12660 =
                        let uu____12661 = FStar_Syntax_Subst.compress str  in
                        uu____12661.FStar_Syntax_Syntax.n  in
                      (match uu____12660 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s,uu____12667)) ->
                           let id =
                             let uu____12671 =
                               let uu____12677 =
                                 FStar_Syntax_Syntax.range_of_bv x  in
                               (s, uu____12677)  in
                             FStar_Ident.mk_ident uu____12671  in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             }  in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv  in
                           FStar_Pervasives_Native.Some bv1
                       | uu____12682 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____12683 ->
                      (FStar_Errors.log_issue top1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `rename_let`");
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                   in
                let remove_attr attrs =
                  let uu____12703 =
                    FStar_List.partition
                      (fun attr  ->
                         let uu____12715 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr]
                            in
                         FStar_Util.is_some uu____12715)
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match uu____12703 with
                  | (uu____12720,other_attrs) -> other_attrs  in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None  ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs  in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1783_12748 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1783_12748.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1783_12748.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1783_12748.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1783_12748.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1783_12748.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1783_12748.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs  in
                      let rename =
                        let uu____12756 =
                          let uu____12757 =
                            let uu____12764 =
                              FStar_Syntax_Syntax.bv_to_name y  in
                            (x, uu____12764)  in
                          FStar_Syntax_Syntax.NT uu____12757  in
                        [uu____12756]  in
                      let body1 =
                        let uu____12770 =
                          FStar_Syntax_Subst.subst rename body  in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____12770
                         in
                      let lb1 =
                        let uu___1790_12786 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1790_12786.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1790_12786.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1790_12786.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1790_12786.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1790_12786.FStar_Syntax_Syntax.lbpos)
                        }  in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1)
                   in
                let top2 =
                  let uu___1794_12803 = top1  in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1794_12803.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1794_12803.FStar_Syntax_Syntax.vars)
                  }  in
                term_as_mlexpr' g top2)
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____12826 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12842 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____12842
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____12857 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____12857  in
                   let lb1 =
                     let uu___1808_12859 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1808_12859.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1808_12859.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1808_12859.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1808_12859.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1808_12859.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1808_12859.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____12826 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____12884 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      let uu____12885 =
                        let uu____12886 =
                          let uu____12887 =
                            let uu____12891 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Pervasives_Native.fst uu____12891  in
                          let uu____12904 =
                            let uu____12908 =
                              let uu____12910 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Pervasives_Native.snd uu____12910  in
                            [uu____12908]  in
                          FStar_List.append uu____12887 uu____12904  in
                        FStar_Ident.lid_of_path uu____12886
                          FStar_Range.dummyRange
                         in
                      FStar_TypeChecker_Env.set_current_module uu____12884
                        uu____12885
                       in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let lbdef =
                              let uu____12937 = FStar_Options.ml_ish ()  in
                              if uu____12937
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____12949 =
                                   let uu____12950 =
                                     let uu____12951 =
                                       extraction_norm_steps ()  in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____12951
                                      in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____12950 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____12954 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____12954
                                 then
                                   ((let uu____12964 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____12964);
                                    (let a =
                                       let uu____12970 =
                                         let uu____12972 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____12972
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____12970 norm_call
                                        in
                                     a))
                                 else norm_call ())
                               in
                            let uu___1825_12979 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1825_12979.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1825_12979.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1825_12979.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1825_12979.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1825_12979.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1825_12979.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____13032 =
                  match uu____13032 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____13188  ->
                               match uu____13188 with
                               | (a,uu____13196) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     false) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____13203 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____13203 with
                       | (e1,ty) ->
                           let uu____13214 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____13214 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____13226 -> []  in
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
                let uu____13257 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____13354  ->
                         match uu____13354 with
                         | (env,lbs4) ->
                             let uu____13488 = lb  in
                             (match uu____13488 with
                              | (lbname,uu____13539,(t1,(uu____13541,polytype)),add_unit,uu____13544)
                                  ->
                                  let uu____13559 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____13559 with
                                   | (env1,nm,uu____13600) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____13257 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____13879 = term_as_mlexpr env_body e'1  in
                     (match uu____13879 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____13896 =
                              let uu____13899 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____13899  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13896
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____13912 =
                            let uu____13913 =
                              let uu____13914 =
                                let uu____13915 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____13915)  in
                              mk_MLE_Let top_level uu____13914 e'2  in
                            let uu____13924 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13913 uu____13924
                             in
                          (uu____13912, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____13963 = term_as_mlexpr g scrutinee  in
           (match uu____13963 with
            | (e,f_e,t_e) ->
                let uu____13979 = check_pats_for_ite pats  in
                (match uu____13979 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____14044 = term_as_mlexpr g then_e1  in
                            (match uu____14044 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____14060 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____14060 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____14076 =
                                        let uu____14087 =
                                          type_leq g t_then t_else  in
                                        if uu____14087
                                        then (t_else, no_lift)
                                        else
                                          (let uu____14108 =
                                             type_leq g t_else t_then  in
                                           if uu____14108
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____14076 with
                                       | (t_branch,maybe_lift) ->
                                           let uu____14155 =
                                             let uu____14156 =
                                               let uu____14157 =
                                                 let uu____14166 =
                                                   maybe_lift then_mle t_then
                                                    in
                                                 let uu____14167 =
                                                   let uu____14170 =
                                                     maybe_lift else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____14170
                                                    in
                                                 (e, uu____14166,
                                                   uu____14167)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____14157
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____14156
                                              in
                                           let uu____14173 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____14155, uu____14173,
                                             t_branch))))
                        | uu____14174 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____14192 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____14291 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____14291 with
                                    | (pat,when_opt,branch) ->
                                        let uu____14336 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____14336 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____14398 =
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
                                                   let uu____14421 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____14421 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____14398 with
                                              | (when_opt1,f_when) ->
                                                  let uu____14471 =
                                                    term_as_mlexpr env branch
                                                     in
                                                  (match uu____14471 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____14506 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14583 
                                                                 ->
                                                                 match uu____14583
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
                                                         uu____14506)))))
                               true)
                           in
                        match uu____14192 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14754  ->
                                      let uu____14755 =
                                        let uu____14757 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu____14757 e
                                         in
                                      let uu____14758 =
                                        let uu____14760 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu____14760 t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14755 uu____14758);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14786 =
                                   let uu____14787 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14787
                                    in
                                 (match uu____14786 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14794;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14796;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____14797;_}
                                      ->
                                      let uu____14800 =
                                        let uu____14801 =
                                          let uu____14802 =
                                            let uu____14809 =
                                              let uu____14812 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____14812]  in
                                            (fw, uu____14809)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14802
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14801
                                         in
                                      (uu____14800,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14816,uu____14817,(uu____14818,f_first,t_first))::rest
                                 ->
                                 let uu____14878 =
                                   FStar_List.fold_left
                                     (fun uu____14920  ->
                                        fun uu____14921  ->
                                          match (uu____14920, uu____14921)
                                          with
                                          | ((topt,f),(uu____14978,uu____14979,
                                                       (uu____14980,f_branch,t_branch)))
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
                                                    let uu____15036 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____15036
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____15043 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____15043
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
                                 (match uu____14878 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____15141  ->
                                                match uu____15141 with
                                                | (p,(wopt,uu____15170),
                                                   (b1,uu____15172,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____15191 -> b1
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
                                      let uu____15196 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____15196, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____15223 =
          let uu____15228 =
            let uu____15237 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_lid uu____15237 discName  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15228  in
        match uu____15223 with
        | (uu____15254,fstar_disc_type) ->
            let uu____15256 =
              let uu____15268 =
                let uu____15269 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____15269.FStar_Syntax_Syntax.n  in
              match uu____15268 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15284) ->
                  let binders1 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_15339  ->
                            match uu___2_15339 with
                            | (uu____15347,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15348)) ->
                                true
                            | uu____15353 -> false))
                     in
                  FStar_List.fold_right
                    (fun uu____15385  ->
                       fun uu____15386  ->
                         match uu____15386 with
                         | (g,vs) ->
                             let uu____15431 =
                               FStar_Extraction_ML_UEnv.new_mlident g  in
                             (match uu____15431 with
                              | (g1,v) ->
                                  (g1,
                                    ((v, FStar_Extraction_ML_Syntax.MLTY_Top)
                                    :: vs)))) binders1 (env, [])
              | uu____15477 -> failwith "Discriminator must be a function"
               in
            (match uu____15256 with
             | (g,wildcards) ->
                 let uu____15506 = FStar_Extraction_ML_UEnv.new_mlident g  in
                 (match uu____15506 with
                  | (g1,mlid) ->
                      let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let discrBody =
                        let uu____15519 =
                          let uu____15520 =
                            let uu____15532 =
                              let uu____15533 =
                                let uu____15534 =
                                  let uu____15549 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         targ)
                                      (FStar_Extraction_ML_Syntax.MLE_Name
                                         ([], mlid))
                                     in
                                  let uu____15555 =
                                    let uu____15566 =
                                      let uu____15575 =
                                        let uu____15576 =
                                          let uu____15583 =
                                            FStar_Extraction_ML_UEnv.mlpath_of_lident
                                              g1 constrName
                                             in
                                          (uu____15583,
                                            [FStar_Extraction_ML_Syntax.MLP_Wild])
                                           in
                                        FStar_Extraction_ML_Syntax.MLP_CTor
                                          uu____15576
                                         in
                                      let uu____15586 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_bool_ty)
                                          (FStar_Extraction_ML_Syntax.MLE_Const
                                             (FStar_Extraction_ML_Syntax.MLC_Bool
                                                true))
                                         in
                                      (uu____15575,
                                        FStar_Pervasives_Native.None,
                                        uu____15586)
                                       in
                                    let uu____15590 =
                                      let uu____15601 =
                                        let uu____15610 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.ml_bool_ty)
                                            (FStar_Extraction_ML_Syntax.MLE_Const
                                               (FStar_Extraction_ML_Syntax.MLC_Bool
                                                  false))
                                           in
                                        (FStar_Extraction_ML_Syntax.MLP_Wild,
                                          FStar_Pervasives_Native.None,
                                          uu____15610)
                                         in
                                      [uu____15601]  in
                                    uu____15566 :: uu____15590  in
                                  (uu____15549, uu____15555)  in
                                FStar_Extraction_ML_Syntax.MLE_Match
                                  uu____15534
                                 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                uu____15533
                               in
                            ((FStar_List.append wildcards [(mlid, targ)]),
                              uu____15532)
                             in
                          FStar_Extraction_ML_Syntax.MLE_Fun uu____15520  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty disc_ty)
                          uu____15519
                         in
                      let uu____15671 =
                        FStar_Extraction_ML_UEnv.mlpath_of_lident env
                          discName
                         in
                      (match uu____15671 with
                       | (uu____15672,name) ->
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
  