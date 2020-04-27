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
    let uu____346 =
      let uu____349 = FStar_Ident.string_of_lid l  in
      FStar_Util.smap_try_find cache uu____349  in
    match uu____346 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____353 =
            let uu____360 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
            FStar_TypeChecker_Env.lookup_effect_abbrev uu____360
              [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____353 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____365,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        ((let uu____372 = FStar_Ident.string_of_lid l  in
          FStar_Util.smap_add cache uu____372 res);
         res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____377 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____377
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____382 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____382
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              let uu____396 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Env.effect_decl_opt uu____396 l1  in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____409 =
                  let uu____411 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_Env.is_reifiable_effect uu____411
                    ed.FStar_Syntax_Syntax.mname
                   in
                if uu____409
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____434 =
        let uu____435 = FStar_Syntax_Subst.compress t1  in
        uu____435.FStar_Syntax_Syntax.n  in
      match uu____434 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____441 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____458 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____487 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____497 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____497
      | FStar_Syntax_Syntax.Tm_uvar uu____498 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____512 -> false
      | FStar_Syntax_Syntax.Tm_name uu____514 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____516 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____524 -> false
      | FStar_Syntax_Syntax.Tm_type uu____526 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____528,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let topt =
            let uu____558 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] uu____558
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match topt with
           | FStar_Pervasives_Native.None  -> false
           | FStar_Pervasives_Native.Some (uu____565,t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____571 ->
          let uu____588 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____588 with | (head,uu____607) -> is_arity env head)
      | FStar_Syntax_Syntax.Tm_uinst (head,uu____633) -> is_arity env head
      | FStar_Syntax_Syntax.Tm_refine (x,uu____639) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____644,body,uu____646) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____671,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____691,branches) ->
          (match branches with
           | (uu____730,uu____731,e)::uu____733 -> is_arity env e
           | uu____780 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____812 ->
          let uu____827 =
            let uu____829 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____829  in
          failwith uu____827
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____833 =
            let uu____835 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____835  in
          failwith uu____833
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____840 = FStar_Syntax_Util.unfold_lazy i  in
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
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____879;_},s)
          ->
          let uu____930 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____930
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____931;
            FStar_Syntax_Syntax.index = uu____932;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____937;
            FStar_Syntax_Syntax.index = uu____938;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____944,uu____945) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____987) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____994) ->
          let uu____1019 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____1019 with
           | (uu____1025,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____1045 =
            let uu____1050 =
              let uu____1051 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1051]  in
            FStar_Syntax_Subst.open_term uu____1050 body  in
          (match uu____1045 with
           | (uu____1071,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1073,lbs),body) ->
          let uu____1093 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____1093 with
           | (uu____1101,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1107,branches) ->
          (match branches with
           | b::uu____1147 ->
               let uu____1192 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1192 with
                | (uu____1194,uu____1195,e) -> is_type_aux env e)
           | uu____1213 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1231 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1240) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head,uu____1246) -> is_type_aux env head
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1287  ->
           let uu____1288 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1290 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1288
             uu____1290);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1299  ->
            if b
            then
              let uu____1301 = FStar_Syntax_Print.term_to_string t  in
              let uu____1303 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1301
                uu____1303
            else
              (let uu____1308 = FStar_Syntax_Print.term_to_string t  in
               let uu____1310 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1308 uu____1310));
       b)
  
let is_type_binder :
  'uuuuuu1320 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu1320) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1347 =
      let uu____1348 = FStar_Syntax_Subst.compress t  in
      uu____1348.FStar_Syntax_Syntax.n  in
    match uu____1347 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1352;
          FStar_Syntax_Syntax.fv_delta = uu____1353;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1355;
          FStar_Syntax_Syntax.fv_delta = uu____1356;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1357);_}
        -> true
    | uu____1365 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1374 =
      let uu____1375 = FStar_Syntax_Subst.compress t  in
      uu____1375.FStar_Syntax_Syntax.n  in
    match uu____1374 with
    | FStar_Syntax_Syntax.Tm_constant uu____1379 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1381 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1383 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1385 -> true
    | FStar_Syntax_Syntax.Tm_app (head,args) ->
        let uu____1431 = is_constructor head  in
        if uu____1431
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1453  ->
                  match uu____1453 with
                  | (te,uu____1462) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1471) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1477,uu____1478) ->
        is_fstar_value t1
    | uu____1519 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1529 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1531 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1534 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1536 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1549,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1558,fields) ->
        FStar_Util.for_all
          (fun uu____1588  ->
             match uu____1588 with | (uu____1595,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1600) -> is_ml_value h
    | uu____1605 -> false
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1687 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1689 = FStar_Syntax_Util.is_fun e'  in
          if uu____1689
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : unit -> FStar_Syntax_Syntax.binder) =
  fun uu____1707  ->
    let uu____1708 =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.t_unit
       in
    FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1708
  
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
      (let uu____1799 = FStar_List.hd l  in
       match uu____1799 with
       | (p1,w1,e1) ->
           let uu____1834 =
             let uu____1843 = FStar_List.tl l  in FStar_List.hd uu____1843
              in
           (match uu____1834 with
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
                 | uu____1927 -> def)))
  
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
      let uu____1992 =
        FStar_List.fold_right
          (fun t  ->
             fun uu____2023  ->
               match uu____2023 with
               | (uenv,vs) ->
                   let uu____2062 = FStar_Extraction_ML_UEnv.new_mlident uenv
                      in
                   (match uu____2062 with
                    | (uenv1,v) -> (uenv1, ((v, t) :: vs)))) ts (g, [])
         in
      match uu____1992 with | (g1,vs_ts) -> (vs_ts, g1)
  
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
          let uu____2179 = s  in
          match uu____2179 with
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
                      let uu___372_2211 = e  in
                      {
                        FStar_Extraction_ML_Syntax.expr =
                          (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                        FStar_Extraction_ML_Syntax.mlty = ts;
                        FStar_Extraction_ML_Syntax.loc =
                          (uu___372_2211.FStar_Extraction_ML_Syntax.loc)
                      }  in
                    (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
              else
                if n_args < n_vars
                then
                  (let extra_tyargs =
                     let uu____2226 = FStar_Util.first_N n_args vars  in
                     match uu____2226 with
                     | (uu____2240,rest_vars) ->
                         FStar_All.pipe_right rest_vars
                           (FStar_List.map
                              (fun uu____2261  ->
                                 FStar_Extraction_ML_Syntax.MLTY_Erased))
                      in
                   let tyargs1 = FStar_List.append tyargs extra_tyargs  in
                   let ts = instantiate_tyscheme (vars, t) tyargs1  in
                   let tapp =
                     let uu___383_2268 = e  in
                     {
                       FStar_Extraction_ML_Syntax.expr =
                         (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                       FStar_Extraction_ML_Syntax.mlty = ts;
                       FStar_Extraction_ML_Syntax.loc =
                         (uu___383_2268.FStar_Extraction_ML_Syntax.loc)
                     }  in
                   let t1 =
                     FStar_List.fold_left
                       (fun out  ->
                          fun t1  ->
                            FStar_Extraction_ML_Syntax.MLTY_Fun
                              (t1, FStar_Extraction_ML_Syntax.E_PURE, out))
                       ts extra_tyargs
                      in
                   let uu____2276 = fresh_mlidents extra_tyargs g  in
                   match uu____2276 with
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
        let uu____2343 = FStar_Extraction_ML_Util.doms_and_cod t  in
        match uu____2343 with
        | (ts,r) ->
            if ts = []
            then e
            else
              (let uu____2361 = fresh_mlidents ts g  in
               match uu____2361 with
               | (vs_ts,g1) ->
                   let vs_es =
                     FStar_List.map
                       (fun uu____2400  ->
                          match uu____2400 with
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
      let uu____2431 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2431 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____2451 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____2451 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2455 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let uu____2461 = fresh_mlidents ts g  in
             match uu____2461 with
             | (vs_ts,g1) ->
                 let uu____2489 =
                   let uu____2490 =
                     let uu____2502 = body r  in (vs_ts, uu____2502)  in
                   FStar_Extraction_ML_Syntax.MLE_Fun uu____2490  in
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
                   uu____2489)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g  ->
    fun expect  ->
      fun e  ->
        let uu____2526 =
          (FStar_Options.ml_no_eta_expand_coertions ()) ||
            (let uu____2529 = FStar_Options.codegen ()  in
             uu____2529 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
           in
        if uu____2526 then e else eta_expand g expect e
  
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
            | uu____2607 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____2662 =
              match uu____2662 with
              | (pat,w,b) ->
                  let uu____2686 = aux b ty1 expect1  in (pat, w, uu____2686)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____2693,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____2696,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____2728 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____2744 = type_leq g s0 t0  in
                if uu____2744
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____2750 =
                       let uu____2751 =
                         let uu____2752 =
                           let uu____2759 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____2759, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____2752  in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____2751  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____2750;
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
               (lbs,body),uu____2778,uu____2779) ->
                let uu____2792 =
                  let uu____2793 =
                    let uu____2804 = aux body ty1 expect1  in
                    (lbs, uu____2804)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____2793  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2792
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____2813,uu____2814) ->
                let uu____2835 =
                  let uu____2836 =
                    let uu____2851 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2851)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____2836  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2835
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____2891,uu____2892) ->
                let uu____2897 =
                  let uu____2898 =
                    let uu____2907 = aux b1 ty1 expect1  in
                    let uu____2908 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____2907, uu____2908)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____2898  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2897
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____2916,uu____2917)
                ->
                let uu____2920 = FStar_Util.prefix es  in
                (match uu____2920 with
                 | (prefix,last) ->
                     let uu____2933 =
                       let uu____2934 =
                         let uu____2937 =
                           let uu____2940 = aux last ty1 expect1  in
                           [uu____2940]  in
                         FStar_List.append prefix uu____2937  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____2934  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____2933)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____2943,uu____2944) ->
                let uu____2965 =
                  let uu____2966 =
                    let uu____2981 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2981)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____2966  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2965
            | uu____3018 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'uuuuuu3038 .
    'uuuuuu3038 ->
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
            let uu____3065 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____3065 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____3078 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____3086 ->
                     let uu____3087 =
                       let uu____3089 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____3090 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____3089 uu____3090  in
                     if uu____3087
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3096  ->
                             let uu____3097 =
                               let uu____3099 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3099 e
                                in
                             let uu____3100 =
                               let uu____3102 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3102 ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____3097 uu____3100);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3111  ->
                             let uu____3112 =
                               let uu____3114 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3114 e
                                in
                             let uu____3115 =
                               let uu____3117 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3117 ty1
                                in
                             let uu____3118 =
                               let uu____3120 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3120 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____3112 uu____3115 uu____3118);
                        (let uu____3122 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand g expect uu____3122)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____3134 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____3134 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____3136 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
  fun uu____3150  ->
    let uu____3151 = FStar_Options.use_nbe_for_extraction ()  in
    if uu____3151
    then extraction_norm_steps_nbe
    else extraction_norm_steps_core
  
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____3172 -> c
    | FStar_Syntax_Syntax.GTotal uu____3181 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____3217  ->
               match uu____3217 with
               | (uu____3232,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___550_3245 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___550_3245.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___550_3245.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___550_3245.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___550_3245.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___553_3249 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___553_3249.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___553_3249.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let maybe_reify_comp :
  'uuuuuu3261 .
    'uuuuuu3261 ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun g  ->
    fun env  ->
      fun c  ->
        let c1 = comp_no_args c  in
        let uu____3280 =
          let uu____3282 =
            let uu____3283 =
              FStar_All.pipe_right c1 FStar_Syntax_Util.comp_effect_name  in
            FStar_All.pipe_right uu____3283
              (FStar_TypeChecker_Env.norm_eff_name env)
             in
          FStar_All.pipe_right uu____3282
            (FStar_TypeChecker_Env.is_reifiable_effect env)
           in
        if uu____3280
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
      let arg_as_mlty g1 uu____3336 =
        match uu____3336 with
        | (a,uu____3344) ->
            let uu____3349 = is_type g1 a  in
            if uu____3349
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_Syntax.MLTY_Erased
         in
      let fv_app_as_mlty g1 fv args =
        let uu____3370 =
          let uu____3372 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____3372  in
        if uu____3370
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____3377 =
             let uu____3384 =
               let uu____3393 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
               FStar_TypeChecker_Env.lookup_lid uu____3393
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____3384 with
             | ((uu____3400,fvty),uu____3402) ->
                 let fvty1 =
                   let uu____3408 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1
                      in
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant] uu____3408 fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____3377 with
           | (formals,uu____3410) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3447 = FStar_Util.first_N n_args formals  in
                   match uu____3447 with
                   | (uu____3476,rest) ->
                       let uu____3510 =
                         FStar_List.map
                           (fun uu____3520  ->
                              FStar_Extraction_ML_Syntax.MLTY_Erased) rest
                          in
                       FStar_List.append mlargs uu____3510
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
        | FStar_Syntax_Syntax.Tm_type uu____3544 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3545 ->
            let uu____3546 =
              let uu____3548 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3548
               in
            failwith uu____3546
        | FStar_Syntax_Syntax.Tm_delayed uu____3551 ->
            let uu____3566 =
              let uu____3568 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3568
               in
            failwith uu____3566
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3571 =
              let uu____3573 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3573
               in
            failwith uu____3571
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3577 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____3577
        | FStar_Syntax_Syntax.Tm_constant uu____3578 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_quoted uu____3579 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_uvar uu____3586 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____3600) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3605;
               FStar_Syntax_Syntax.index = uu____3606;
               FStar_Syntax_Syntax.sort = t2;_},uu____3608)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3617) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3623,uu____3624) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____3697 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____3697 with
             | (bs1,c1) ->
                 let uu____3704 = binders_as_ml_binders env bs1  in
                 (match uu____3704 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let uu____3733 =
                          let uu____3734 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv env1  in
                          maybe_reify_comp env1 uu____3734 c1  in
                        translate_term_to_mlty env1 uu____3733  in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____3736 =
                        FStar_List.fold_right
                          (fun uu____3756  ->
                             fun uu____3757  ->
                               match (uu____3756, uu____3757) with
                               | ((uu____3780,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____3736 with | (uu____3795,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let res =
              let uu____3824 =
                let uu____3825 = FStar_Syntax_Util.un_uinst head  in
                uu____3825.FStar_Syntax_Syntax.n  in
              match uu____3824 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head1,args') ->
                  let uu____3856 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head1, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____3856
              | uu____3877 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____3880) ->
            let uu____3905 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____3905 with
             | (bs1,ty1) ->
                 let uu____3912 = binders_as_ml_binders env bs1  in
                 (match uu____3912 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____3940 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_match uu____3954 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____3986 ->
            let uu____3993 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____3993 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____3999 -> false  in
      let uu____4001 =
        let uu____4003 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Util.must_erase_for_extraction uu____4003 t0  in
      if uu____4001
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____4008 = is_top_ty mlt  in
         if uu____4008 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____4026 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____4083  ->
                fun b  ->
                  match uu____4083 with
                  | (ml_bs,env) ->
                      let uu____4129 = is_type_binder g b  in
                      if uu____4129
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1 true  in
                        let ml_b =
                          let uu____4152 =
                            FStar_Extraction_ML_UEnv.lookup_ty env1 b1  in
                          uu____4152.FStar_Extraction_ML_UEnv.ty_b_name  in
                        let ml_b1 =
                          (ml_b, FStar_Extraction_ML_Syntax.ml_unit_ty)  in
                        ((ml_b1 :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____4178 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false
                            in
                         match uu____4178 with
                         | (env1,b2,uu____4202) ->
                             let ml_b = (b2, t)  in ((ml_b :: ml_bs), env1)))
             ([], g))
         in
      match uu____4026 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        let uu____4287 = extraction_norm_steps ()  in
        let uu____4288 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Normalize.normalize uu____4287 uu____4288 t0  in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____4307) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4310,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4314 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____4348 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4349 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4350 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4359 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
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
            (fun uu____4435  ->
               fun x  -> match uu____4435 with | (p,s) -> (s, x)) fns1 xs
  
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
            let uu____4487 = FStar_Extraction_ML_Util.is_xtuple d  in
            (match uu____4487 with
             | FStar_Pervasives_Native.Some n ->
                 FStar_Extraction_ML_Syntax.MLP_Tuple pats
             | uu____4494 ->
                 (match q with
                  | FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                      let path =
                        let uu____4508 = FStar_Ident.ns_of_lid ty  in
                        FStar_List.map FStar_Ident.text_of_id uu____4508  in
                      let fs = record_fields g ty fns pats  in
                      FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                  | uu____4530 -> p))
        | uu____4533 -> p
  
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
                       (fun uu____4635  ->
                          let uu____4636 =
                            let uu____4638 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4638 t'
                             in
                          let uu____4639 =
                            let uu____4641 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4641 t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4636 uu____4639)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____4676 = FStar_Options.codegen ()  in
                uu____4676 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4681 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4694 =
                        let uu____4695 =
                          let uu____4696 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4696  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4695
                         in
                      (uu____4694, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        let uu____4718 =
                          let uu____4719 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                          uu____4719.FStar_TypeChecker_Env.dsenv  in
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          uu____4718 c sw FStar_Range.dummyRange
                         in
                      let uu____4720 = term_as_mlexpr g source_term  in
                      (match uu____4720 with
                       | (mlterm,uu____4732,mlty) -> (mlterm, mlty))
                   in
                (match uu____4681 with
                 | (mlc,ml_ty) ->
                     let uu____4751 = FStar_Extraction_ML_UEnv.new_mlident g
                        in
                     (match uu____4751 with
                      | (g1,x) ->
                          let when_clause =
                            let uu____4777 =
                              let uu____4778 =
                                let uu____4785 =
                                  let uu____4788 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         ml_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Var x)
                                     in
                                  [uu____4788; mlc]  in
                                (FStar_Extraction_ML_Util.prims_op_equality,
                                  uu____4785)
                                 in
                              FStar_Extraction_ML_Syntax.MLE_App uu____4778
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_bool_ty)
                              uu____4777
                             in
                          let uu____4791 = ok ml_ty  in
                          (g1,
                            (FStar_Pervasives_Native.Some
                               ((FStar_Extraction_ML_Syntax.MLP_Var x),
                                 [when_clause])), uu____4791)))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  let uu____4812 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_TcTerm.tc_constant uu____4812
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____4814 =
                  let uu____4823 =
                    let uu____4830 =
                      let uu____4831 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4831  in
                    (uu____4830, [])  in
                  FStar_Pervasives_Native.Some uu____4823  in
                let uu____4840 = ok mlty  in (g, uu____4814, uu____4840)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4853 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false imp
                   in
                (match uu____4853 with
                 | (g1,x1,uu____4880) ->
                     let uu____4883 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4883))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4921 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false imp
                   in
                (match uu____4921 with
                 | (g1,x1,uu____4948) ->
                     let uu____4951 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4951))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4987 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____5030 =
                  let uu____5039 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____5039 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____5048;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n;
                          FStar_Extraction_ML_Syntax.mlty = uu____5050;
                          FStar_Extraction_ML_Syntax.loc = uu____5051;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;_} ->
                      (n, ttys)
                  | uu____5058 -> failwith "Expected a constructor"  in
                (match uu____5030 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____5095 = FStar_Util.first_N nTyVars pats  in
                     (match uu____5095 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___852_5199  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____5230  ->
                                               match uu____5230 with
                                               | (p1,uu____5237) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5240,t) ->
                                                        term_as_mlty g t
                                                    | uu____5246 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5250 
                                                              ->
                                                              let uu____5251
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5251);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____5255 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____5255)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____5284 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____5321  ->
                                   match uu____5321 with
                                   | (p1,imp1) ->
                                       let uu____5343 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____5343 with
                                        | (g2,p2,uu____5374) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____5284 with
                           | (g1,tyMLPats) ->
                               let uu____5438 =
                                 FStar_Util.fold_map
                                   (fun uu____5503  ->
                                      fun uu____5504  ->
                                        match (uu____5503, uu____5504) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____5602 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd))
                                              | uu____5662 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____5602 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____5733 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____5733 with
                                                  | (g3,p2,uu____5776) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____5438 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____5897 =
                                      let uu____5908 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5959  ->
                                                match uu___0_5959 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____6001 -> []))
                                         in
                                      FStar_All.pipe_right uu____5908
                                        FStar_List.split
                                       in
                                    (match uu____5897 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____6077 -> false  in
                                         let uu____6087 =
                                           let uu____6096 =
                                             let uu____6103 =
                                               resugar_pat g2
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____6106 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____6103, uu____6106)  in
                                           FStar_Pervasives_Native.Some
                                             uu____6096
                                            in
                                         (g2, uu____6087, pat_ty_compat))))))
  
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
            let uu____6238 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____6238 with
            | (g2,FStar_Pervasives_Native.Some (x,v),b) -> (g2, (x, v), b)
            | uu____6301 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd::tl ->
                let uu____6349 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl
                   in
                FStar_Pervasives_Native.Some uu____6349
             in
          let uu____6350 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____6350 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____6515,t1) ->
                let uu____6517 = FStar_Extraction_ML_UEnv.new_mlident g1  in
                (match uu____6517 with
                 | (g2,x) ->
                     let uu____6542 =
                       let uu____6554 =
                         let uu____6564 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty t0)
                             (FStar_Extraction_ML_Syntax.MLE_Var x)
                            in
                         ((x, t0), uu____6564)  in
                       uu____6554 :: more_args  in
                     eta_args g2 uu____6542 t1)
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6580,uu____6581)
                -> ((FStar_List.rev more_args), t)
            | uu____6606 ->
                let uu____6607 =
                  let uu____6609 =
                    let uu____6611 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu____6611
                      mlAppExpr
                     in
                  let uu____6612 =
                    let uu____6614 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlty uu____6614 t  in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6609 uu____6612
                   in
                failwith uu____6607
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____6648,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  let uu____6666 = FStar_Ident.ns_of_lid tyname  in
                  FStar_List.map FStar_Ident.text_of_id uu____6666  in
                let fields1 = record_fields g tyname fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6688 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____6710 = eta_args g [] residualType  in
            match uu____6710 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____6768 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____6768
                 | uu____6769 ->
                     let uu____6781 = FStar_List.unzip eargs  in
                     (match uu____6781 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head,args)
                               ->
                               let body =
                                 let uu____6827 =
                                   let uu____6828 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6828
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6827
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6838 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6842,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6846;
                FStar_Extraction_ML_Syntax.loc = uu____6847;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let fn =
                let uu____6859 =
                  let uu____6864 =
                    let uu____6865 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6865
                      constrname
                     in
                  (uu____6864, f)  in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6859
                 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____6868 ->
                    let uu____6871 =
                      let uu____6878 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6878, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6871
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
                     FStar_Extraction_ML_Syntax.mlty = uu____6882;
                     FStar_Extraction_ML_Syntax.loc = uu____6883;_},uu____6884);
                FStar_Extraction_ML_Syntax.mlty = uu____6885;
                FStar_Extraction_ML_Syntax.loc = uu____6886;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let fn =
                let uu____6902 =
                  let uu____6907 =
                    let uu____6908 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6908
                      constrname
                     in
                  (uu____6907, f)  in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6902
                 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____6911 ->
                    let uu____6914 =
                      let uu____6921 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6921, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6914
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6925;
                FStar_Extraction_ML_Syntax.loc = uu____6926;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6934 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6934
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6938;
                FStar_Extraction_ML_Syntax.loc = uu____6939;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6941)) ->
              let uu____6954 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6954
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6958;
                     FStar_Extraction_ML_Syntax.loc = uu____6959;_},uu____6960);
                FStar_Extraction_ML_Syntax.mlty = uu____6961;
                FStar_Extraction_ML_Syntax.loc = uu____6962;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6974 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6974
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6978;
                     FStar_Extraction_ML_Syntax.loc = uu____6979;_},uu____6980);
                FStar_Extraction_ML_Syntax.mlty = uu____6981;
                FStar_Extraction_ML_Syntax.loc = uu____6982;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6984)) ->
              let uu____7001 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7001
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____7007 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7007
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7011)) ->
              let uu____7020 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7020
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7024;
                FStar_Extraction_ML_Syntax.loc = uu____7025;_},uu____7026),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____7033 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7033
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7037;
                FStar_Extraction_ML_Syntax.loc = uu____7038;_},uu____7039),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7040)) ->
              let uu____7053 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7053
          | uu____7056 -> mlAppExpr
  
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
        | uu____7087 -> (ml_e, tag)
  
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
      let maybe_generalize uu____7148 =
        match uu____7148 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____7169;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____7174;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____7255 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____7332 =
              let uu____7334 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Util.must_erase_for_extraction uu____7334
                lbtyp1
               in
            if uu____7332
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____7419 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____7419 (is_type_binder g) ->
                   let uu____7441 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____7441 with
                    | (bs1,c1) ->
                        let uu____7467 =
                          let uu____7480 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____7526 = is_type_binder g x  in
                                 Prims.op_Negation uu____7526) bs1
                             in
                          match uu____7480 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____7653 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____7653)
                           in
                        (match uu____7467 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____7715 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____7715
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____7764 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____7764 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7816 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____7816 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7919  ->
                                                       fun uu____7920  ->
                                                         match (uu____7919,
                                                                 uu____7920)
                                                         with
                                                         | ((x,uu____7946),
                                                            (y,uu____7948))
                                                             ->
                                                             let uu____7969 =
                                                               let uu____7976
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____7976)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7969)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____7993  ->
                                                       match uu____7993 with
                                                       | (a,uu____8001) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a false) g
                                                  targs
                                                 in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty
                                                 in
                                              let polytype =
                                                let uu____8013 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____8033  ->
                                                          match uu____8033
                                                          with
                                                          | (x,uu____8042) ->
                                                              let uu____8047
                                                                =
                                                                FStar_Extraction_ML_UEnv.lookup_ty
                                                                  env x
                                                                 in
                                                              uu____8047.FStar_Extraction_ML_UEnv.ty_b_name))
                                                   in
                                                (uu____8013, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____8059 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____8059)
                                                      ||
                                                      (let uu____8062 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____8062)
                                                | uu____8064 -> false  in
                                              let rest_args1 =
                                                if add_unit
                                                then
                                                  let uu____8076 =
                                                    unit_binder ()  in
                                                  uu____8076 :: rest_args
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____8133 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8152  ->
                                           match uu____8152 with
                                           | (a,uu____8160) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8172 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8192  ->
                                              match uu____8192 with
                                              | (x,uu____8201) ->
                                                  let uu____8206 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8206.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8172, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8246  ->
                                            match uu____8246 with
                                            | (bv,uu____8254) ->
                                                let uu____8259 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8259
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____8289 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8302  ->
                                           match uu____8302 with
                                           | (a,uu____8310) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8322 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8342  ->
                                              match uu____8342 with
                                              | (x,uu____8351) ->
                                                  let uu____8356 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8356.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8322, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8396  ->
                                            match uu____8396 with
                                            | (bv,uu____8404) ->
                                                let uu____8409 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8409
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
                              | FStar_Syntax_Syntax.Tm_name uu____8439 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8452  ->
                                           match uu____8452 with
                                           | (a,uu____8460) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8472 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8492  ->
                                              match uu____8492 with
                                              | (x,uu____8501) ->
                                                  let uu____8506 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8506.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8472, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8546  ->
                                            match uu____8546 with
                                            | (bv,uu____8554) ->
                                                let uu____8559 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8559
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
                              | uu____8589 -> err_value_restriction lbdef1)))
               | uu____8609 -> no_gen ())
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
           fun uu____8760  ->
             match uu____8760 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____8821 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit
                    in
                 (match uu____8821 with
                  | (env1,uu____8838,exp_binding) ->
                      let uu____8842 =
                        let uu____8847 = FStar_Util.right lbname  in
                        (uu____8847, exp_binding)  in
                      (env1, uu____8842))) g lbs1
  
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
            (fun uu____8914  ->
               let uu____8915 = FStar_Syntax_Print.term_to_string e  in
               let uu____8917 =
                 let uu____8919 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g  in
                 FStar_Extraction_ML_Code.string_of_mlty uu____8919 ty  in
               let uu____8920 = FStar_Extraction_ML_Util.eff_to_string f  in
               FStar_Util.print3 "Checking %s at type %s and eff %s\n"
                 uu____8915 uu____8917 uu____8920);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____8927) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8928 ->
               let uu____8933 = term_as_mlexpr g e  in
               (match uu____8933 with
                | (ml_e,tag,t) ->
                    let uu____8947 = FStar_Extraction_ML_Util.eff_leq tag f
                       in
                    if uu____8947
                    then
                      let uu____8954 =
                        maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t ty
                         in
                      (uu____8954, ty)
                    else
                      (match (tag, f, ty) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST
                          ,FStar_Extraction_ML_Syntax.E_PURE
                          ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                           let uu____8961 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t
                               ty
                              in
                           (uu____8961, ty)
                       | uu____8962 ->
                           (err_unexpected_eff g e ty f tag;
                            (let uu____8970 =
                               maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e
                                 t ty
                                in
                             (uu____8970, ty))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____8979 = term_as_mlexpr' g e  in
      match uu____8979 with
      | (e1,f,t) ->
          let uu____8995 = maybe_promote_effect e1 f t  in
          (match uu____8995 with | (e2,f1) -> (e2, f1, t))

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
           let uu____9021 =
             let uu____9023 =
               FStar_Range.string_of_range top1.FStar_Syntax_Syntax.pos  in
             let uu____9025 = FStar_Syntax_Print.tag_of_term top1  in
             let uu____9027 = FStar_Syntax_Print.term_to_string top1  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____9023 uu____9025 uu____9027
              in
           FStar_Util.print_string uu____9021);
      (let is_match t =
         let uu____9037 =
           let uu____9038 =
             let uu____9041 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9041 FStar_Syntax_Util.unascribe  in
           uu____9038.FStar_Syntax_Syntax.n  in
         match uu____9037 with
         | FStar_Syntax_Syntax.Tm_match uu____9045 -> true
         | uu____9069 -> false  in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____9088  ->
              match uu____9088 with
              | (t,uu____9097) ->
                  let uu____9102 =
                    let uu____9103 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
                    uu____9103.FStar_Syntax_Syntax.n  in
                  (match uu____9102 with
                   | FStar_Syntax_Syntax.Tm_name uu____9109 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____9111 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____9113 -> true
                   | uu____9115 -> false))
          in
       let apply_to_match_branches head args =
         let uu____9154 =
           let uu____9155 =
             let uu____9158 =
               FStar_All.pipe_right head FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9158 FStar_Syntax_Util.unascribe  in
           uu____9155.FStar_Syntax_Syntax.n  in
         match uu____9154 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee,branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____9282  ->
                       match uu____9282 with
                       | (pat,when_opt,body) ->
                           (pat, when_opt,
                             (let uu___1319_9339 = body  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1319_9339.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1319_9339.FStar_Syntax_Syntax.vars)
                              }))))
                in
             let uu___1322_9354 = head  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1322_9354.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1322_9354.FStar_Syntax_Syntax.vars)
             }
         | uu____9375 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match"
          in
       let t = FStar_Syntax_Subst.compress top1  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9386 =
             let uu____9388 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9388
              in
           failwith uu____9386
       | FStar_Syntax_Syntax.Tm_delayed uu____9397 ->
           let uu____9412 =
             let uu____9414 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9414
              in
           failwith uu____9412
       | FStar_Syntax_Syntax.Tm_uvar uu____9423 ->
           let uu____9436 =
             let uu____9438 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9438
              in
           failwith uu____9436
       | FStar_Syntax_Syntax.Tm_bvar uu____9447 ->
           let uu____9448 =
             let uu____9450 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9450
              in
           failwith uu____9448
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9460 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____9460
       | FStar_Syntax_Syntax.Tm_type uu____9461 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9462 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9469 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____9485;_})
           ->
           let uu____9498 =
             let uu____9499 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9499  in
           (match uu____9498 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9506;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9508;_} ->
                let uu____9510 =
                  let uu____9511 =
                    let uu____9512 =
                      let uu____9519 =
                        let uu____9522 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____9522]  in
                      (fw, uu____9519)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9512  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9511
                   in
                (uu____9510, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9540 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____9540 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9548 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____9548 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____9559 =
                         let uu____9566 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____9566
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____9559 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____9574 =
                         let uu____9585 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____9585]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9574
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9612 =
                    let uu____9619 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____9619 tv  in
                  uu____9612 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____9627 =
                    let uu____9638 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____9638]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9627
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____9665)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9698 =
                  let uu____9705 =
                    let uu____9714 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.effect_decl_opt uu____9714 m  in
                  FStar_Util.must uu____9705  in
                (match uu____9698 with
                 | (ed,qualifiers) ->
                     let uu____9733 =
                       let uu____9735 =
                         let uu____9737 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                         FStar_TypeChecker_Env.is_reifiable_effect uu____9737
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____9735  in
                     if uu____9733
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9754 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9756) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9762) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9768 =
             let uu____9775 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_TcTerm.type_of_tot_term uu____9775 t  in
           (match uu____9768 with
            | (uu____9782,ty,uu____9784) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____9786 =
                  let uu____9787 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9787  in
                (uu____9786, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9788 ->
           let uu____9789 = is_type g t  in
           if uu____9789
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9800 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____9800 with
              | (FStar_Util.Inl uu____9813,uu____9814) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9819;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____9838 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____9838, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9839 -> instantiate_maybe_partial g x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9841 = is_type g t  in
           if uu____9841
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9852 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____9852 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9861;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9870  ->
                        let uu____9871 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____9873 =
                          let uu____9875 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            uu____9875 x
                           in
                        let uu____9876 =
                          let uu____9878 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlty uu____9878
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9871 uu____9873 uu____9876);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____9890 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____9890, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9891 -> instantiate_maybe_partial g x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____9919 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____9919 with
            | (bs1,body1) ->
                let uu____9932 = binders_as_ml_binders g bs1  in
                (match uu____9932 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9968 =
                             let uu____9970 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Env.is_reifiable_rc uu____9970
                               rc
                              in
                           if uu____9968
                           then
                             let uu____9972 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Util.reify_body uu____9972
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Unascribe] body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9978  ->
                                 let uu____9979 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9979);
                            body1)
                        in
                     let uu____9982 = term_as_mlexpr env body2  in
                     (match uu____9982 with
                      | (ml_body,f,t1) ->
                          let uu____9998 =
                            FStar_List.fold_right
                              (fun uu____10018  ->
                                 fun uu____10019  ->
                                   match (uu____10018, uu____10019) with
                                   | ((uu____10042,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____9998 with
                           | (f1,tfun) ->
                               let uu____10065 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____10065, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____10073;
              FStar_Syntax_Syntax.vars = uu____10074;_},(a1,uu____10076)::[])
           ->
           let ty =
             let uu____10116 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____10116  in
           let uu____10117 =
             let uu____10118 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____10118
              in
           (uu____10117, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____10119;
              FStar_Syntax_Syntax.vars = uu____10120;_},(t1,uu____10122)::
            (r,uu____10124)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____10179);
              FStar_Syntax_Syntax.pos = uu____10180;
              FStar_Syntax_Syntax.vars = uu____10181;_},uu____10182)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head,args) when
           (is_match head) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____10241 =
             FStar_All.pipe_right args (apply_to_match_branches head)  in
           FStar_All.pipe_right uu____10241 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_10295  ->
                        match uu___1_10295 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____10298 -> false)))
              in
           let uu____10300 =
             let uu____10301 =
               let uu____10304 =
                 FStar_All.pipe_right head FStar_Syntax_Subst.compress  in
               FStar_All.pipe_right uu____10304 FStar_Syntax_Util.unascribe
                in
             uu____10301.FStar_Syntax_Syntax.n  in
           (match uu____10300 with
            | FStar_Syntax_Syntax.Tm_abs (bs,uu____10314,_rc) ->
                let uu____10340 =
                  let uu____10341 =
                    let uu____10346 =
                      FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses]
                      uu____10346
                     in
                  FStar_All.pipe_right t uu____10341  in
                FStar_All.pipe_right uu____10340 (term_as_mlexpr g)
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                let e =
                  let uu____10354 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  let uu____10355 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg uu____10354
                    [FStar_TypeChecker_Env.Inlining;
                    FStar_TypeChecker_Env.Unascribe] head uu____10355
                   in
                let tm =
                  let uu____10367 =
                    let uu____10372 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____10373 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____10372 uu____10373  in
                  uu____10367 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____10382 ->
                let rec extract_app is_data uu____10431 uu____10432 restArgs
                  =
                  match (uu____10431, uu____10432) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____10513 =
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
                         (fun uu____10540  ->
                            let uu____10541 =
                              let uu____10543 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              let uu____10544 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____10543 uu____10544
                               in
                            let uu____10545 =
                              let uu____10547 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlty
                                uu____10547 t1
                               in
                            let uu____10548 =
                              match restArgs with
                              | [] -> "none"
                              | (hd,uu____10559)::uu____10560 ->
                                  FStar_Syntax_Print.term_to_string hd
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10541 uu____10545 uu____10548);
                       (match (restArgs, t1) with
                        | ([],uu____10594) ->
                            let app =
                              let uu____10610 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10610
                               in
                            (app, f, t1)
                        | ((arg,uu____10612)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10643 =
                              let uu____10648 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____10648, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10643 rest
                        | ((e0,uu____10660)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____10693 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head)
                                 in
                              if uu____10693
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____10698 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____10698 with
                             | (e01,tInferred) ->
                                 let uu____10711 =
                                   let uu____10716 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____10716, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10711 rest)
                        | uu____10727 ->
                            let uu____10740 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____10740 with
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
                                  | uu____10812 ->
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
                let extract_app_maybe_projector is_data mlhead uu____10883
                  args1 =
                  match uu____10883 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10913)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10997))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____10999,f',t3)) ->
                                 let uu____11037 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____11037 t3
                             | uu____11038 -> (args2, f1, t2)  in
                           let uu____11063 = remove_implicits args1 f t1  in
                           (match uu____11063 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____11119 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____11143 =
                  let head1 = FStar_Syntax_Util.un_uinst head  in
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____11151 ->
                      let uu____11152 =
                        let uu____11167 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1  in
                        match uu____11167 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11199  ->
                                  let uu____11200 =
                                    FStar_Syntax_Print.term_to_string head1
                                     in
                                  let uu____11202 =
                                    let uu____11204 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11204
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11205 =
                                    let uu____11207 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11207
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  FStar_Util.print3
                                    "@@@looked up %s: got %s at %s\n"
                                    uu____11200 uu____11202 uu____11205);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu____11223 -> failwith "FIXME Ty"  in
                      (match uu____11152 with
                       | ((head_ml,(vars,t1)),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11275)::uu____11276 -> is_type g a
                             | uu____11303 -> false  in
                           let uu____11315 =
                             let n = FStar_List.length vars  in
                             let uu____11332 =
                               if (FStar_List.length args) <= n
                               then
                                 let uu____11370 =
                                   FStar_List.map
                                     (fun uu____11382  ->
                                        match uu____11382 with
                                        | (x,uu____11390) -> term_as_mlty g x)
                                     args
                                    in
                                 (uu____11370, [])
                               else
                                 (let uu____11413 = FStar_Util.first_N n args
                                     in
                                  match uu____11413 with
                                  | (prefix,rest) ->
                                      let uu____11502 =
                                        FStar_List.map
                                          (fun uu____11514  ->
                                             match uu____11514 with
                                             | (x,uu____11522) ->
                                                 term_as_mlty g x) prefix
                                         in
                                      (uu____11502, rest))
                                in
                             match uu____11332 with
                             | (provided_type_args,rest) ->
                                 let uu____11573 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu____11582 ->
                                       let uu____11583 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____11583 with
                                        | (head2,uu____11595,t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu____11597 ->
                                       let uu____11599 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____11599 with
                                        | (head2,uu____11611,t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head2,{
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  FStar_Extraction_ML_Syntax.MLE_Const
                                                  (FStar_Extraction_ML_Syntax.MLC_Unit
                                                  );
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = uu____11614;
                                                FStar_Extraction_ML_Syntax.loc
                                                  = uu____11615;_}::[])
                                       ->
                                       let uu____11618 =
                                         instantiate_maybe_partial g head2
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____11618 with
                                        | (head3,uu____11630,t2) ->
                                            let uu____11632 =
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head3,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                               in
                                            (uu____11632, t2))
                                   | uu____11635 ->
                                       failwith
                                         "Impossible: Unexpected head term"
                                    in
                                 (match uu____11573 with
                                  | (head2,t2) -> (head2, t2, rest))
                              in
                           (match uu____11315 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11702 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____11702,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11703 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11712 ->
                      let uu____11713 =
                        let uu____11728 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1  in
                        match uu____11728 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11760  ->
                                  let uu____11761 =
                                    FStar_Syntax_Print.term_to_string head1
                                     in
                                  let uu____11763 =
                                    let uu____11765 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11765
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11766 =
                                    let uu____11768 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11768
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  FStar_Util.print3
                                    "@@@looked up %s: got %s at %s\n"
                                    uu____11761 uu____11763 uu____11766);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu____11784 -> failwith "FIXME Ty"  in
                      (match uu____11713 with
                       | ((head_ml,(vars,t1)),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11836)::uu____11837 -> is_type g a
                             | uu____11864 -> false  in
                           let uu____11876 =
                             let n = FStar_List.length vars  in
                             let uu____11893 =
                               if (FStar_List.length args) <= n
                               then
                                 let uu____11931 =
                                   FStar_List.map
                                     (fun uu____11943  ->
                                        match uu____11943 with
                                        | (x,uu____11951) -> term_as_mlty g x)
                                     args
                                    in
                                 (uu____11931, [])
                               else
                                 (let uu____11974 = FStar_Util.first_N n args
                                     in
                                  match uu____11974 with
                                  | (prefix,rest) ->
                                      let uu____12063 =
                                        FStar_List.map
                                          (fun uu____12075  ->
                                             match uu____12075 with
                                             | (x,uu____12083) ->
                                                 term_as_mlty g x) prefix
                                         in
                                      (uu____12063, rest))
                                in
                             match uu____11893 with
                             | (provided_type_args,rest) ->
                                 let uu____12134 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu____12143 ->
                                       let uu____12144 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____12144 with
                                        | (head2,uu____12156,t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu____12158 ->
                                       let uu____12160 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____12160 with
                                        | (head2,uu____12172,t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head2,{
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  FStar_Extraction_ML_Syntax.MLE_Const
                                                  (FStar_Extraction_ML_Syntax.MLC_Unit
                                                  );
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = uu____12175;
                                                FStar_Extraction_ML_Syntax.loc
                                                  = uu____12176;_}::[])
                                       ->
                                       let uu____12179 =
                                         instantiate_maybe_partial g head2
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____12179 with
                                        | (head3,uu____12191,t2) ->
                                            let uu____12193 =
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head3,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                               in
                                            (uu____12193, t2))
                                   | uu____12196 ->
                                       failwith
                                         "Impossible: Unexpected head term"
                                    in
                                 (match uu____12134 with
                                  | (head2,t2) -> (head2, t2, rest))
                              in
                           (match uu____11876 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12263 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____12263,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12264 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12273 ->
                      let uu____12274 = term_as_mlexpr g head1  in
                      (match uu____12274 with
                       | (head2,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head2 (f, t1) args)
                   in
                let uu____12290 = is_type g t  in
                if uu____12290
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12301 =
                     let uu____12302 = FStar_Syntax_Util.un_uinst head  in
                     uu____12302.FStar_Syntax_Syntax.n  in
                   match uu____12301 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12312 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____12312 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12321 -> extract_app_with_instantiations ())
                   | uu____12324 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____12327),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12392 =
                   let uu____12393 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                      in
                   maybe_reify_comp g uu____12393 c  in
                 term_as_mlty g uu____12392
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____12397 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____12397 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e') when
           (let uu____12429 = FStar_Syntax_Syntax.is_top_level [lb]  in
            Prims.op_Negation uu____12429) &&
             (let uu____12432 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs
                 in
              FStar_Util.is_some uu____12432)
           ->
           let b =
             let uu____12442 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                in
             (uu____12442, FStar_Pervasives_Native.None)  in
           let uu____12445 = FStar_Syntax_Subst.open_term_1 b e'  in
           (match uu____12445 with
            | ((x,uu____12457),body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str,uu____12472)::[]) ->
                      let uu____12497 =
                        let uu____12498 = FStar_Syntax_Subst.compress str  in
                        uu____12498.FStar_Syntax_Syntax.n  in
                      (match uu____12497 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s,uu____12504)) ->
                           let id =
                             let uu____12508 =
                               let uu____12514 =
                                 FStar_Syntax_Syntax.range_of_bv x  in
                               (s, uu____12514)  in
                             FStar_Ident.mk_ident uu____12508  in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             }  in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv  in
                           FStar_Pervasives_Native.Some bv1
                       | uu____12519 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____12520 ->
                      (FStar_Errors.log_issue top1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `rename_let`");
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                   in
                let remove_attr attrs =
                  let uu____12540 =
                    FStar_List.partition
                      (fun attr  ->
                         let uu____12552 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr]
                            in
                         FStar_Util.is_some uu____12552)
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match uu____12540 with
                  | (uu____12557,other_attrs) -> other_attrs  in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None  ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs  in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1774_12585 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1774_12585.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1774_12585.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1774_12585.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1774_12585.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1774_12585.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1774_12585.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs  in
                      let rename =
                        let uu____12593 =
                          let uu____12594 =
                            let uu____12601 =
                              FStar_Syntax_Syntax.bv_to_name y  in
                            (x, uu____12601)  in
                          FStar_Syntax_Syntax.NT uu____12594  in
                        [uu____12593]  in
                      let body1 =
                        let uu____12607 =
                          FStar_Syntax_Subst.subst rename body  in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____12607
                         in
                      let lb1 =
                        let uu___1781_12623 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1781_12623.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1781_12623.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1781_12623.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1781_12623.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1781_12623.FStar_Syntax_Syntax.lbpos)
                        }  in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1)
                   in
                let top2 =
                  let uu___1785_12640 = top1  in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1785_12640.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1785_12640.FStar_Syntax_Syntax.vars)
                  }  in
                term_as_mlexpr' g top2)
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____12663 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12679 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____12679
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____12694 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____12694  in
                   let lb1 =
                     let uu___1799_12696 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1799_12696.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1799_12696.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1799_12696.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1799_12696.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1799_12696.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1799_12696.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____12663 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____12721 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      let uu____12722 =
                        let uu____12723 =
                          let uu____12724 =
                            let uu____12728 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Pervasives_Native.fst uu____12728  in
                          let uu____12741 =
                            let uu____12745 =
                              let uu____12747 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Pervasives_Native.snd uu____12747  in
                            [uu____12745]  in
                          FStar_List.append uu____12724 uu____12741  in
                        FStar_Ident.lid_of_path uu____12723
                          FStar_Range.dummyRange
                         in
                      FStar_TypeChecker_Env.set_current_module uu____12721
                        uu____12722
                       in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let lbdef =
                              let uu____12774 = FStar_Options.ml_ish ()  in
                              if uu____12774
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____12786 =
                                   let uu____12787 =
                                     let uu____12788 =
                                       extraction_norm_steps ()  in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____12788
                                      in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____12787 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____12791 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____12791
                                 then
                                   ((let uu____12801 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____12801);
                                    (let a =
                                       let uu____12807 =
                                         let uu____12809 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____12809
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____12807 norm_call
                                        in
                                     a))
                                 else norm_call ())
                               in
                            let uu___1816_12816 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1816_12816.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1816_12816.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1816_12816.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1816_12816.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1816_12816.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1816_12816.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____12869 =
                  match uu____12869 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____13025  ->
                               match uu____13025 with
                               | (a,uu____13033) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     false) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____13040 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____13040 with
                       | (e1,ty) ->
                           let uu____13051 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____13051 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____13063 -> []  in
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
                let uu____13094 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____13191  ->
                         match uu____13191 with
                         | (env,lbs4) ->
                             let uu____13325 = lb  in
                             (match uu____13325 with
                              | (lbname,uu____13376,(t1,(uu____13378,polytype)),add_unit,uu____13381)
                                  ->
                                  let uu____13396 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit
                                     in
                                  (match uu____13396 with
                                   | (env1,nm,uu____13436) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____13094 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____13715 = term_as_mlexpr env_body e'1  in
                     (match uu____13715 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____13732 =
                              let uu____13735 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____13735  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13732
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____13748 =
                            let uu____13749 =
                              let uu____13750 =
                                let uu____13751 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____13751)  in
                              mk_MLE_Let top_level uu____13750 e'2  in
                            let uu____13760 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13749 uu____13760
                             in
                          (uu____13748, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____13799 = term_as_mlexpr g scrutinee  in
           (match uu____13799 with
            | (e,f_e,t_e) ->
                let uu____13815 = check_pats_for_ite pats  in
                (match uu____13815 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____13880 = term_as_mlexpr g then_e1  in
                            (match uu____13880 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____13896 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____13896 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____13912 =
                                        let uu____13923 =
                                          type_leq g t_then t_else  in
                                        if uu____13923
                                        then (t_else, no_lift)
                                        else
                                          (let uu____13944 =
                                             type_leq g t_else t_then  in
                                           if uu____13944
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____13912 with
                                       | (t_branch,maybe_lift) ->
                                           let uu____13991 =
                                             let uu____13992 =
                                               let uu____13993 =
                                                 let uu____14002 =
                                                   maybe_lift then_mle t_then
                                                    in
                                                 let uu____14003 =
                                                   let uu____14006 =
                                                     maybe_lift else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____14006
                                                    in
                                                 (e, uu____14002,
                                                   uu____14003)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____13993
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____13992
                                              in
                                           let uu____14009 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____13991, uu____14009,
                                             t_branch))))
                        | uu____14010 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____14028 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____14127 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____14127 with
                                    | (pat,when_opt,branch) ->
                                        let uu____14172 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____14172 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____14234 =
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
                                                   let uu____14257 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____14257 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____14234 with
                                              | (when_opt1,f_when) ->
                                                  let uu____14307 =
                                                    term_as_mlexpr env branch
                                                     in
                                                  (match uu____14307 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____14342 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14419 
                                                                 ->
                                                                 match uu____14419
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
                                                         uu____14342)))))
                               true)
                           in
                        match uu____14028 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14590  ->
                                      let uu____14591 =
                                        let uu____14593 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu____14593 e
                                         in
                                      let uu____14594 =
                                        let uu____14596 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu____14596 t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14591 uu____14594);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14622 =
                                   let uu____14623 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14623
                                    in
                                 (match uu____14622 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14630;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14632;_}
                                      ->
                                      let uu____14634 =
                                        let uu____14635 =
                                          let uu____14636 =
                                            let uu____14643 =
                                              let uu____14646 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____14646]  in
                                            (fw, uu____14643)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14636
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14635
                                         in
                                      (uu____14634,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14650,uu____14651,(uu____14652,f_first,t_first))::rest
                                 ->
                                 let uu____14712 =
                                   FStar_List.fold_left
                                     (fun uu____14754  ->
                                        fun uu____14755  ->
                                          match (uu____14754, uu____14755)
                                          with
                                          | ((topt,f),(uu____14812,uu____14813,
                                                       (uu____14814,f_branch,t_branch)))
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
                                                    let uu____14870 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____14870
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____14877 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____14877
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
                                 (match uu____14712 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____14975  ->
                                                match uu____14975 with
                                                | (p,(wopt,uu____15004),
                                                   (b1,uu____15006,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____15025 -> b1
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
                                      let uu____15030 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____15030, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____15057 =
          let uu____15062 =
            let uu____15071 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_lid uu____15071 discName  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15062  in
        match uu____15057 with
        | (uu____15088,fstar_disc_type) ->
            let uu____15090 =
              let uu____15102 =
                let uu____15103 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____15103.FStar_Syntax_Syntax.n  in
              match uu____15102 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15118) ->
                  let binders1 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_15173  ->
                            match uu___2_15173 with
                            | (uu____15181,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15182)) ->
                                true
                            | uu____15187 -> false))
                     in
                  FStar_List.fold_right
                    (fun uu____15219  ->
                       fun uu____15220  ->
                         match uu____15220 with
                         | (g,vs) ->
                             let uu____15265 =
                               FStar_Extraction_ML_UEnv.new_mlident g  in
                             (match uu____15265 with
                              | (g1,v) ->
                                  (g1,
                                    ((v, FStar_Extraction_ML_Syntax.MLTY_Top)
                                    :: vs)))) binders1 (env, [])
              | uu____15311 -> failwith "Discriminator must be a function"
               in
            (match uu____15090 with
             | (g,wildcards) ->
                 let uu____15340 = FStar_Extraction_ML_UEnv.new_mlident g  in
                 (match uu____15340 with
                  | (g1,mlid) ->
                      let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let discrBody =
                        let uu____15353 =
                          let uu____15354 =
                            let uu____15366 =
                              let uu____15367 =
                                let uu____15368 =
                                  let uu____15383 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         targ)
                                      (FStar_Extraction_ML_Syntax.MLE_Name
                                         ([], mlid))
                                     in
                                  let uu____15389 =
                                    let uu____15400 =
                                      let uu____15409 =
                                        let uu____15410 =
                                          let uu____15417 =
                                            FStar_Extraction_ML_UEnv.mlpath_of_lident
                                              g1 constrName
                                             in
                                          (uu____15417,
                                            [FStar_Extraction_ML_Syntax.MLP_Wild])
                                           in
                                        FStar_Extraction_ML_Syntax.MLP_CTor
                                          uu____15410
                                         in
                                      let uu____15420 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_bool_ty)
                                          (FStar_Extraction_ML_Syntax.MLE_Const
                                             (FStar_Extraction_ML_Syntax.MLC_Bool
                                                true))
                                         in
                                      (uu____15409,
                                        FStar_Pervasives_Native.None,
                                        uu____15420)
                                       in
                                    let uu____15424 =
                                      let uu____15435 =
                                        let uu____15444 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.ml_bool_ty)
                                            (FStar_Extraction_ML_Syntax.MLE_Const
                                               (FStar_Extraction_ML_Syntax.MLC_Bool
                                                  false))
                                           in
                                        (FStar_Extraction_ML_Syntax.MLP_Wild,
                                          FStar_Pervasives_Native.None,
                                          uu____15444)
                                         in
                                      [uu____15435]  in
                                    uu____15400 :: uu____15424  in
                                  (uu____15383, uu____15389)  in
                                FStar_Extraction_ML_Syntax.MLE_Match
                                  uu____15368
                                 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                uu____15367
                               in
                            ((FStar_List.append wildcards [(mlid, targ)]),
                              uu____15366)
                             in
                          FStar_Extraction_ML_Syntax.MLE_Fun uu____15354  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty disc_ty)
                          uu____15353
                         in
                      let uu____15505 =
                        FStar_Extraction_ML_UEnv.mlpath_of_lident env
                          discName
                         in
                      (match uu____15505 with
                       | (uu____15506,name) ->
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
  