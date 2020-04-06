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
      | FStar_Syntax_Syntax.Tm_ascribed uu____462 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____491 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____501 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____501
      | FStar_Syntax_Syntax.Tm_uvar uu____502 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____516 -> false
      | FStar_Syntax_Syntax.Tm_name uu____518 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____520 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____528 -> false
      | FStar_Syntax_Syntax.Tm_type uu____530 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____532,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let topt =
            let uu____562 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] uu____562
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match topt with
           | FStar_Pervasives_Native.None  -> false
           | FStar_Pervasives_Native.Some (uu____569,t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____575 ->
          let uu____592 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____592 with | (head,uu____611) -> is_arity env head)
      | FStar_Syntax_Syntax.Tm_uinst (head,uu____637) -> is_arity env head
      | FStar_Syntax_Syntax.Tm_refine (x,uu____643) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____648,body,uu____650) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____675,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____695,branches) ->
          (match branches with
           | (uu____734,uu____735,e)::uu____737 -> is_arity env e
           | uu____784 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____816 ->
          let uu____839 =
            let uu____841 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____841  in
          failwith uu____839
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____845 =
            let uu____847 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____847  in
          failwith uu____845
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____852 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____852
      | FStar_Syntax_Syntax.Tm_constant uu____853 -> false
      | FStar_Syntax_Syntax.Tm_type uu____855 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____857 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____865 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____884;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____885;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____886;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____888;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____889;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____890;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____891;_},s)
          ->
          let uu____940 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____940
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____941;
            FStar_Syntax_Syntax.index = uu____942;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____947;
            FStar_Syntax_Syntax.index = uu____948;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____954,uu____955) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____997) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1004) ->
          let uu____1029 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____1029 with
           | (uu____1035,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____1055 =
            let uu____1060 =
              let uu____1061 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1061]  in
            FStar_Syntax_Subst.open_term uu____1060 body  in
          (match uu____1055 with
           | (uu____1081,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1083,lbs),body) ->
          let uu____1103 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____1103 with
           | (uu____1111,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1117,branches) ->
          (match branches with
           | b::uu____1157 ->
               let uu____1202 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1202 with
                | (uu____1204,uu____1205,e) -> is_type_aux env e)
           | uu____1223 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1241 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1250) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head,uu____1256) -> is_type_aux env head
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1297  ->
           let uu____1298 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1300 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1298
             uu____1300);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1309  ->
            if b
            then
              let uu____1311 = FStar_Syntax_Print.term_to_string t  in
              let uu____1313 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1311
                uu____1313
            else
              (let uu____1318 = FStar_Syntax_Print.term_to_string t  in
               let uu____1320 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1318 uu____1320));
       b)
  
let is_type_binder :
  'uuuuuu1330 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu1330) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1357 =
      let uu____1358 = FStar_Syntax_Subst.compress t  in
      uu____1358.FStar_Syntax_Syntax.n  in
    match uu____1357 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1362;
          FStar_Syntax_Syntax.fv_delta = uu____1363;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1365;
          FStar_Syntax_Syntax.fv_delta = uu____1366;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1367);_}
        -> true
    | uu____1375 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1384 =
      let uu____1385 = FStar_Syntax_Subst.compress t  in
      uu____1385.FStar_Syntax_Syntax.n  in
    match uu____1384 with
    | FStar_Syntax_Syntax.Tm_constant uu____1389 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1391 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1393 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1395 -> true
    | FStar_Syntax_Syntax.Tm_app (head,args) ->
        let uu____1441 = is_constructor head  in
        if uu____1441
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1463  ->
                  match uu____1463 with
                  | (te,uu____1472) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1481) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1487,uu____1488) ->
        is_fstar_value t1
    | uu____1529 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1539 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1541 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1544 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1546 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1559,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1568,fields) ->
        FStar_Util.for_all
          (fun uu____1598  ->
             match uu____1598 with | (uu____1605,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1610) -> is_ml_value h
    | uu____1615 -> false
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1697 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1699 = FStar_Syntax_Util.is_fun e'  in
          if uu____1699
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : unit -> FStar_Syntax_Syntax.binder) =
  fun uu____1717  ->
    let uu____1718 =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.t_unit
       in
    FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1718
  
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
      (let uu____1809 = FStar_List.hd l  in
       match uu____1809 with
       | (p1,w1,e1) ->
           let uu____1844 =
             let uu____1853 = FStar_List.tl l  in FStar_List.hd uu____1853
              in
           (match uu____1844 with
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
                 | uu____1937 -> def)))
  
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
      let uu____2002 =
        FStar_List.fold_right
          (fun t  ->
             fun uu____2033  ->
               match uu____2033 with
               | (uenv,vs) ->
                   let uu____2072 = FStar_Extraction_ML_UEnv.new_mlident uenv
                      in
                   (match uu____2072 with
                    | (uenv1,v) -> (uenv1, ((v, t) :: vs)))) ts (g, [])
         in
      match uu____2002 with | (g1,vs_ts) -> (vs_ts, g1)
  
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
          let uu____2189 = s  in
          match uu____2189 with
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
                      let uu___372_2221 = e  in
                      {
                        FStar_Extraction_ML_Syntax.expr =
                          (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                        FStar_Extraction_ML_Syntax.mlty = ts;
                        FStar_Extraction_ML_Syntax.loc =
                          (uu___372_2221.FStar_Extraction_ML_Syntax.loc)
                      }  in
                    (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
              else
                if n_args < n_vars
                then
                  (let extra_tyargs =
                     let uu____2236 = FStar_Util.first_N n_args vars  in
                     match uu____2236 with
                     | (uu____2250,rest_vars) ->
                         FStar_All.pipe_right rest_vars
                           (FStar_List.map
                              (fun uu____2271  ->
                                 FStar_Extraction_ML_Syntax.MLTY_Erased))
                      in
                   let tyargs1 = FStar_List.append tyargs extra_tyargs  in
                   let ts = instantiate_tyscheme (vars, t) tyargs1  in
                   let tapp =
                     let uu___383_2278 = e  in
                     {
                       FStar_Extraction_ML_Syntax.expr =
                         (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                       FStar_Extraction_ML_Syntax.mlty = ts;
                       FStar_Extraction_ML_Syntax.loc =
                         (uu___383_2278.FStar_Extraction_ML_Syntax.loc)
                     }  in
                   let t1 =
                     FStar_List.fold_left
                       (fun out  ->
                          fun t1  ->
                            FStar_Extraction_ML_Syntax.MLTY_Fun
                              (t1, FStar_Extraction_ML_Syntax.E_PURE, out))
                       ts extra_tyargs
                      in
                   let uu____2286 = fresh_mlidents extra_tyargs g  in
                   match uu____2286 with
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
        let uu____2353 = FStar_Extraction_ML_Util.doms_and_cod t  in
        match uu____2353 with
        | (ts,r) ->
            if ts = []
            then e
            else
              (let uu____2371 = fresh_mlidents ts g  in
               match uu____2371 with
               | (vs_ts,g1) ->
                   let vs_es =
                     FStar_List.map
                       (fun uu____2410  ->
                          match uu____2410 with
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
      let uu____2441 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2441 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____2461 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____2461 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2465 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let uu____2471 = fresh_mlidents ts g  in
             match uu____2471 with
             | (vs_ts,g1) ->
                 let uu____2499 =
                   let uu____2500 =
                     let uu____2512 = body r  in (vs_ts, uu____2512)  in
                   FStar_Extraction_ML_Syntax.MLE_Fun uu____2500  in
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
                   uu____2499)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g  ->
    fun expect  ->
      fun e  ->
        let uu____2536 =
          (FStar_Options.ml_no_eta_expand_coertions ()) ||
            (let uu____2539 = FStar_Options.codegen ()  in
             uu____2539 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
           in
        if uu____2536 then e else eta_expand g expect e
  
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
            | uu____2617 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____2672 =
              match uu____2672 with
              | (pat,w,b) ->
                  let uu____2696 = aux b ty1 expect1  in (pat, w, uu____2696)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____2703,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____2706,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____2738 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____2754 = type_leq g s0 t0  in
                if uu____2754
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____2760 =
                       let uu____2761 =
                         let uu____2762 =
                           let uu____2769 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____2769, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____2762  in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____2761  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____2760;
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
               (lbs,body),uu____2788,uu____2789) ->
                let uu____2802 =
                  let uu____2803 =
                    let uu____2814 = aux body ty1 expect1  in
                    (lbs, uu____2814)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____2803  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2802
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____2823,uu____2824) ->
                let uu____2845 =
                  let uu____2846 =
                    let uu____2861 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2861)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____2846  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2845
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____2901,uu____2902) ->
                let uu____2907 =
                  let uu____2908 =
                    let uu____2917 = aux b1 ty1 expect1  in
                    let uu____2918 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____2917, uu____2918)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____2908  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2907
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____2926,uu____2927)
                ->
                let uu____2930 = FStar_Util.prefix es  in
                (match uu____2930 with
                 | (prefix,last) ->
                     let uu____2943 =
                       let uu____2944 =
                         let uu____2947 =
                           let uu____2950 = aux last ty1 expect1  in
                           [uu____2950]  in
                         FStar_List.append prefix uu____2947  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____2944  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____2943)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____2953,uu____2954) ->
                let uu____2975 =
                  let uu____2976 =
                    let uu____2991 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2991)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____2976  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2975
            | uu____3028 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'uuuuuu3048 .
    'uuuuuu3048 ->
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
            let uu____3075 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____3075 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____3088 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____3096 ->
                     let uu____3097 =
                       let uu____3099 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____3100 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____3099 uu____3100  in
                     if uu____3097
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3106  ->
                             let uu____3107 =
                               let uu____3109 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3109 e
                                in
                             let uu____3110 =
                               let uu____3112 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3112 ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____3107 uu____3110);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3121  ->
                             let uu____3122 =
                               let uu____3124 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3124 e
                                in
                             let uu____3125 =
                               let uu____3127 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3127 ty1
                                in
                             let uu____3128 =
                               let uu____3130 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3130 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____3122 uu____3125 uu____3128);
                        (let uu____3132 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand g expect uu____3132)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____3144 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____3144 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____3146 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
  fun uu____3160  ->
    let uu____3161 = FStar_Options.use_nbe_for_extraction ()  in
    if uu____3161
    then extraction_norm_steps_nbe
    else extraction_norm_steps_core
  
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____3182 -> c
    | FStar_Syntax_Syntax.GTotal uu____3191 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____3227  ->
               match uu____3227 with
               | (uu____3242,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___550_3255 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___550_3255.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___550_3255.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___550_3255.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___550_3255.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___553_3259 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___553_3259.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___553_3259.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let maybe_reify_comp :
  'uuuuuu3271 .
    'uuuuuu3271 ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun g  ->
    fun env  ->
      fun c  ->
        let c1 = comp_no_args c  in
        let uu____3290 =
          let uu____3292 =
            let uu____3293 =
              FStar_All.pipe_right c1 FStar_Syntax_Util.comp_effect_name  in
            FStar_All.pipe_right uu____3293
              (FStar_TypeChecker_Env.norm_eff_name env)
             in
          FStar_All.pipe_right uu____3292
            (FStar_TypeChecker_Env.is_reifiable_effect env)
           in
        if uu____3290
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
      let arg_as_mlty g1 uu____3346 =
        match uu____3346 with
        | (a,uu____3354) ->
            let uu____3359 = is_type g1 a  in
            if uu____3359
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____3380 =
          let uu____3382 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____3382  in
        if uu____3380
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____3387 =
             let uu____3394 =
               let uu____3403 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
               FStar_TypeChecker_Env.lookup_lid uu____3403
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____3394 with
             | ((uu____3410,fvty),uu____3412) ->
                 let fvty1 =
                   let uu____3418 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1
                      in
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant] uu____3418 fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____3387 with
           | (formals,uu____3420) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3457 = FStar_Util.first_N n_args formals  in
                   match uu____3457 with
                   | (uu____3486,rest) ->
                       let uu____3520 =
                         FStar_List.map
                           (fun uu____3530  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____3520
                 else mlargs  in
               let nm =
                 let uu____3540 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____3540 with
                 | FStar_Pervasives_Native.Some p -> p
                 | FStar_Pervasives_Native.None  ->
                     FStar_Extraction_ML_UEnv.mlpath_of_lident g1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm))
         in
      let aux env t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_type uu____3558 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3559 ->
            let uu____3560 =
              let uu____3562 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3562
               in
            failwith uu____3560
        | FStar_Syntax_Syntax.Tm_delayed uu____3565 ->
            let uu____3588 =
              let uu____3590 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3590
               in
            failwith uu____3588
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3593 =
              let uu____3595 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3595
               in
            failwith uu____3593
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3599 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____3599
        | FStar_Syntax_Syntax.Tm_constant uu____3600 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____3601 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____3608 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____3622) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3627;
               FStar_Syntax_Syntax.index = uu____3628;
               FStar_Syntax_Syntax.sort = t2;_},uu____3630)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3639) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3645,uu____3646) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____3719 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____3719 with
             | (bs1,c1) ->
                 let uu____3726 = binders_as_ml_binders env bs1  in
                 (match uu____3726 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let uu____3755 =
                          let uu____3756 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv env1  in
                          maybe_reify_comp env1 uu____3756 c1  in
                        translate_term_to_mlty env1 uu____3755  in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____3758 =
                        FStar_List.fold_right
                          (fun uu____3778  ->
                             fun uu____3779  ->
                               match (uu____3778, uu____3779) with
                               | ((uu____3802,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____3758 with | (uu____3817,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let res =
              let uu____3846 =
                let uu____3847 = FStar_Syntax_Util.un_uinst head  in
                uu____3847.FStar_Syntax_Syntax.n  in
              match uu____3846 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head1,args') ->
                  let uu____3878 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head1, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____3878
              | uu____3899 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____3902) ->
            let uu____3927 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____3927 with
             | (bs1,ty1) ->
                 let uu____3934 = binders_as_ml_binders env bs1  in
                 (match uu____3934 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____3962 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____3976 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____4008 ->
            let uu____4015 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____4015 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____4021 -> false  in
      let uu____4023 =
        let uu____4025 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Util.must_erase_for_extraction uu____4025 t0  in
      if uu____4023
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____4030 = is_top_ty mlt  in
         if uu____4030 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____4048 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____4105  ->
                fun b  ->
                  match uu____4105 with
                  | (ml_bs,env) ->
                      let uu____4151 = is_type_binder g b  in
                      if uu____4151
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1 true  in
                        let ml_b =
                          let uu____4174 =
                            FStar_Extraction_ML_UEnv.lookup_ty env1 b1  in
                          uu____4174.FStar_Extraction_ML_UEnv.ty_b_name  in
                        let ml_b1 =
                          (ml_b, FStar_Extraction_ML_Syntax.ml_unit_ty)  in
                        ((ml_b1 :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____4200 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____4200 with
                         | (env1,b2,uu____4225) ->
                             let ml_b = (b2, t)  in ((ml_b :: ml_bs), env1)))
             ([], g))
         in
      match uu____4048 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        let uu____4310 = extraction_norm_steps ()  in
        let uu____4311 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Normalize.normalize uu____4310 uu____4311 t0  in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____4330) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4333,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4337 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____4371 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4372 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4373 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4382 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
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
            (fun uu____4458  ->
               fun x  -> match uu____4458 with | (p,s) -> (s, x)) fns1 xs
  
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
            let uu____4510 = FStar_Extraction_ML_Util.is_xtuple d  in
            (match uu____4510 with
             | FStar_Pervasives_Native.Some n ->
                 FStar_Extraction_ML_Syntax.MLP_Tuple pats
             | uu____4517 ->
                 (match q with
                  | FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                      let path =
                        FStar_List.map FStar_Ident.text_of_id
                          ty.FStar_Ident.ns
                         in
                      let fs = record_fields g ty fns pats  in
                      FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                  | uu____4550 -> p))
        | uu____4553 -> p
  
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
                       (fun uu____4655  ->
                          let uu____4656 =
                            let uu____4658 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4658 t'
                             in
                          let uu____4659 =
                            let uu____4661 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4661 t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4656 uu____4659)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____4696 = FStar_Options.codegen ()  in
                uu____4696 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4701 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4714 =
                        let uu____4715 =
                          let uu____4716 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4716  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4715
                         in
                      (uu____4714, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        let uu____4738 =
                          let uu____4739 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                          uu____4739.FStar_TypeChecker_Env.dsenv  in
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          uu____4738 c sw FStar_Range.dummyRange
                         in
                      let uu____4740 = term_as_mlexpr g source_term  in
                      (match uu____4740 with
                       | (mlterm,uu____4752,mlty) -> (mlterm, mlty))
                   in
                (match uu____4701 with
                 | (mlc,ml_ty) ->
                     let uu____4771 = FStar_Extraction_ML_UEnv.new_mlident g
                        in
                     (match uu____4771 with
                      | (g1,x) ->
                          let when_clause =
                            let uu____4797 =
                              let uu____4798 =
                                let uu____4805 =
                                  let uu____4808 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         ml_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Var x)
                                     in
                                  [uu____4808; mlc]  in
                                (FStar_Extraction_ML_Util.prims_op_equality,
                                  uu____4805)
                                 in
                              FStar_Extraction_ML_Syntax.MLE_App uu____4798
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_bool_ty)
                              uu____4797
                             in
                          let uu____4811 = ok ml_ty  in
                          (g1,
                            (FStar_Pervasives_Native.Some
                               ((FStar_Extraction_ML_Syntax.MLP_Var x),
                                 [when_clause])), uu____4811)))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  let uu____4832 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_TcTerm.tc_constant uu____4832
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____4834 =
                  let uu____4843 =
                    let uu____4850 =
                      let uu____4851 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4851  in
                    (uu____4850, [])  in
                  FStar_Pervasives_Native.Some uu____4843  in
                let uu____4860 = ok mlty  in (g, uu____4834, uu____4860)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4873 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4873 with
                 | (g1,x1,uu____4901) ->
                     let uu____4904 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4904))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4942 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4942 with
                 | (g1,x1,uu____4970) ->
                     let uu____4973 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4973))
            | FStar_Syntax_Syntax.Pat_dot_term uu____5009 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____5052 =
                  let uu____5061 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____5061 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____5070;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n;
                          FStar_Extraction_ML_Syntax.mlty = uu____5072;
                          FStar_Extraction_ML_Syntax.loc = uu____5073;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____5075;_}
                      -> (n, ttys)
                  | uu____5082 -> failwith "Expected a constructor"  in
                (match uu____5052 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____5119 = FStar_Util.first_N nTyVars pats  in
                     (match uu____5119 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___856_5223  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____5254  ->
                                               match uu____5254 with
                                               | (p1,uu____5261) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5264,t) ->
                                                        term_as_mlty g t
                                                    | uu____5270 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5274 
                                                              ->
                                                              let uu____5275
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5275);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____5279 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____5279)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____5308 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____5345  ->
                                   match uu____5345 with
                                   | (p1,imp1) ->
                                       let uu____5367 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____5367 with
                                        | (g2,p2,uu____5398) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____5308 with
                           | (g1,tyMLPats) ->
                               let uu____5462 =
                                 FStar_Util.fold_map
                                   (fun uu____5527  ->
                                      fun uu____5528  ->
                                        match (uu____5527, uu____5528) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____5626 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd))
                                              | uu____5686 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____5626 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____5757 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____5757 with
                                                  | (g3,p2,uu____5800) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____5462 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____5921 =
                                      let uu____5932 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5983  ->
                                                match uu___0_5983 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____6025 -> []))
                                         in
                                      FStar_All.pipe_right uu____5932
                                        FStar_List.split
                                       in
                                    (match uu____5921 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____6101 -> false  in
                                         let uu____6111 =
                                           let uu____6120 =
                                             let uu____6127 =
                                               resugar_pat g2
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____6130 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____6127, uu____6130)  in
                                           FStar_Pervasives_Native.Some
                                             uu____6120
                                            in
                                         (g2, uu____6111, pat_ty_compat))))))
  
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
            let uu____6262 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____6262 with
            | (g2,FStar_Pervasives_Native.Some (x,v),b) -> (g2, (x, v), b)
            | uu____6325 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd::tl ->
                let uu____6373 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl
                   in
                FStar_Pervasives_Native.Some uu____6373
             in
          let uu____6374 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____6374 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____6539,t1) ->
                let uu____6541 = FStar_Extraction_ML_UEnv.new_mlident g1  in
                (match uu____6541 with
                 | (g2,x) ->
                     let uu____6566 =
                       let uu____6578 =
                         let uu____6588 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty t0)
                             (FStar_Extraction_ML_Syntax.MLE_Var x)
                            in
                         ((x, t0), uu____6588)  in
                       uu____6578 :: more_args  in
                     eta_args g2 uu____6566 t1)
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6604,uu____6605)
                -> ((FStar_List.rev more_args), t)
            | uu____6630 ->
                let uu____6631 =
                  let uu____6633 =
                    let uu____6635 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu____6635
                      mlAppExpr
                     in
                  let uu____6636 =
                    let uu____6638 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlty uu____6638 t  in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6633 uu____6636
                   in
                failwith uu____6631
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____6672,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields g tyname fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6709 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____6731 = eta_args g [] residualType  in
            match uu____6731 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____6789 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____6789
                 | uu____6790 ->
                     let uu____6802 = FStar_List.unzip eargs  in
                     (match uu____6802 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head,args)
                               ->
                               let body =
                                 let uu____6848 =
                                   let uu____6849 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6849
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6848
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6859 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6863,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6867;
                FStar_Extraction_ML_Syntax.loc = uu____6868;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let fn =
                let uu____6880 =
                  let uu____6885 =
                    let uu____6886 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6886
                      constrname
                     in
                  (uu____6885, f)  in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6880
                 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____6889 ->
                    let uu____6892 =
                      let uu____6899 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6899, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6892
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
                     FStar_Extraction_ML_Syntax.mlty = uu____6903;
                     FStar_Extraction_ML_Syntax.loc = uu____6904;_},uu____6905);
                FStar_Extraction_ML_Syntax.mlty = uu____6906;
                FStar_Extraction_ML_Syntax.loc = uu____6907;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let fn =
                let uu____6923 =
                  let uu____6928 =
                    let uu____6929 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6929
                      constrname
                     in
                  (uu____6928, f)  in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6923
                 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____6932 ->
                    let uu____6935 =
                      let uu____6942 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6942, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6935
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6946;
                FStar_Extraction_ML_Syntax.loc = uu____6947;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6955 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6955
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6959;
                FStar_Extraction_ML_Syntax.loc = uu____6960;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6962)) ->
              let uu____6975 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6975
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6979;
                     FStar_Extraction_ML_Syntax.loc = uu____6980;_},uu____6981);
                FStar_Extraction_ML_Syntax.mlty = uu____6982;
                FStar_Extraction_ML_Syntax.loc = uu____6983;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6995 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6995
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6999;
                     FStar_Extraction_ML_Syntax.loc = uu____7000;_},uu____7001);
                FStar_Extraction_ML_Syntax.mlty = uu____7002;
                FStar_Extraction_ML_Syntax.loc = uu____7003;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7005)) ->
              let uu____7022 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7022
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____7028 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7028
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7032)) ->
              let uu____7041 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7041
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7045;
                FStar_Extraction_ML_Syntax.loc = uu____7046;_},uu____7047),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____7054 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7054
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7058;
                FStar_Extraction_ML_Syntax.loc = uu____7059;_},uu____7060),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7061)) ->
              let uu____7074 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7074
          | uu____7077 -> mlAppExpr
  
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
        | uu____7108 -> (ml_e, tag)
  
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
      let maybe_generalize uu____7169 =
        match uu____7169 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____7190;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____7195;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____7276 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____7353 =
              let uu____7355 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Util.must_erase_for_extraction uu____7355
                lbtyp1
               in
            if uu____7353
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____7440 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____7440 (is_type_binder g) ->
                   let uu____7462 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____7462 with
                    | (bs1,c1) ->
                        let uu____7488 =
                          let uu____7501 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____7547 = is_type_binder g x  in
                                 Prims.op_Negation uu____7547) bs1
                             in
                          match uu____7501 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____7674 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____7674)
                           in
                        (match uu____7488 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____7736 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____7736
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____7785 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____7785 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7837 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____7837 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7940  ->
                                                       fun uu____7941  ->
                                                         match (uu____7940,
                                                                 uu____7941)
                                                         with
                                                         | ((x,uu____7967),
                                                            (y,uu____7969))
                                                             ->
                                                             let uu____7990 =
                                                               let uu____7997
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____7997)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7990)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____8014  ->
                                                       match uu____8014 with
                                                       | (a,uu____8022) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a false) g
                                                  targs
                                                 in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty
                                                 in
                                              let polytype =
                                                let uu____8034 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____8054  ->
                                                          match uu____8054
                                                          with
                                                          | (x,uu____8063) ->
                                                              let uu____8068
                                                                =
                                                                FStar_Extraction_ML_UEnv.lookup_ty
                                                                  env x
                                                                 in
                                                              uu____8068.FStar_Extraction_ML_UEnv.ty_b_name))
                                                   in
                                                (uu____8034, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____8080 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____8080)
                                                      ||
                                                      (let uu____8083 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____8083)
                                                | uu____8085 -> false  in
                                              let rest_args1 =
                                                if add_unit
                                                then
                                                  let uu____8097 =
                                                    unit_binder ()  in
                                                  uu____8097 :: rest_args
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____8154 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8173  ->
                                           match uu____8173 with
                                           | (a,uu____8181) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8193 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8213  ->
                                              match uu____8213 with
                                              | (x,uu____8222) ->
                                                  let uu____8227 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8227.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8193, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8267  ->
                                            match uu____8267 with
                                            | (bv,uu____8275) ->
                                                let uu____8280 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8280
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____8310 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8323  ->
                                           match uu____8323 with
                                           | (a,uu____8331) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8343 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8363  ->
                                              match uu____8363 with
                                              | (x,uu____8372) ->
                                                  let uu____8377 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8377.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8343, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8417  ->
                                            match uu____8417 with
                                            | (bv,uu____8425) ->
                                                let uu____8430 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8430
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
                              | FStar_Syntax_Syntax.Tm_name uu____8460 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8473  ->
                                           match uu____8473 with
                                           | (a,uu____8481) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8493 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8513  ->
                                              match uu____8513 with
                                              | (x,uu____8522) ->
                                                  let uu____8527 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8527.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8493, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8567  ->
                                            match uu____8567 with
                                            | (bv,uu____8575) ->
                                                let uu____8580 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8580
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
                              | uu____8610 -> err_value_restriction lbdef1)))
               | uu____8630 -> no_gen ())
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
           fun uu____8781  ->
             match uu____8781 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____8842 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____8842 with
                  | (env1,uu____8859,exp_binding) ->
                      let uu____8863 =
                        let uu____8868 = FStar_Util.right lbname  in
                        (uu____8868, exp_binding)  in
                      (env1, uu____8863))) g lbs1
  
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
            (fun uu____8935  ->
               let uu____8936 = FStar_Syntax_Print.term_to_string e  in
               let uu____8938 =
                 let uu____8940 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g  in
                 FStar_Extraction_ML_Code.string_of_mlty uu____8940 ty  in
               let uu____8941 = FStar_Extraction_ML_Util.eff_to_string f  in
               FStar_Util.print3 "Checking %s at type %s and eff %s\n"
                 uu____8936 uu____8938 uu____8941);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____8948) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8949 ->
               let uu____8954 = term_as_mlexpr g e  in
               (match uu____8954 with
                | (ml_e,tag,t) ->
                    let uu____8968 = FStar_Extraction_ML_Util.eff_leq tag f
                       in
                    if uu____8968
                    then
                      let uu____8975 =
                        maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t ty
                         in
                      (uu____8975, ty)
                    else
                      (match (tag, f, ty) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST
                          ,FStar_Extraction_ML_Syntax.E_PURE
                          ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                           let uu____8982 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t
                               ty
                              in
                           (uu____8982, ty)
                       | uu____8983 ->
                           (err_unexpected_eff g e ty f tag;
                            (let uu____8991 =
                               maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e
                                 t ty
                                in
                             (uu____8991, ty))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____9000 = term_as_mlexpr' g e  in
      match uu____9000 with
      | (e1,f,t) ->
          let uu____9016 = maybe_promote_effect e1 f t  in
          (match uu____9016 with | (e2,f1) -> (e2, f1, t))

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
           let uu____9042 =
             let uu____9044 =
               FStar_Range.string_of_range top1.FStar_Syntax_Syntax.pos  in
             let uu____9046 = FStar_Syntax_Print.tag_of_term top1  in
             let uu____9048 = FStar_Syntax_Print.term_to_string top1  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____9044 uu____9046 uu____9048
              in
           FStar_Util.print_string uu____9042);
      (let is_match t =
         let uu____9058 =
           let uu____9059 =
             let uu____9062 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9062 FStar_Syntax_Util.unascribe  in
           uu____9059.FStar_Syntax_Syntax.n  in
         match uu____9058 with
         | FStar_Syntax_Syntax.Tm_match uu____9066 -> true
         | uu____9090 -> false  in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____9109  ->
              match uu____9109 with
              | (t,uu____9118) ->
                  let uu____9123 =
                    let uu____9124 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
                    uu____9124.FStar_Syntax_Syntax.n  in
                  (match uu____9123 with
                   | FStar_Syntax_Syntax.Tm_name uu____9130 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____9132 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____9134 -> true
                   | uu____9136 -> false))
          in
       let apply_to_match_branches head args =
         let uu____9175 =
           let uu____9176 =
             let uu____9179 =
               FStar_All.pipe_right head FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9179 FStar_Syntax_Util.unascribe  in
           uu____9176.FStar_Syntax_Syntax.n  in
         match uu____9175 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee,branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____9303  ->
                       match uu____9303 with
                       | (pat,when_opt,body) ->
                           (pat, when_opt,
                             (let uu___1323_9360 = body  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1323_9360.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1323_9360.FStar_Syntax_Syntax.vars)
                              }))))
                in
             let uu___1326_9375 = head  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1326_9375.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1326_9375.FStar_Syntax_Syntax.vars)
             }
         | uu____9396 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match"
          in
       let t = FStar_Syntax_Subst.compress top1  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9407 =
             let uu____9409 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9409
              in
           failwith uu____9407
       | FStar_Syntax_Syntax.Tm_delayed uu____9418 ->
           let uu____9441 =
             let uu____9443 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9443
              in
           failwith uu____9441
       | FStar_Syntax_Syntax.Tm_uvar uu____9452 ->
           let uu____9465 =
             let uu____9467 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9467
              in
           failwith uu____9465
       | FStar_Syntax_Syntax.Tm_bvar uu____9476 ->
           let uu____9477 =
             let uu____9479 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9479
              in
           failwith uu____9477
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9489 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____9489
       | FStar_Syntax_Syntax.Tm_type uu____9490 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9491 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9498 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____9514;_})
           ->
           let uu____9527 =
             let uu____9528 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9528  in
           (match uu____9527 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9535;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9537;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9538;_} ->
                let uu____9541 =
                  let uu____9542 =
                    let uu____9543 =
                      let uu____9550 =
                        let uu____9553 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____9553]  in
                      (fw, uu____9550)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9543  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9542
                   in
                (uu____9541, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9571 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____9571 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9579 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____9579 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____9590 =
                         let uu____9597 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____9597
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____9590 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____9605 =
                         let uu____9616 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____9616]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9605
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9643 =
                    let uu____9650 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____9650 tv  in
                  uu____9643 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____9658 =
                    let uu____9669 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____9669]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9658
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____9696)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9729 =
                  let uu____9736 =
                    let uu____9745 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.effect_decl_opt uu____9745 m  in
                  FStar_Util.must uu____9736  in
                (match uu____9729 with
                 | (ed,qualifiers) ->
                     let uu____9764 =
                       let uu____9766 =
                         let uu____9768 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                         FStar_TypeChecker_Env.is_reifiable_effect uu____9768
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____9766  in
                     if uu____9764
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9785 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9787) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9793) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9799 =
             let uu____9806 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_TcTerm.type_of_tot_term uu____9806 t  in
           (match uu____9799 with
            | (uu____9813,ty,uu____9815) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____9817 =
                  let uu____9818 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9818  in
                (uu____9817, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9819 ->
           let uu____9820 = is_type g t  in
           if uu____9820
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9831 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____9831 with
              | (FStar_Util.Inl uu____9844,uu____9845) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9850;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9853;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____9871 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____9871, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9872 -> instantiate_maybe_partial g x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9874 = is_type g t  in
           if uu____9874
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9885 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____9885 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9894;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9897;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9905  ->
                        let uu____9906 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____9908 =
                          let uu____9910 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            uu____9910 x
                           in
                        let uu____9911 =
                          let uu____9913 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlty uu____9913
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9906 uu____9908 uu____9911);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____9925 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____9925, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9926 -> instantiate_maybe_partial g x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____9954 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____9954 with
            | (bs1,body1) ->
                let uu____9967 = binders_as_ml_binders g bs1  in
                (match uu____9967 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____10003 =
                             let uu____10005 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Env.is_reifiable_rc
                               uu____10005 rc
                              in
                           if uu____10003
                           then
                             let uu____10007 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Util.reify_body uu____10007
                               [FStar_TypeChecker_Env.Inlining] body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____10013  ->
                                 let uu____10014 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n"
                                   uu____10014);
                            body1)
                        in
                     let uu____10017 = term_as_mlexpr env body2  in
                     (match uu____10017 with
                      | (ml_body,f,t1) ->
                          let uu____10033 =
                            FStar_List.fold_right
                              (fun uu____10053  ->
                                 fun uu____10054  ->
                                   match (uu____10053, uu____10054) with
                                   | ((uu____10077,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____10033 with
                           | (f1,tfun) ->
                               let uu____10100 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____10100, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____10108;
              FStar_Syntax_Syntax.vars = uu____10109;_},(a1,uu____10111)::[])
           ->
           let ty =
             let uu____10151 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____10151  in
           let uu____10152 =
             let uu____10153 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____10153
              in
           (uu____10152, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____10154;
              FStar_Syntax_Syntax.vars = uu____10155;_},(t1,uu____10157)::
            (r,uu____10159)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____10214);
              FStar_Syntax_Syntax.pos = uu____10215;
              FStar_Syntax_Syntax.vars = uu____10216;_},uu____10217)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head,args) when
           (is_match head) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____10276 =
             FStar_All.pipe_right args (apply_to_match_branches head)  in
           FStar_All.pipe_right uu____10276 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_10330  ->
                        match uu___1_10330 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____10333 -> false)))
              in
           let uu____10335 =
             let uu____10336 =
               let uu____10339 =
                 FStar_All.pipe_right head FStar_Syntax_Subst.compress  in
               FStar_All.pipe_right uu____10339 FStar_Syntax_Util.unascribe
                in
             uu____10336.FStar_Syntax_Syntax.n  in
           (match uu____10335 with
            | FStar_Syntax_Syntax.Tm_abs (bs,uu____10349,_rc) ->
                let uu____10375 =
                  let uu____10376 =
                    let uu____10381 =
                      FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses]
                      uu____10381
                     in
                  FStar_All.pipe_right t uu____10376  in
                FStar_All.pipe_right uu____10375 (term_as_mlexpr g)
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                let e =
                  let uu____10389 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  let uu____10390 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg uu____10389
                    [FStar_TypeChecker_Env.Inlining] head uu____10390
                   in
                let tm =
                  let uu____10402 =
                    let uu____10407 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____10408 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____10407 uu____10408  in
                  uu____10402 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____10417 ->
                let rec extract_app is_data uu____10466 uu____10467 restArgs
                  =
                  match (uu____10466, uu____10467) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____10548 =
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
                         (fun uu____10575  ->
                            let uu____10576 =
                              let uu____10578 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              let uu____10579 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____10578 uu____10579
                               in
                            let uu____10580 =
                              let uu____10582 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlty
                                uu____10582 t1
                               in
                            let uu____10583 =
                              match restArgs with
                              | [] -> "none"
                              | (hd,uu____10594)::uu____10595 ->
                                  FStar_Syntax_Print.term_to_string hd
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10576 uu____10580 uu____10583);
                       (match (restArgs, t1) with
                        | ([],uu____10629) ->
                            let app =
                              let uu____10645 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10645
                               in
                            (app, f, t1)
                        | ((arg,uu____10647)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10678 =
                              let uu____10683 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____10683, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10678 rest
                        | ((e0,uu____10695)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____10728 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head)
                                 in
                              if uu____10728
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____10733 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____10733 with
                             | (e01,tInferred) ->
                                 let uu____10746 =
                                   let uu____10751 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____10751, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10746 rest)
                        | uu____10762 ->
                            let uu____10775 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____10775 with
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
                                  | uu____10847 ->
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
                let extract_app_maybe_projector is_data mlhead uu____10918
                  args1 =
                  match uu____10918 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10948)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____11032))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____11034,f',t3)) ->
                                 let uu____11072 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____11072 t3
                             | uu____11073 -> (args2, f1, t2)  in
                           let uu____11098 = remove_implicits args1 f t1  in
                           (match uu____11098 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____11154 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____11178 =
                  let head1 = FStar_Syntax_Util.un_uinst head  in
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____11186 ->
                      let uu____11187 =
                        let uu____11208 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1  in
                        match uu____11208 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11247  ->
                                  let uu____11248 =
                                    FStar_Syntax_Print.term_to_string head1
                                     in
                                  let uu____11250 =
                                    let uu____11252 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11252
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11253 =
                                    let uu____11255 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11255
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11256 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11248 uu____11250 uu____11253
                                    uu____11256);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11283 -> failwith "FIXME Ty"  in
                      (match uu____11187 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11359)::uu____11360 -> is_type g a
                             | uu____11387 -> false  in
                           let uu____11399 =
                             match vars with
                             | uu____11428::uu____11429 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11443 ->
                                 let n = FStar_List.length vars  in
                                 let uu____11449 =
                                   if (FStar_List.length args) <= n
                                   then
                                     let uu____11487 =
                                       FStar_List.map
                                         (fun uu____11499  ->
                                            match uu____11499 with
                                            | (x,uu____11507) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____11487, [])
                                   else
                                     (let uu____11530 =
                                        FStar_Util.first_N n args  in
                                      match uu____11530 with
                                      | (prefix,rest) ->
                                          let uu____11619 =
                                            FStar_List.map
                                              (fun uu____11631  ->
                                                 match uu____11631 with
                                                 | (x,uu____11639) ->
                                                     term_as_mlty g x) prefix
                                             in
                                          (uu____11619, rest))
                                    in
                                 (match uu____11449 with
                                  | (provided_type_args,rest) ->
                                      let uu____11690 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____11699 ->
                                            let uu____11700 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11700 with
                                             | (head2,uu____11712,t2) ->
                                                 (head2, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____11714 ->
                                            let uu____11716 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11716 with
                                             | (head2,uu____11728,t2) ->
                                                 (head2, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head2,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____11731;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____11732;_}::[])
                                            ->
                                            let uu____11735 =
                                              instantiate_maybe_partial g
                                                head2 (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11735 with
                                             | (head3,uu____11747,t2) ->
                                                 let uu____11749 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head3,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____11749, t2))
                                        | uu____11752 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____11690 with
                                       | (head2,t2) -> (head2, t2, rest)))
                              in
                           (match uu____11399 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11819 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____11819,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11820 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11829 ->
                      let uu____11830 =
                        let uu____11851 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1  in
                        match uu____11851 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11890  ->
                                  let uu____11891 =
                                    FStar_Syntax_Print.term_to_string head1
                                     in
                                  let uu____11893 =
                                    let uu____11895 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11895
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11896 =
                                    let uu____11898 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11898
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11899 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11891 uu____11893 uu____11896
                                    uu____11899);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11926 -> failwith "FIXME Ty"  in
                      (match uu____11830 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____12002)::uu____12003 -> is_type g a
                             | uu____12030 -> false  in
                           let uu____12042 =
                             match vars with
                             | uu____12071::uu____12072 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____12086 ->
                                 let n = FStar_List.length vars  in
                                 let uu____12092 =
                                   if (FStar_List.length args) <= n
                                   then
                                     let uu____12130 =
                                       FStar_List.map
                                         (fun uu____12142  ->
                                            match uu____12142 with
                                            | (x,uu____12150) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____12130, [])
                                   else
                                     (let uu____12173 =
                                        FStar_Util.first_N n args  in
                                      match uu____12173 with
                                      | (prefix,rest) ->
                                          let uu____12262 =
                                            FStar_List.map
                                              (fun uu____12274  ->
                                                 match uu____12274 with
                                                 | (x,uu____12282) ->
                                                     term_as_mlty g x) prefix
                                             in
                                          (uu____12262, rest))
                                    in
                                 (match uu____12092 with
                                  | (provided_type_args,rest) ->
                                      let uu____12333 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____12342 ->
                                            let uu____12343 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12343 with
                                             | (head2,uu____12355,t2) ->
                                                 (head2, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____12357 ->
                                            let uu____12359 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12359 with
                                             | (head2,uu____12371,t2) ->
                                                 (head2, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head2,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____12374;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____12375;_}::[])
                                            ->
                                            let uu____12378 =
                                              instantiate_maybe_partial g
                                                head2 (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12378 with
                                             | (head3,uu____12390,t2) ->
                                                 let uu____12392 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head3,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____12392, t2))
                                        | uu____12395 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____12333 with
                                       | (head2,t2) -> (head2, t2, rest)))
                              in
                           (match uu____12042 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12462 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____12462,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12463 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12472 ->
                      let uu____12473 = term_as_mlexpr g head1  in
                      (match uu____12473 with
                       | (head2,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head2 (f, t1) args)
                   in
                let uu____12489 = is_type g t  in
                if uu____12489
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12500 =
                     let uu____12501 = FStar_Syntax_Util.un_uinst head  in
                     uu____12501.FStar_Syntax_Syntax.n  in
                   match uu____12500 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12511 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____12511 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12520 -> extract_app_with_instantiations ())
                   | uu____12523 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____12526),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12591 =
                   let uu____12592 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                      in
                   maybe_reify_comp g uu____12592 c  in
                 term_as_mlty g uu____12591
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____12596 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____12596 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e') when
           (let uu____12628 = FStar_Syntax_Syntax.is_top_level [lb]  in
            Prims.op_Negation uu____12628) &&
             (let uu____12631 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs
                 in
              FStar_Util.is_some uu____12631)
           ->
           let b =
             let uu____12641 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                in
             (uu____12641, FStar_Pervasives_Native.None)  in
           let uu____12644 = FStar_Syntax_Subst.open_term [b] e'  in
           (match uu____12644 with
            | ((x,uu____12668)::uu____12669,body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str,uu____12698)::[]) ->
                      let uu____12723 =
                        let uu____12724 = FStar_Syntax_Subst.compress str  in
                        uu____12724.FStar_Syntax_Syntax.n  in
                      (match uu____12723 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s,uu____12730)) ->
                           let id =
                             let uu____12734 =
                               let uu____12740 =
                                 FStar_Syntax_Syntax.range_of_bv x  in
                               (s, uu____12740)  in
                             FStar_Ident.mk_ident uu____12734  in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             }  in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv  in
                           FStar_Pervasives_Native.Some bv1
                       | uu____12745 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                   in
                let remove_attr attrs =
                  let uu____12762 =
                    FStar_List.partition
                      (fun attr  ->
                         let uu____12774 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr]
                            in
                         FStar_Util.is_some uu____12774)
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match uu____12762 with
                  | (uu____12779,other_attrs) -> other_attrs  in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None  ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs  in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1785_12807 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1785_12807.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1785_12807.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1785_12807.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1785_12807.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1785_12807.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1785_12807.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs  in
                      let rename =
                        let uu____12815 =
                          let uu____12816 =
                            let uu____12823 =
                              FStar_Syntax_Syntax.bv_to_name y  in
                            (x, uu____12823)  in
                          FStar_Syntax_Syntax.NT uu____12816  in
                        [uu____12815]  in
                      let body1 =
                        let uu____12829 =
                          FStar_Syntax_Subst.subst rename body  in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____12829
                         in
                      let lb1 =
                        let uu___1792_12845 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1792_12845.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1792_12845.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1792_12845.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1792_12845.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1792_12845.FStar_Syntax_Syntax.lbpos)
                        }  in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1)
                   in
                let top2 =
                  let uu___1796_12862 = top1  in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1796_12862.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1796_12862.FStar_Syntax_Syntax.vars)
                  }  in
                term_as_mlexpr' g top2)
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____12885 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12901 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____12901
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____12916 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____12916  in
                   let lb1 =
                     let uu___1810_12918 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1810_12918.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1810_12918.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1810_12918.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1810_12918.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1810_12918.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1810_12918.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____12885 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____12943 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      let uu____12944 =
                        let uu____12945 =
                          let uu____12946 =
                            let uu____12950 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Pervasives_Native.fst uu____12950  in
                          let uu____12963 =
                            let uu____12967 =
                              let uu____12969 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Pervasives_Native.snd uu____12969  in
                            [uu____12967]  in
                          FStar_List.append uu____12946 uu____12963  in
                        FStar_Ident.lid_of_path uu____12945
                          FStar_Range.dummyRange
                         in
                      FStar_TypeChecker_Env.set_current_module uu____12943
                        uu____12944
                       in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let lbdef =
                              let uu____12996 = FStar_Options.ml_ish ()  in
                              if uu____12996
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____13008 =
                                   let uu____13009 =
                                     let uu____13010 =
                                       extraction_norm_steps ()  in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____13010
                                      in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____13009 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____13013 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____13013
                                 then
                                   ((let uu____13023 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____13023);
                                    (let a =
                                       let uu____13029 =
                                         let uu____13031 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____13031
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____13029 norm_call
                                        in
                                     a))
                                 else norm_call ())
                               in
                            let uu___1827_13038 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1827_13038.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1827_13038.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1827_13038.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1827_13038.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1827_13038.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1827_13038.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____13091 =
                  match uu____13091 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____13247  ->
                               match uu____13247 with
                               | (a,uu____13255) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     false) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____13262 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____13262 with
                       | (e1,ty) ->
                           let uu____13273 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____13273 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____13285 -> []  in
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
                let uu____13316 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____13413  ->
                         match uu____13413 with
                         | (env,lbs4) ->
                             let uu____13547 = lb  in
                             (match uu____13547 with
                              | (lbname,uu____13598,(t1,(uu____13600,polytype)),add_unit,uu____13603)
                                  ->
                                  let uu____13618 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____13618 with
                                   | (env1,nm,uu____13659) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____13316 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____13938 = term_as_mlexpr env_body e'1  in
                     (match uu____13938 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____13955 =
                              let uu____13958 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____13958  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13955
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____13971 =
                            let uu____13972 =
                              let uu____13973 =
                                let uu____13974 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____13974)  in
                              mk_MLE_Let top_level uu____13973 e'2  in
                            let uu____13983 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13972 uu____13983
                             in
                          (uu____13971, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____14022 = term_as_mlexpr g scrutinee  in
           (match uu____14022 with
            | (e,f_e,t_e) ->
                let uu____14038 = check_pats_for_ite pats  in
                (match uu____14038 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____14103 = term_as_mlexpr g then_e1  in
                            (match uu____14103 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____14119 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____14119 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____14135 =
                                        let uu____14146 =
                                          type_leq g t_then t_else  in
                                        if uu____14146
                                        then (t_else, no_lift)
                                        else
                                          (let uu____14167 =
                                             type_leq g t_else t_then  in
                                           if uu____14167
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____14135 with
                                       | (t_branch,maybe_lift) ->
                                           let uu____14214 =
                                             let uu____14215 =
                                               let uu____14216 =
                                                 let uu____14225 =
                                                   maybe_lift then_mle t_then
                                                    in
                                                 let uu____14226 =
                                                   let uu____14229 =
                                                     maybe_lift else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____14229
                                                    in
                                                 (e, uu____14225,
                                                   uu____14226)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____14216
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____14215
                                              in
                                           let uu____14232 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____14214, uu____14232,
                                             t_branch))))
                        | uu____14233 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____14251 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____14350 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____14350 with
                                    | (pat,when_opt,branch) ->
                                        let uu____14395 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____14395 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____14457 =
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
                                                   let uu____14480 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____14480 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____14457 with
                                              | (when_opt1,f_when) ->
                                                  let uu____14530 =
                                                    term_as_mlexpr env branch
                                                     in
                                                  (match uu____14530 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____14565 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14642 
                                                                 ->
                                                                 match uu____14642
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
                                                         uu____14565)))))
                               true)
                           in
                        match uu____14251 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14813  ->
                                      let uu____14814 =
                                        let uu____14816 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu____14816 e
                                         in
                                      let uu____14817 =
                                        let uu____14819 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu____14819 t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14814 uu____14817);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14845 =
                                   let uu____14846 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14846
                                    in
                                 (match uu____14845 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14853;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14855;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____14856;_}
                                      ->
                                      let uu____14859 =
                                        let uu____14860 =
                                          let uu____14861 =
                                            let uu____14868 =
                                              let uu____14871 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____14871]  in
                                            (fw, uu____14868)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14861
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14860
                                         in
                                      (uu____14859,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14875,uu____14876,(uu____14877,f_first,t_first))::rest
                                 ->
                                 let uu____14937 =
                                   FStar_List.fold_left
                                     (fun uu____14979  ->
                                        fun uu____14980  ->
                                          match (uu____14979, uu____14980)
                                          with
                                          | ((topt,f),(uu____15037,uu____15038,
                                                       (uu____15039,f_branch,t_branch)))
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
                                                    let uu____15095 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____15095
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____15102 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____15102
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
                                 (match uu____14937 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____15200  ->
                                                match uu____15200 with
                                                | (p,(wopt,uu____15229),
                                                   (b1,uu____15231,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____15250 -> b1
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
                                      let uu____15255 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____15255, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____15282 =
          let uu____15287 =
            let uu____15296 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_lid uu____15296 discName  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15287  in
        match uu____15282 with
        | (uu____15313,fstar_disc_type) ->
            let uu____15315 =
              let uu____15327 =
                let uu____15328 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____15328.FStar_Syntax_Syntax.n  in
              match uu____15327 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15343) ->
                  let binders1 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_15398  ->
                            match uu___2_15398 with
                            | (uu____15406,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15407)) ->
                                true
                            | uu____15412 -> false))
                     in
                  FStar_List.fold_right
                    (fun uu____15444  ->
                       fun uu____15445  ->
                         match uu____15445 with
                         | (g,vs) ->
                             let uu____15490 =
                               FStar_Extraction_ML_UEnv.new_mlident g  in
                             (match uu____15490 with
                              | (g1,v) ->
                                  (g1,
                                    ((v, FStar_Extraction_ML_Syntax.MLTY_Top)
                                    :: vs)))) binders1 (env, [])
              | uu____15536 -> failwith "Discriminator must be a function"
               in
            (match uu____15315 with
             | (g,wildcards) ->
                 let uu____15565 = FStar_Extraction_ML_UEnv.new_mlident g  in
                 (match uu____15565 with
                  | (g1,mlid) ->
                      let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let discrBody =
                        let uu____15578 =
                          let uu____15579 =
                            let uu____15591 =
                              let uu____15592 =
                                let uu____15593 =
                                  let uu____15608 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         targ)
                                      (FStar_Extraction_ML_Syntax.MLE_Name
                                         ([], mlid))
                                     in
                                  let uu____15614 =
                                    let uu____15625 =
                                      let uu____15634 =
                                        let uu____15635 =
                                          let uu____15642 =
                                            FStar_Extraction_ML_UEnv.mlpath_of_lident
                                              g1 constrName
                                             in
                                          (uu____15642,
                                            [FStar_Extraction_ML_Syntax.MLP_Wild])
                                           in
                                        FStar_Extraction_ML_Syntax.MLP_CTor
                                          uu____15635
                                         in
                                      let uu____15645 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_bool_ty)
                                          (FStar_Extraction_ML_Syntax.MLE_Const
                                             (FStar_Extraction_ML_Syntax.MLC_Bool
                                                true))
                                         in
                                      (uu____15634,
                                        FStar_Pervasives_Native.None,
                                        uu____15645)
                                       in
                                    let uu____15649 =
                                      let uu____15660 =
                                        let uu____15669 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.ml_bool_ty)
                                            (FStar_Extraction_ML_Syntax.MLE_Const
                                               (FStar_Extraction_ML_Syntax.MLC_Bool
                                                  false))
                                           in
                                        (FStar_Extraction_ML_Syntax.MLP_Wild,
                                          FStar_Pervasives_Native.None,
                                          uu____15669)
                                         in
                                      [uu____15660]  in
                                    uu____15625 :: uu____15649  in
                                  (uu____15608, uu____15614)  in
                                FStar_Extraction_ML_Syntax.MLE_Match
                                  uu____15593
                                 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                uu____15592
                               in
                            ((FStar_List.append wildcards [(mlid, targ)]),
                              uu____15591)
                             in
                          FStar_Extraction_ML_Syntax.MLE_Fun uu____15579  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty disc_ty)
                          uu____15578
                         in
                      let uu____15730 =
                        let uu____15731 =
                          let uu____15734 =
                            let uu____15735 =
                              FStar_Extraction_ML_UEnv.convIdent
                                discName.FStar_Ident.ident
                               in
                            {
                              FStar_Extraction_ML_Syntax.mllb_name =
                                uu____15735;
                              FStar_Extraction_ML_Syntax.mllb_tysc =
                                FStar_Pervasives_Native.None;
                              FStar_Extraction_ML_Syntax.mllb_add_unit =
                                false;
                              FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                              FStar_Extraction_ML_Syntax.mllb_meta = [];
                              FStar_Extraction_ML_Syntax.print_typ = false
                            }  in
                          [uu____15734]  in
                        (FStar_Extraction_ML_Syntax.NonRec, uu____15731)  in
                      FStar_Extraction_ML_Syntax.MLM_Let uu____15730))
  