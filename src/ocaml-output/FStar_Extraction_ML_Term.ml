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
  
let record_fields :
  'Auu____77 .
    FStar_Ident.ident Prims.list ->
      'Auu____77 Prims.list -> (Prims.string * 'Auu____77) Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2
        (fun f  ->
           fun e  ->
             let uu____113 =
               FStar_Extraction_ML_Syntax.avoid_keyword f.FStar_Ident.idText
                in
             (uu____113, e)) fs vs
  
let fail :
  'Auu____123 .
    FStar_Range.range ->
      (FStar_Errors.raw_error * Prims.string) -> 'Auu____123
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_ill_typed_application :
  'Auu____159 'Auu____160 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'Auu____159) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'Auu____160
  =
  fun env  ->
    fun t  ->
      fun mlhead  ->
        fun args  ->
          fun ty  ->
            let uu____198 =
              let uu____204 =
                let uu____206 = FStar_Syntax_Print.term_to_string t  in
                let uu____208 =
                  let uu____210 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
                  FStar_Extraction_ML_Code.string_of_mlexpr uu____210 mlhead
                   in
                let uu____211 =
                  let uu____213 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
                  FStar_Extraction_ML_Code.string_of_mlty uu____213 ty  in
                let uu____214 =
                  let uu____216 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____237  ->
                            match uu____237 with
                            | (x,uu____244) ->
                                FStar_Syntax_Print.term_to_string x))
                     in
                  FStar_All.pipe_right uu____216 (FStar_String.concat " ")
                   in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____206 uu____208 uu____211 uu____214
                 in
              (FStar_Errors.Fatal_IllTyped, uu____204)  in
            fail t.FStar_Syntax_Syntax.pos uu____198
  
let err_ill_typed_erasure :
  'Auu____261 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____261
  =
  fun env  ->
    fun pos  ->
      fun ty  ->
        let uu____277 =
          let uu____283 =
            let uu____285 =
              let uu____287 =
                FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
              FStar_Extraction_ML_Code.string_of_mlty uu____287 ty  in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____285
             in
          (FStar_Errors.Fatal_IllTyped, uu____283)  in
        fail pos uu____277
  
let err_value_restriction :
  'Auu____295 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____295
  =
  fun t  ->
    let uu____305 =
      let uu____311 =
        let uu____313 = FStar_Syntax_Print.tag_of_term t  in
        let uu____315 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____313 uu____315
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____311)  in
    fail t.FStar_Syntax_Syntax.pos uu____305
  
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
            let uu____349 =
              let uu____355 =
                let uu____357 = FStar_Syntax_Print.term_to_string t  in
                let uu____359 =
                  let uu____361 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env  in
                  FStar_Extraction_ML_Code.string_of_mlty uu____361 ty  in
                let uu____362 = FStar_Extraction_ML_Util.eff_to_string f0  in
                let uu____364 = FStar_Extraction_ML_Util.eff_to_string f1  in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____357 uu____359 uu____362 uu____364
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____355)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____349
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.of_int (20))  in
  let rec delta_norm_eff g l =
    let uu____392 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____392 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____397 =
            let uu____404 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
            FStar_TypeChecker_Env.lookup_effect_abbrev uu____404
              [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____397 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____409,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____419 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____419
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____424 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____424
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              let uu____438 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Env.effect_decl_opt uu____438 l1  in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____451 =
                  let uu____453 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_Env.is_reifiable_effect uu____453
                    ed.FStar_Syntax_Syntax.mname
                   in
                if uu____451
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____476 =
        let uu____477 = FStar_Syntax_Subst.compress t1  in
        uu____477.FStar_Syntax_Syntax.n  in
      match uu____476 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____483 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____508 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____537 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____547 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____547
      | FStar_Syntax_Syntax.Tm_uvar uu____548 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____562 -> false
      | FStar_Syntax_Syntax.Tm_name uu____564 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____566 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____574 -> false
      | FStar_Syntax_Syntax.Tm_type uu____576 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____578,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let topt =
            let uu____608 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] uu____608
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match topt with
           | FStar_Pervasives_Native.None  -> false
           | FStar_Pervasives_Native.Some (uu____615,t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____621 ->
          let uu____638 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____638 with | (head1,uu____657) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____683) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____689) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____694,body,uu____696) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____721,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____741,branches) ->
          (match branches with
           | (uu____780,uu____781,e)::uu____783 -> is_arity env e
           | uu____830 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____862 ->
          let uu____885 =
            let uu____887 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____887  in
          failwith uu____885
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____891 =
            let uu____893 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____893  in
          failwith uu____891
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____898 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____898
      | FStar_Syntax_Syntax.Tm_constant uu____899 -> false
      | FStar_Syntax_Syntax.Tm_type uu____901 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____903 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____911 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____930;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____931;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____932;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____934;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____935;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____936;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____937;_},s)
          ->
          let uu____986 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____986
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____987;
            FStar_Syntax_Syntax.index = uu____988;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____993;
            FStar_Syntax_Syntax.index = uu____994;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1000,uu____1001) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1043) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1050) ->
          let uu____1075 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____1075 with
           | (uu____1081,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____1101 =
            let uu____1106 =
              let uu____1107 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1107]  in
            FStar_Syntax_Subst.open_term uu____1106 body  in
          (match uu____1101 with
           | (uu____1127,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1129,lbs),body) ->
          let uu____1149 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____1149 with
           | (uu____1157,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1163,branches) ->
          (match branches with
           | b::uu____1203 ->
               let uu____1248 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1248 with
                | (uu____1250,uu____1251,e) -> is_type_aux env e)
           | uu____1269 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1287 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1296) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1302) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1343  ->
           let uu____1344 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1346 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1344
             uu____1346);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1355  ->
            if b
            then
              let uu____1357 = FStar_Syntax_Print.term_to_string t  in
              let uu____1359 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1357
                uu____1359
            else
              (let uu____1364 = FStar_Syntax_Print.term_to_string t  in
               let uu____1366 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1364 uu____1366));
       b)
  
let is_type_binder :
  'Auu____1376 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____1376) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1403 =
      let uu____1404 = FStar_Syntax_Subst.compress t  in
      uu____1404.FStar_Syntax_Syntax.n  in
    match uu____1403 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1408;
          FStar_Syntax_Syntax.fv_delta = uu____1409;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1411;
          FStar_Syntax_Syntax.fv_delta = uu____1412;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1413);_}
        -> true
    | uu____1421 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1430 =
      let uu____1431 = FStar_Syntax_Subst.compress t  in
      uu____1431.FStar_Syntax_Syntax.n  in
    match uu____1430 with
    | FStar_Syntax_Syntax.Tm_constant uu____1435 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1437 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1439 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1441 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1487 = is_constructor head1  in
        if uu____1487
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1509  ->
                  match uu____1509 with
                  | (te,uu____1518) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1527) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1533,uu____1534) ->
        is_fstar_value t1
    | uu____1575 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1585 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1587 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1590 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1592 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1605,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1614,fields) ->
        FStar_Util.for_all
          (fun uu____1644  ->
             match uu____1644 with | (uu____1651,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1656) -> is_ml_value h
    | uu____1661 -> false
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1743 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1745 = FStar_Syntax_Util.is_fun e'  in
          if uu____1745
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : unit -> FStar_Syntax_Syntax.binder) =
  fun uu____1763  ->
    let uu____1764 =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.t_unit
       in
    FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1764
  
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
      (let uu____1855 = FStar_List.hd l  in
       match uu____1855 with
       | (p1,w1,e1) ->
           let uu____1890 =
             let uu____1899 = FStar_List.tl l  in FStar_List.hd uu____1899
              in
           (match uu____1890 with
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
                 | uu____1983 -> def)))
  
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
      let uu____2048 =
        FStar_List.fold_right
          (fun t  ->
             fun uu____2079  ->
               match uu____2079 with
               | (uenv,vs) ->
                   let uu____2118 = FStar_Extraction_ML_UEnv.new_mlident uenv
                      in
                   (match uu____2118 with
                    | (uenv1,v1) -> (uenv1, ((v1, t) :: vs)))) ts (g, [])
         in
      match uu____2048 with | (g1,vs_ts) -> (vs_ts, g1)
  
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
          let uu____2235 = s  in
          match uu____2235 with
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
                      let uu___376_2267 = e  in
                      {
                        FStar_Extraction_ML_Syntax.expr =
                          (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                        FStar_Extraction_ML_Syntax.mlty = ts;
                        FStar_Extraction_ML_Syntax.loc =
                          (uu___376_2267.FStar_Extraction_ML_Syntax.loc)
                      }  in
                    (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
              else
                if n_args < n_vars
                then
                  (let extra_tyargs =
                     let uu____2282 = FStar_Util.first_N n_args vars  in
                     match uu____2282 with
                     | (uu____2296,rest_vars) ->
                         FStar_All.pipe_right rest_vars
                           (FStar_List.map
                              (fun uu____2317  ->
                                 FStar_Extraction_ML_Syntax.MLTY_Erased))
                      in
                   let tyargs1 = FStar_List.append tyargs extra_tyargs  in
                   let ts = instantiate_tyscheme (vars, t) tyargs1  in
                   let tapp =
                     let uu___387_2324 = e  in
                     {
                       FStar_Extraction_ML_Syntax.expr =
                         (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                       FStar_Extraction_ML_Syntax.mlty = ts;
                       FStar_Extraction_ML_Syntax.loc =
                         (uu___387_2324.FStar_Extraction_ML_Syntax.loc)
                     }  in
                   let t1 =
                     FStar_List.fold_left
                       (fun out  ->
                          fun t1  ->
                            FStar_Extraction_ML_Syntax.MLTY_Fun
                              (t1, FStar_Extraction_ML_Syntax.E_PURE, out))
                       ts extra_tyargs
                      in
                   let uu____2332 = fresh_mlidents extra_tyargs g  in
                   match uu____2332 with
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
        let uu____2399 = FStar_Extraction_ML_Util.doms_and_cod t  in
        match uu____2399 with
        | (ts,r) ->
            if ts = []
            then e
            else
              (let uu____2417 = fresh_mlidents ts g  in
               match uu____2417 with
               | (vs_ts,g1) ->
                   let vs_es =
                     FStar_List.map
                       (fun uu____2456  ->
                          match uu____2456 with
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
      let uu____2487 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2487 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____2507 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____2507 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2511 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let uu____2517 = fresh_mlidents ts g  in
             match uu____2517 with
             | (vs_ts,g1) ->
                 let uu____2545 =
                   let uu____2546 =
                     let uu____2558 = body r  in (vs_ts, uu____2558)  in
                   FStar_Extraction_ML_Syntax.MLE_Fun uu____2546  in
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
                   uu____2545)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g  ->
    fun expect  ->
      fun e  ->
        let uu____2582 =
          (FStar_Options.ml_no_eta_expand_coertions ()) ||
            (let uu____2585 = FStar_Options.codegen ()  in
             uu____2585 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
           in
        if uu____2582 then e else eta_expand g expect e
  
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
            | uu____2663 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____2718 =
              match uu____2718 with
              | (pat,w,b) ->
                  let uu____2742 = aux b ty1 expect1  in (pat, w, uu____2742)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____2749,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____2752,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____2784 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____2800 = type_leq g s0 t0  in
                if uu____2800
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____2806 =
                       let uu____2807 =
                         let uu____2808 =
                           let uu____2815 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____2815, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____2808  in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____2807  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____2806;
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
               (lbs,body),uu____2834,uu____2835) ->
                let uu____2848 =
                  let uu____2849 =
                    let uu____2860 = aux body ty1 expect1  in
                    (lbs, uu____2860)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____2849  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2848
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____2869,uu____2870) ->
                let uu____2891 =
                  let uu____2892 =
                    let uu____2907 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2907)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____2892  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2891
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____2947,uu____2948) ->
                let uu____2953 =
                  let uu____2954 =
                    let uu____2963 = aux b1 ty1 expect1  in
                    let uu____2964 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____2963, uu____2964)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____2954  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2953
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____2972,uu____2973)
                ->
                let uu____2976 = FStar_Util.prefix es  in
                (match uu____2976 with
                 | (prefix1,last1) ->
                     let uu____2989 =
                       let uu____2990 =
                         let uu____2993 =
                           let uu____2996 = aux last1 ty1 expect1  in
                           [uu____2996]  in
                         FStar_List.append prefix1 uu____2993  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____2990  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____2989)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____2999,uu____3000) ->
                let uu____3021 =
                  let uu____3022 =
                    let uu____3037 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____3037)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____3022  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____3021
            | uu____3074 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'Auu____3094 .
    'Auu____3094 ->
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
            let uu____3121 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____3121 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____3134 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____3142 ->
                     let uu____3143 =
                       let uu____3145 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____3146 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____3145 uu____3146  in
                     if uu____3143
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3152  ->
                             let uu____3153 =
                               let uu____3155 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3155 e
                                in
                             let uu____3156 =
                               let uu____3158 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3158 ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____3153 uu____3156);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3167  ->
                             let uu____3168 =
                               let uu____3170 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3170 e
                                in
                             let uu____3171 =
                               let uu____3173 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3173 ty1
                                in
                             let uu____3174 =
                               let uu____3176 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3176 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____3168 uu____3171 uu____3174);
                        (let uu____3178 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand g expect uu____3178)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____3190 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____3190 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____3192 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
  fun uu____3206  ->
    let uu____3207 = FStar_Options.use_nbe_for_extraction ()  in
    if uu____3207
    then extraction_norm_steps_nbe
    else extraction_norm_steps_core
  
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____3228 -> c
    | FStar_Syntax_Syntax.GTotal uu____3237 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____3273  ->
               match uu____3273 with
               | (uu____3288,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___554_3301 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___554_3301.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___554_3301.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___554_3301.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___554_3301.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___557_3305 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___557_3305.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___557_3305.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let maybe_reify_comp :
  'Auu____3317 .
    'Auu____3317 ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun g  ->
    fun env  ->
      fun c  ->
        let c1 = comp_no_args c  in
        let uu____3336 =
          let uu____3338 =
            let uu____3339 =
              FStar_All.pipe_right c1 FStar_Syntax_Util.comp_effect_name  in
            FStar_All.pipe_right uu____3339
              (FStar_TypeChecker_Env.norm_eff_name env)
             in
          FStar_All.pipe_right uu____3338
            (FStar_TypeChecker_Env.is_reifiable_effect env)
           in
        if uu____3336
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
      let arg_as_mlty g1 uu____3392 =
        match uu____3392 with
        | (a,uu____3400) ->
            let uu____3405 = is_type g1 a  in
            if uu____3405
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____3426 =
          let uu____3428 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____3428  in
        if uu____3426
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____3433 =
             let uu____3448 =
               let uu____3457 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
               FStar_TypeChecker_Env.lookup_lid uu____3457
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____3448 with
             | ((uu____3472,fvty),uu____3474) ->
                 let fvty1 =
                   let uu____3480 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1
                      in
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant] uu____3480 fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____3433 with
           | (formals,uu____3482) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3535 = FStar_Util.first_N n_args formals  in
                   match uu____3535 with
                   | (uu____3564,rest) ->
                       let uu____3598 =
                         FStar_List.map
                           (fun uu____3608  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____3598
                 else mlargs  in
               let nm =
                 let uu____3618 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____3618 with
                 | FStar_Pervasives_Native.Some p -> p
                 | FStar_Pervasives_Native.None  ->
                     FStar_Extraction_ML_Syntax.mlpath_of_lident
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm))
         in
      let aux env t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_type uu____3636 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3637 ->
            let uu____3638 =
              let uu____3640 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3640
               in
            failwith uu____3638
        | FStar_Syntax_Syntax.Tm_delayed uu____3643 ->
            let uu____3666 =
              let uu____3668 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3668
               in
            failwith uu____3666
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3671 =
              let uu____3673 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3673
               in
            failwith uu____3671
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3677 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____3677
        | FStar_Syntax_Syntax.Tm_constant uu____3678 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____3679 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____3686 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____3700) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3705;
               FStar_Syntax_Syntax.index = uu____3706;
               FStar_Syntax_Syntax.sort = t2;_},uu____3708)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3717) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3723,uu____3724) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____3797 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____3797 with
             | (bs1,c1) ->
                 let uu____3804 = binders_as_ml_binders env bs1  in
                 (match uu____3804 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let uu____3833 =
                          let uu____3834 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv env1  in
                          maybe_reify_comp env1 uu____3834 c1  in
                        translate_term_to_mlty env1 uu____3833  in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____3836 =
                        FStar_List.fold_right
                          (fun uu____3856  ->
                             fun uu____3857  ->
                               match (uu____3856, uu____3857) with
                               | ((uu____3880,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____3836 with | (uu____3895,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____3924 =
                let uu____3925 = FStar_Syntax_Util.un_uinst head1  in
                uu____3925.FStar_Syntax_Syntax.n  in
              match uu____3924 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____3956 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____3956
              | uu____3977 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____3980) ->
            let uu____4005 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____4005 with
             | (bs1,ty1) ->
                 let uu____4012 = binders_as_ml_binders env bs1  in
                 (match uu____4012 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____4040 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____4054 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____4086 ->
            let uu____4093 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____4093 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____4099 -> false  in
      let uu____4101 =
        let uu____4103 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Util.must_erase_for_extraction uu____4103 t0  in
      if uu____4101
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____4108 = is_top_ty mlt  in
         if uu____4108 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____4126 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____4182  ->
                fun b  ->
                  match uu____4182 with
                  | (ml_bs,env) ->
                      let uu____4228 = is_type_binder g b  in
                      if uu____4228
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____4254 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____4254, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____4275 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____4275 with
                         | (env1,b2,uu____4300) ->
                             let ml_b =
                               let uu____4309 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____4309, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____4126 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        let uu____4387 = extraction_norm_steps ()  in
        let uu____4388 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Normalize.normalize uu____4387 uu____4388 t0  in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____4407) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4410,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4414 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____4448 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4449 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4450 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4459 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____4487 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____4487 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____4494 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____4527 -> p))
      | uu____4530 -> p
  
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
                       (fun uu____4632  ->
                          let uu____4633 =
                            let uu____4635 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4635 t'
                             in
                          let uu____4636 =
                            let uu____4638 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4638 t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4633 uu____4636)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____4673 = FStar_Options.codegen ()  in
                uu____4673 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4678 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4691 =
                        let uu____4692 =
                          let uu____4693 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4693  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4692
                         in
                      (uu____4691, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        let uu____4715 =
                          let uu____4716 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                          uu____4716.FStar_TypeChecker_Env.dsenv  in
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          uu____4715 c sw FStar_Range.dummyRange
                         in
                      let uu____4717 = term_as_mlexpr g source_term  in
                      (match uu____4717 with
                       | (mlterm,uu____4729,mlty) -> (mlterm, mlty))
                   in
                (match uu____4678 with
                 | (mlc,ml_ty) ->
                     let uu____4748 = FStar_Extraction_ML_UEnv.new_mlident g
                        in
                     (match uu____4748 with
                      | (g1,x) ->
                          let when_clause =
                            let uu____4774 =
                              let uu____4775 =
                                let uu____4782 =
                                  let uu____4785 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         ml_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Var x)
                                     in
                                  [uu____4785; mlc]  in
                                (FStar_Extraction_ML_Util.prims_op_equality,
                                  uu____4782)
                                 in
                              FStar_Extraction_ML_Syntax.MLE_App uu____4775
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_bool_ty)
                              uu____4774
                             in
                          let uu____4788 = ok ml_ty  in
                          (g1,
                            (FStar_Pervasives_Native.Some
                               ((FStar_Extraction_ML_Syntax.MLP_Var x),
                                 [when_clause])), uu____4788)))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  let uu____4809 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_TcTerm.tc_constant uu____4809
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____4811 =
                  let uu____4820 =
                    let uu____4827 =
                      let uu____4828 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4828  in
                    (uu____4827, [])  in
                  FStar_Pervasives_Native.Some uu____4820  in
                let uu____4837 = ok mlty  in (g, uu____4811, uu____4837)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4850 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4850 with
                 | (g1,x1,uu____4878) ->
                     let uu____4881 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4881))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4919 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4919 with
                 | (g1,x1,uu____4947) ->
                     let uu____4950 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4950))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4986 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____5029 =
                  let uu____5038 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____5038 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____5047;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____5049;
                          FStar_Extraction_ML_Syntax.loc = uu____5050;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____5052;_}
                      -> (n1, ttys)
                  | uu____5059 -> failwith "Expected a constructor"  in
                (match uu____5029 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____5096 = FStar_Util.first_N nTyVars pats  in
                     (match uu____5096 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___847_5200  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____5231  ->
                                               match uu____5231 with
                                               | (p1,uu____5238) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5241,t) ->
                                                        term_as_mlty g t
                                                    | uu____5247 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5251 
                                                              ->
                                                              let uu____5252
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5252);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____5256 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____5256)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____5285 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____5322  ->
                                   match uu____5322 with
                                   | (p1,imp1) ->
                                       let uu____5344 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____5344 with
                                        | (g2,p2,uu____5375) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____5285 with
                           | (g1,tyMLPats) ->
                               let uu____5439 =
                                 FStar_Util.fold_map
                                   (fun uu____5504  ->
                                      fun uu____5505  ->
                                        match (uu____5504, uu____5505) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____5603 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____5663 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____5603 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____5734 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____5734 with
                                                  | (g3,p2,uu____5777) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____5439 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____5898 =
                                      let uu____5909 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5960  ->
                                                match uu___0_5960 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____6002 -> []))
                                         in
                                      FStar_All.pipe_right uu____5909
                                        FStar_List.split
                                       in
                                    (match uu____5898 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____6078 -> false  in
                                         let uu____6088 =
                                           let uu____6097 =
                                             let uu____6104 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____6107 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____6104, uu____6107)  in
                                           FStar_Pervasives_Native.Some
                                             uu____6097
                                            in
                                         (g2, uu____6088, pat_ty_compat))))))
  
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
            let uu____6239 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____6239 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____6302 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____6350 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____6350
             in
          let uu____6351 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____6351 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____6516,t1) ->
                let uu____6518 = FStar_Extraction_ML_UEnv.new_mlident g1  in
                (match uu____6518 with
                 | (g2,x) ->
                     let uu____6543 =
                       let uu____6555 =
                         let uu____6565 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty t0)
                             (FStar_Extraction_ML_Syntax.MLE_Var x)
                            in
                         ((x, t0), uu____6565)  in
                       uu____6555 :: more_args  in
                     eta_args g2 uu____6543 t1)
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6581,uu____6582)
                -> ((FStar_List.rev more_args), t)
            | uu____6607 ->
                let uu____6608 =
                  let uu____6610 =
                    let uu____6612 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu____6612
                      mlAppExpr
                     in
                  let uu____6613 =
                    let uu____6615 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlty uu____6615 t  in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6610 uu____6613
                   in
                failwith uu____6608
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____6649,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6686 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____6708 = eta_args g [] residualType  in
            match uu____6708 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____6766 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____6766
                 | uu____6767 ->
                     let uu____6779 = FStar_List.unzip eargs  in
                     (match uu____6779 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____6825 =
                                   let uu____6826 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6826
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6825
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6836 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6840,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6844;
                FStar_Extraction_ML_Syntax.loc = uu____6845;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f])
                 in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1  in
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
              let f1 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append constrname.FStar_Ident.ns [f])
                 in
              let fn = FStar_Extraction_ML_Util.mlpath_of_lid f1  in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____6913 ->
                    let uu____6916 =
                      let uu____6923 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6923, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6916
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6927;
                FStar_Extraction_ML_Syntax.loc = uu____6928;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6936 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6936
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6940;
                FStar_Extraction_ML_Syntax.loc = uu____6941;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6943)) ->
              let uu____6956 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6956
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6960;
                     FStar_Extraction_ML_Syntax.loc = uu____6961;_},uu____6962);
                FStar_Extraction_ML_Syntax.mlty = uu____6963;
                FStar_Extraction_ML_Syntax.loc = uu____6964;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6976 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6976
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6980;
                     FStar_Extraction_ML_Syntax.loc = uu____6981;_},uu____6982);
                FStar_Extraction_ML_Syntax.mlty = uu____6983;
                FStar_Extraction_ML_Syntax.loc = uu____6984;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6986)) ->
              let uu____7003 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7003
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____7009 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7009
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7013)) ->
              let uu____7022 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7022
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7026;
                FStar_Extraction_ML_Syntax.loc = uu____7027;_},uu____7028),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____7035 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7035
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7039;
                FStar_Extraction_ML_Syntax.loc = uu____7040;_},uu____7041),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7042)) ->
              let uu____7055 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7055
          | uu____7058 -> mlAppExpr
  
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
        | uu____7089 -> (ml_e, tag)
  
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
      let maybe_generalize uu____7150 =
        match uu____7150 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____7171;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____7176;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____7257 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____7334 =
              let uu____7336 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Util.must_erase_for_extraction uu____7336
                lbtyp1
               in
            if uu____7334
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____7421 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____7421 (is_type_binder g) ->
                   let uu____7443 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____7443 with
                    | (bs1,c1) ->
                        let uu____7469 =
                          let uu____7482 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____7528 = is_type_binder g x  in
                                 Prims.op_Negation uu____7528) bs1
                             in
                          match uu____7482 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____7655 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____7655)
                           in
                        (match uu____7469 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____7717 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____7717
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____7766 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____7766 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7818 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____7818 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7921  ->
                                                       fun uu____7922  ->
                                                         match (uu____7921,
                                                                 uu____7922)
                                                         with
                                                         | ((x,uu____7948),
                                                            (y,uu____7950))
                                                             ->
                                                             let uu____7971 =
                                                               let uu____7978
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____7978)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7971)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____7995  ->
                                                       match uu____7995 with
                                                       | (a,uu____8003) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a
                                                             FStar_Pervasives_Native.None)
                                                  g targs
                                                 in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty
                                                 in
                                              let polytype =
                                                let uu____8014 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____8033  ->
                                                          match uu____8033
                                                          with
                                                          | (x,uu____8042) ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____8014, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____8058 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____8058)
                                                      ||
                                                      (let uu____8061 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____8061)
                                                | uu____8063 -> false  in
                                              let rest_args1 =
                                                if add_unit
                                                then
                                                  let uu____8075 =
                                                    unit_binder ()  in
                                                  uu____8075 :: rest_args
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____8132 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8151  ->
                                           match uu____8151 with
                                           | (a,uu____8159) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8170 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8189  ->
                                              match uu____8189 with
                                              | (x,uu____8198) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____8170, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8242  ->
                                            match uu____8242 with
                                            | (bv,uu____8250) ->
                                                let uu____8255 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8255
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____8285 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8298  ->
                                           match uu____8298 with
                                           | (a,uu____8306) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8317 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8336  ->
                                              match uu____8336 with
                                              | (x,uu____8345) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____8317, expected_t)  in
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
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8464 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8483  ->
                                              match uu____8483 with
                                              | (x,uu____8492) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____8464, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8536  ->
                                            match uu____8536 with
                                            | (bv,uu____8544) ->
                                                let uu____8549 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8549
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
                              | uu____8579 -> err_value_restriction lbdef1)))
               | uu____8599 -> no_gen ())
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
           fun uu____8750  ->
             match uu____8750 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____8811 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____8811 with
                  | (env1,uu____8828,exp_binding) ->
                      let uu____8832 =
                        let uu____8837 = FStar_Util.right lbname  in
                        (uu____8837, exp_binding)  in
                      (env1, uu____8832))) g lbs1
  
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
            (fun uu____8903  ->
               let uu____8904 = FStar_Syntax_Print.term_to_string e  in
               let uu____8906 =
                 let uu____8908 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g  in
                 FStar_Extraction_ML_Code.string_of_mlty uu____8908 ty  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____8904
                 uu____8906);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____8914) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8915 ->
               let uu____8920 = term_as_mlexpr g e  in
               (match uu____8920 with
                | (ml_e,tag,t) ->
                    let uu____8934 = maybe_promote_effect ml_e tag t  in
                    (match uu____8934 with
                     | (ml_e1,tag1) ->
                         let uu____8945 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____8945
                         then
                           let uu____8952 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____8952, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____8959 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____8959, ty)
                            | uu____8960 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____8968 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____8968, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____8971 = term_as_mlexpr' g e  in
      match uu____8971 with
      | (e1,f,t) ->
          let uu____8987 = maybe_promote_effect e1 f t  in
          (match uu____8987 with | (e2,f1) -> (e2, f1, t))

and (term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun top  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____9012 =
             let uu____9014 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____9016 = FStar_Syntax_Print.tag_of_term top  in
             let uu____9018 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____9014 uu____9016 uu____9018
              in
           FStar_Util.print_string uu____9012);
      (let is_match t =
         let uu____9028 =
           let uu____9029 =
             let uu____9032 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9032 FStar_Syntax_Util.unascribe  in
           uu____9029.FStar_Syntax_Syntax.n  in
         match uu____9028 with
         | FStar_Syntax_Syntax.Tm_match uu____9036 -> true
         | uu____9060 -> false  in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____9079  ->
              match uu____9079 with
              | (t,uu____9088) ->
                  let uu____9093 =
                    let uu____9094 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
                    uu____9094.FStar_Syntax_Syntax.n  in
                  (match uu____9093 with
                   | FStar_Syntax_Syntax.Tm_name uu____9100 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____9102 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____9104 -> true
                   | uu____9106 -> false))
          in
       let apply_to_match_branches head1 args =
         let uu____9145 =
           let uu____9146 =
             let uu____9149 =
               FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9149 FStar_Syntax_Util.unascribe  in
           uu____9146.FStar_Syntax_Syntax.n  in
         match uu____9145 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee,branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____9273  ->
                       match uu____9273 with
                       | (pat,when_opt,body) ->
                           (pat, when_opt,
                             (let uu___1317_9330 = body  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1317_9330.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1317_9330.FStar_Syntax_Syntax.vars)
                              }))))
                in
             let uu___1320_9345 = head1  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1320_9345.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1320_9345.FStar_Syntax_Syntax.vars)
             }
         | uu____9366 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match"
          in
       let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9377 =
             let uu____9379 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9379
              in
           failwith uu____9377
       | FStar_Syntax_Syntax.Tm_delayed uu____9388 ->
           let uu____9411 =
             let uu____9413 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9413
              in
           failwith uu____9411
       | FStar_Syntax_Syntax.Tm_uvar uu____9422 ->
           let uu____9435 =
             let uu____9437 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9437
              in
           failwith uu____9435
       | FStar_Syntax_Syntax.Tm_bvar uu____9446 ->
           let uu____9447 =
             let uu____9449 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9449
              in
           failwith uu____9447
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9459 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____9459
       | FStar_Syntax_Syntax.Tm_type uu____9460 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9461 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9468 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____9484;_})
           ->
           let uu____9497 =
             let uu____9498 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9498  in
           (match uu____9497 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9505;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9507;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9508;_} ->
                let uu____9511 =
                  let uu____9512 =
                    let uu____9513 =
                      let uu____9520 =
                        let uu____9523 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____9523]  in
                      (fw, uu____9520)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9513  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9512
                   in
                (uu____9511, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9541 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____9541 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9549 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____9549 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____9560 =
                         let uu____9567 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____9567
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____9560 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____9575 =
                         let uu____9586 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____9586]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9575
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9613 =
                    let uu____9620 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____9620 tv  in
                  uu____9613 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____9628 =
                    let uu____9639 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____9639]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9628
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____9666)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9699 =
                  let uu____9706 =
                    let uu____9715 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.effect_decl_opt uu____9715 m  in
                  FStar_Util.must uu____9706  in
                (match uu____9699 with
                 | (ed,qualifiers) ->
                     let uu____9734 =
                       let uu____9736 =
                         let uu____9738 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                         FStar_TypeChecker_Env.is_reifiable_effect uu____9738
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____9736  in
                     if uu____9734
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9755 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9757) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9763) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9769 =
             let uu____9776 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_TcTerm.type_of_tot_term uu____9776 t  in
           (match uu____9769 with
            | (uu____9783,ty,uu____9785) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____9787 =
                  let uu____9788 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9788  in
                (uu____9787, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9789 ->
           let uu____9790 = is_type g t  in
           if uu____9790
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9801 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____9801 with
              | (FStar_Util.Inl uu____9814,uu____9815) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9820;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9823;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____9841 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____9841, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9842 -> instantiate_maybe_partial g x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9844 = is_type g t  in
           if uu____9844
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9855 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____9855 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9864;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9867;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9875  ->
                        let uu____9876 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____9878 =
                          let uu____9880 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            uu____9880 x
                           in
                        let uu____9881 =
                          let uu____9883 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlty uu____9883
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9876 uu____9878 uu____9881);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____9895 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____9895, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9896 -> instantiate_maybe_partial g x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____9924 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____9924 with
            | (bs1,body1) ->
                let uu____9937 = binders_as_ml_binders g bs1  in
                (match uu____9937 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9973 =
                             let uu____9975 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Env.is_reifiable_rc uu____9975
                               rc
                              in
                           if uu____9973
                           then
                             let uu____9977 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Util.reify_body uu____9977
                               [FStar_TypeChecker_Env.Inlining] body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9983  ->
                                 let uu____9984 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9984);
                            body1)
                        in
                     let uu____9987 = term_as_mlexpr env body2  in
                     (match uu____9987 with
                      | (ml_body,f,t1) ->
                          let uu____10003 =
                            FStar_List.fold_right
                              (fun uu____10023  ->
                                 fun uu____10024  ->
                                   match (uu____10023, uu____10024) with
                                   | ((uu____10047,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____10003 with
                           | (f1,tfun) ->
                               let uu____10070 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____10070, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____10078;
              FStar_Syntax_Syntax.vars = uu____10079;_},(a1,uu____10081)::[])
           ->
           let ty =
             let uu____10121 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____10121  in
           let uu____10122 =
             let uu____10123 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____10123
              in
           (uu____10122, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____10124;
              FStar_Syntax_Syntax.vars = uu____10125;_},(t1,uu____10127)::
            (r,uu____10129)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____10184);
              FStar_Syntax_Syntax.pos = uu____10185;
              FStar_Syntax_Syntax.vars = uu____10186;_},uu____10187)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (is_match head1) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____10246 =
             FStar_All.pipe_right args (apply_to_match_branches head1)  in
           FStar_All.pipe_right uu____10246 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_10300  ->
                        match uu___1_10300 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____10303 -> false)))
              in
           let uu____10305 =
             let uu____10310 =
               let uu____10311 =
                 let uu____10314 =
                   FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
                 FStar_All.pipe_right uu____10314 FStar_Syntax_Util.unascribe
                  in
               uu____10311.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____10310)  in
           (match uu____10305 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____10323,uu____10324) ->
                let t1 =
                  let uu____10338 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Iota;
                    FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.AllowUnboundUniverses] uu____10338
                    t
                   in
                term_as_mlexpr g t1
            | (uu____10339,FStar_Syntax_Syntax.Tm_abs (bs,uu____10341,_rc))
                ->
                let uu____10367 =
                  let uu____10368 =
                    let uu____10373 =
                      FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses]
                      uu____10373
                     in
                  FStar_All.pipe_right t uu____10368  in
                FStar_All.pipe_right uu____10367 (term_as_mlexpr g)
            | (uu____10380,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____10382 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  let uu____10383 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg uu____10382
                    [FStar_TypeChecker_Env.Inlining] head1 uu____10383
                   in
                let tm =
                  let uu____10395 =
                    let uu____10400 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____10401 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____10400 uu____10401  in
                  uu____10395 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____10410 ->
                let rec extract_app is_data uu____10463 uu____10464 restArgs
                  =
                  match (uu____10463, uu____10464) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____10545 =
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
                         (fun uu____10572  ->
                            let uu____10573 =
                              let uu____10575 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              let uu____10576 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____10575 uu____10576
                               in
                            let uu____10577 =
                              let uu____10579 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlty
                                uu____10579 t1
                               in
                            let uu____10580 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____10591)::uu____10592 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10573 uu____10577 uu____10580);
                       (match (restArgs, t1) with
                        | ([],uu____10626) ->
                            let app =
                              let uu____10642 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10642
                               in
                            (app, f, t1)
                        | ((arg,uu____10644)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10675 =
                              let uu____10680 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____10680, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10675 rest
                        | ((e0,uu____10692)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____10725 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____10725
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____10730 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____10730 with
                             | (e01,tInferred) ->
                                 let uu____10743 =
                                   let uu____10748 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____10748, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10743 rest)
                        | uu____10759 ->
                            let uu____10772 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____10772 with
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
                                          top.FStar_Syntax_Syntax.pos g head2
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t2
                                         in
                                      extract_app is_data (mlhead1, [])
                                        (f, t2) restArgs
                                  | uu____10844 ->
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
                                          top.FStar_Syntax_Syntax.pos g head2
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t1
                                         in
                                      err_ill_typed_application g top mlhead1
                                        restArgs t1))))
                   in
                let extract_app_maybe_projector is_data mlhead uu____10915
                  args1 =
                  match uu____10915 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10945)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____11029))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____11031,f',t3)) ->
                                 let uu____11069 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____11069 t3
                             | uu____11070 -> (args2, f1, t2)  in
                           let uu____11095 = remove_implicits args1 f t1  in
                           (match uu____11095 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____11151 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____11175 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____11183 ->
                      let uu____11184 =
                        let uu____11205 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____11205 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11244  ->
                                  let uu____11245 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____11247 =
                                    let uu____11249 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11249
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11250 =
                                    let uu____11252 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11252
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11253 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11245 uu____11247 uu____11250
                                    uu____11253);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11280 -> failwith "FIXME Ty"  in
                      (match uu____11184 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11356)::uu____11357 -> is_type g a
                             | uu____11384 -> false  in
                           let uu____11396 =
                             match vars with
                             | uu____11425::uu____11426 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11440 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____11446 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____11484 =
                                       FStar_List.map
                                         (fun uu____11496  ->
                                            match uu____11496 with
                                            | (x,uu____11504) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____11484, [])
                                   else
                                     (let uu____11527 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____11527 with
                                      | (prefix1,rest) ->
                                          let uu____11616 =
                                            FStar_List.map
                                              (fun uu____11628  ->
                                                 match uu____11628 with
                                                 | (x,uu____11636) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____11616, rest))
                                    in
                                 (match uu____11446 with
                                  | (provided_type_args,rest) ->
                                      let uu____11687 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____11696 ->
                                            let uu____11697 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11697 with
                                             | (head3,uu____11709,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____11711 ->
                                            let uu____11713 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11713 with
                                             | (head3,uu____11725,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____11728;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____11729;_}::[])
                                            ->
                                            let uu____11732 =
                                              instantiate_maybe_partial g
                                                head3 (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11732 with
                                             | (head4,uu____11744,t2) ->
                                                 let uu____11746 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____11746, t2))
                                        | uu____11749 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____11687 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____11396 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11816 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____11816,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11817 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11826 ->
                      let uu____11827 =
                        let uu____11848 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____11848 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11887  ->
                                  let uu____11888 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____11890 =
                                    let uu____11892 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11892
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11893 =
                                    let uu____11895 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11895
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11896 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11888 uu____11890 uu____11893
                                    uu____11896);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11923 -> failwith "FIXME Ty"  in
                      (match uu____11827 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11999)::uu____12000 -> is_type g a
                             | uu____12027 -> false  in
                           let uu____12039 =
                             match vars with
                             | uu____12068::uu____12069 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____12083 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____12089 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____12127 =
                                       FStar_List.map
                                         (fun uu____12139  ->
                                            match uu____12139 with
                                            | (x,uu____12147) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____12127, [])
                                   else
                                     (let uu____12170 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____12170 with
                                      | (prefix1,rest) ->
                                          let uu____12259 =
                                            FStar_List.map
                                              (fun uu____12271  ->
                                                 match uu____12271 with
                                                 | (x,uu____12279) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____12259, rest))
                                    in
                                 (match uu____12089 with
                                  | (provided_type_args,rest) ->
                                      let uu____12330 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____12339 ->
                                            let uu____12340 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12340 with
                                             | (head3,uu____12352,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____12354 ->
                                            let uu____12356 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12356 with
                                             | (head3,uu____12368,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____12371;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____12372;_}::[])
                                            ->
                                            let uu____12375 =
                                              instantiate_maybe_partial g
                                                head3 (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12375 with
                                             | (head4,uu____12387,t2) ->
                                                 let uu____12389 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____12389, t2))
                                        | uu____12392 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____12330 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____12039 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12459 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____12459,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12460 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12469 ->
                      let uu____12470 = term_as_mlexpr g head2  in
                      (match uu____12470 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____12486 = is_type g t  in
                if uu____12486
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12497 =
                     let uu____12498 = FStar_Syntax_Util.un_uinst head1  in
                     uu____12498.FStar_Syntax_Syntax.n  in
                   match uu____12497 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12508 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____12508 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12517 -> extract_app_with_instantiations ())
                   | uu____12520 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____12523),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12588 =
                   let uu____12589 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                      in
                   maybe_reify_comp g uu____12589 c  in
                 term_as_mlty g uu____12588
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____12593 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____12593 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e') when
           (let uu____12625 = FStar_Syntax_Syntax.is_top_level [lb]  in
            Prims.op_Negation uu____12625) &&
             (let uu____12628 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs
                 in
              FStar_Util.is_some uu____12628)
           ->
           let b =
             let uu____12638 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                in
             (uu____12638, FStar_Pervasives_Native.None)  in
           let uu____12641 = FStar_Syntax_Subst.open_term [b] e'  in
           (match uu____12641 with
            | ((x,uu____12665)::uu____12666,body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str,uu____12695)::[]) ->
                      let uu____12720 =
                        let uu____12721 = FStar_Syntax_Subst.compress str  in
                        uu____12721.FStar_Syntax_Syntax.n  in
                      (match uu____12720 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s,uu____12727)) ->
                           let id1 =
                             let uu____12731 =
                               let uu____12737 =
                                 FStar_Syntax_Syntax.range_of_bv x  in
                               (s, uu____12737)  in
                             FStar_Ident.mk_ident uu____12731  in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id1;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             }  in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv  in
                           FStar_Pervasives_Native.Some bv1
                       | uu____12742 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                   in
                let remove_attr1 attrs =
                  let uu____12759 =
                    FStar_List.partition
                      (fun attr  ->
                         let uu____12771 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr]
                            in
                         FStar_Util.is_some uu____12771)
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match uu____12759 with
                  | (uu____12776,other_attrs) -> other_attrs  in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None  ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1788_12804 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1788_12804.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1788_12804.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1788_12804.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1788_12804.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1788_12804.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1788_12804.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      let rename =
                        let uu____12812 =
                          let uu____12813 =
                            let uu____12820 =
                              FStar_Syntax_Syntax.bv_to_name y  in
                            (x, uu____12820)  in
                          FStar_Syntax_Syntax.NT uu____12813  in
                        [uu____12812]  in
                      let body1 =
                        let uu____12826 =
                          FStar_Syntax_Subst.subst rename body  in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____12826
                         in
                      let lb1 =
                        let uu___1795_12842 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1795_12842.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1795_12842.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1795_12842.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1795_12842.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1795_12842.FStar_Syntax_Syntax.lbpos)
                        }  in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1)
                   in
                let top1 =
                  let uu___1799_12859 = top  in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1799_12859.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1799_12859.FStar_Syntax_Syntax.vars)
                  }  in
                term_as_mlexpr' g top1)
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____12882 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12898 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____12898
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____12913 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____12913  in
                   let lb1 =
                     let uu___1813_12915 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1813_12915.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1813_12915.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1813_12915.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1813_12915.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1813_12915.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1813_12915.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____12882 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____12940 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      let uu____12941 =
                        let uu____12942 =
                          let uu____12943 =
                            let uu____12947 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Pervasives_Native.fst uu____12947  in
                          let uu____12960 =
                            let uu____12964 =
                              let uu____12966 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Pervasives_Native.snd uu____12966  in
                            [uu____12964]  in
                          FStar_List.append uu____12943 uu____12960  in
                        FStar_Ident.lid_of_path uu____12942
                          FStar_Range.dummyRange
                         in
                      FStar_TypeChecker_Env.set_current_module uu____12940
                        uu____12941
                       in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let lbdef =
                              let uu____12993 = FStar_Options.ml_ish ()  in
                              if uu____12993
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____13005 =
                                   let uu____13006 =
                                     let uu____13007 =
                                       extraction_norm_steps ()  in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____13007
                                      in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____13006 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____13010 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____13010
                                 then
                                   ((let uu____13020 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____13020);
                                    (let a =
                                       let uu____13026 =
                                         let uu____13028 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____13028
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____13026 norm_call
                                        in
                                     a))
                                 else norm_call ())
                               in
                            let uu___1830_13035 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1830_13035.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1830_13035.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1830_13035.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1830_13035.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1830_13035.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1830_13035.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____13088 =
                  match uu____13088 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____13244  ->
                               match uu____13244 with
                               | (a,uu____13252) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____13258 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____13258 with
                       | (e1,ty) ->
                           let uu____13269 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____13269 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____13281 -> []  in
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
                let uu____13312 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____13409  ->
                         match uu____13409 with
                         | (env,lbs4) ->
                             let uu____13543 = lb  in
                             (match uu____13543 with
                              | (lbname,uu____13594,(t1,(uu____13596,polytype)),add_unit,uu____13599)
                                  ->
                                  let uu____13614 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____13614 with
                                   | (env1,nm,uu____13655) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____13312 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____13934 = term_as_mlexpr env_body e'1  in
                     (match uu____13934 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____13951 =
                              let uu____13954 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____13954  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13951
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____13967 =
                            let uu____13968 =
                              let uu____13969 =
                                let uu____13970 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____13970)  in
                              mk_MLE_Let top_level uu____13969 e'2  in
                            let uu____13979 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13968 uu____13979
                             in
                          (uu____13967, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____14018 = term_as_mlexpr g scrutinee  in
           (match uu____14018 with
            | (e,f_e,t_e) ->
                let uu____14034 = check_pats_for_ite pats  in
                (match uu____14034 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____14099 = term_as_mlexpr g then_e1  in
                            (match uu____14099 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____14115 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____14115 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____14131 =
                                        let uu____14142 =
                                          type_leq g t_then t_else  in
                                        if uu____14142
                                        then (t_else, no_lift)
                                        else
                                          (let uu____14163 =
                                             type_leq g t_else t_then  in
                                           if uu____14163
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____14131 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____14210 =
                                             let uu____14211 =
                                               let uu____14212 =
                                                 let uu____14221 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____14222 =
                                                   let uu____14225 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____14225
                                                    in
                                                 (e, uu____14221,
                                                   uu____14222)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____14212
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____14211
                                              in
                                           let uu____14228 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____14210, uu____14228,
                                             t_branch))))
                        | uu____14229 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____14247 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____14346 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____14346 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____14391 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____14391 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____14453 =
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
                                                   let uu____14476 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____14476 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____14453 with
                                              | (when_opt1,f_when) ->
                                                  let uu____14526 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____14526 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____14561 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14638 
                                                                 ->
                                                                 match uu____14638
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
                                                         uu____14561)))))
                               true)
                           in
                        match uu____14247 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14809  ->
                                      let uu____14810 =
                                        let uu____14812 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu____14812 e
                                         in
                                      let uu____14813 =
                                        let uu____14815 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu____14815 t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14810 uu____14813);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14841 =
                                   let uu____14842 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14842
                                    in
                                 (match uu____14841 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14849;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14851;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____14852;_}
                                      ->
                                      let uu____14855 =
                                        let uu____14856 =
                                          let uu____14857 =
                                            let uu____14864 =
                                              let uu____14867 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____14867]  in
                                            (fw, uu____14864)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14857
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14856
                                         in
                                      (uu____14855,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14871,uu____14872,(uu____14873,f_first,t_first))::rest
                                 ->
                                 let uu____14933 =
                                   FStar_List.fold_left
                                     (fun uu____14975  ->
                                        fun uu____14976  ->
                                          match (uu____14975, uu____14976)
                                          with
                                          | ((topt,f),(uu____15033,uu____15034,
                                                       (uu____15035,f_branch,t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top.FStar_Syntax_Syntax.pos
                                                  f f_branch
                                                 in
                                              let topt1 =
                                                match topt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    t1 ->
                                                    let uu____15091 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____15091
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____15098 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____15098
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
                                 (match uu____14933 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____15196  ->
                                                match uu____15196 with
                                                | (p,(wopt,uu____15225),
                                                   (b1,uu____15227,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____15246 -> b1
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
                                      let uu____15251 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____15251, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____15278 =
          let uu____15283 =
            let uu____15292 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_lid uu____15292 discName  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15283  in
        match uu____15278 with
        | (uu____15309,fstar_disc_type) ->
            let uu____15311 =
              let uu____15323 =
                let uu____15324 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____15324.FStar_Syntax_Syntax.n  in
              match uu____15323 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15339) ->
                  let binders1 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_15394  ->
                            match uu___2_15394 with
                            | (uu____15402,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15403)) ->
                                true
                            | uu____15408 -> false))
                     in
                  FStar_List.fold_right
                    (fun uu____15440  ->
                       fun uu____15441  ->
                         match uu____15441 with
                         | (g,vs) ->
                             let uu____15486 =
                               FStar_Extraction_ML_UEnv.new_mlident g  in
                             (match uu____15486 with
                              | (g1,v1) ->
                                  (g1,
                                    ((v1,
                                       FStar_Extraction_ML_Syntax.MLTY_Top)
                                    :: vs)))) binders1 (env, [])
              | uu____15532 -> failwith "Discriminator must be a function"
               in
            (match uu____15311 with
             | (g,wildcards) ->
                 let uu____15561 = FStar_Extraction_ML_UEnv.new_mlident g  in
                 (match uu____15561 with
                  | (g1,mlid) ->
                      let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let discrBody =
                        let uu____15574 =
                          let uu____15575 =
                            let uu____15587 =
                              let uu____15588 =
                                let uu____15589 =
                                  let uu____15604 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         targ)
                                      (FStar_Extraction_ML_Syntax.MLE_Name
                                         ([], mlid))
                                     in
                                  let uu____15610 =
                                    let uu____15621 =
                                      let uu____15630 =
                                        let uu____15631 =
                                          let uu____15638 =
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                              constrName
                                             in
                                          (uu____15638,
                                            [FStar_Extraction_ML_Syntax.MLP_Wild])
                                           in
                                        FStar_Extraction_ML_Syntax.MLP_CTor
                                          uu____15631
                                         in
                                      let uu____15641 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_bool_ty)
                                          (FStar_Extraction_ML_Syntax.MLE_Const
                                             (FStar_Extraction_ML_Syntax.MLC_Bool
                                                true))
                                         in
                                      (uu____15630,
                                        FStar_Pervasives_Native.None,
                                        uu____15641)
                                       in
                                    let uu____15645 =
                                      let uu____15656 =
                                        let uu____15665 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.ml_bool_ty)
                                            (FStar_Extraction_ML_Syntax.MLE_Const
                                               (FStar_Extraction_ML_Syntax.MLC_Bool
                                                  false))
                                           in
                                        (FStar_Extraction_ML_Syntax.MLP_Wild,
                                          FStar_Pervasives_Native.None,
                                          uu____15665)
                                         in
                                      [uu____15656]  in
                                    uu____15621 :: uu____15645  in
                                  (uu____15604, uu____15610)  in
                                FStar_Extraction_ML_Syntax.MLE_Match
                                  uu____15589
                                 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                uu____15588
                               in
                            ((FStar_List.append wildcards [(mlid, targ)]),
                              uu____15587)
                             in
                          FStar_Extraction_ML_Syntax.MLE_Fun uu____15575  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty disc_ty)
                          uu____15574
                         in
                      let uu____15726 =
                        let uu____15727 =
                          let uu____15730 =
                            let uu____15731 =
                              FStar_Extraction_ML_UEnv.convIdent
                                discName.FStar_Ident.ident
                               in
                            {
                              FStar_Extraction_ML_Syntax.mllb_name =
                                uu____15731;
                              FStar_Extraction_ML_Syntax.mllb_tysc =
                                FStar_Pervasives_Native.None;
                              FStar_Extraction_ML_Syntax.mllb_add_unit =
                                false;
                              FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                              FStar_Extraction_ML_Syntax.mllb_meta = [];
                              FStar_Extraction_ML_Syntax.print_typ = false
                            }  in
                          [uu____15730]  in
                        (FStar_Extraction_ML_Syntax.NonRec, uu____15727)  in
                      FStar_Extraction_ML_Syntax.MLM_Let uu____15726))
  