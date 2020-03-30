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
             let uu____3440 =
               let uu____3449 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
               FStar_TypeChecker_Env.lookup_lid uu____3449
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____3440 with
             | ((uu____3456,fvty),uu____3458) ->
                 let fvty1 =
                   let uu____3464 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1
                      in
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant] uu____3464 fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____3433 with
           | (formals,uu____3466) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3503 = FStar_Util.first_N n_args formals  in
                   match uu____3503 with
                   | (uu____3532,rest) ->
                       let uu____3566 =
                         FStar_List.map
                           (fun uu____3576  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____3566
                 else mlargs  in
               let nm =
                 let uu____3586 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____3586 with
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
        | FStar_Syntax_Syntax.Tm_type uu____3604 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3605 ->
            let uu____3606 =
              let uu____3608 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3608
               in
            failwith uu____3606
        | FStar_Syntax_Syntax.Tm_delayed uu____3611 ->
            let uu____3634 =
              let uu____3636 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3636
               in
            failwith uu____3634
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3639 =
              let uu____3641 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3641
               in
            failwith uu____3639
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3645 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____3645
        | FStar_Syntax_Syntax.Tm_constant uu____3646 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____3647 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____3654 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____3668) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3673;
               FStar_Syntax_Syntax.index = uu____3674;
               FStar_Syntax_Syntax.sort = t2;_},uu____3676)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3685) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3691,uu____3692) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____3765 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____3765 with
             | (bs1,c1) ->
                 let uu____3772 = binders_as_ml_binders env bs1  in
                 (match uu____3772 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let uu____3801 =
                          let uu____3802 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv env1  in
                          maybe_reify_comp env1 uu____3802 c1  in
                        translate_term_to_mlty env1 uu____3801  in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____3804 =
                        FStar_List.fold_right
                          (fun uu____3824  ->
                             fun uu____3825  ->
                               match (uu____3824, uu____3825) with
                               | ((uu____3848,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____3804 with | (uu____3863,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____3892 =
                let uu____3893 = FStar_Syntax_Util.un_uinst head1  in
                uu____3893.FStar_Syntax_Syntax.n  in
              match uu____3892 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____3924 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____3924
              | uu____3945 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____3948) ->
            let uu____3973 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____3973 with
             | (bs1,ty1) ->
                 let uu____3980 = binders_as_ml_binders env bs1  in
                 (match uu____3980 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____4008 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____4022 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____4054 ->
            let uu____4061 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____4061 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____4067 -> false  in
      let uu____4069 =
        let uu____4071 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Util.must_erase_for_extraction uu____4071 t0  in
      if uu____4069
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____4076 = is_top_ty mlt  in
         if uu____4076 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____4094 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____4151  ->
                fun b  ->
                  match uu____4151 with
                  | (ml_bs,env) ->
                      let uu____4197 = is_type_binder g b  in
                      if uu____4197
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1 true  in
                        let ml_b =
                          let uu____4220 =
                            FStar_Extraction_ML_UEnv.lookup_ty env1 b1  in
                          uu____4220.FStar_Extraction_ML_UEnv.ty_b_name  in
                        let ml_b1 =
                          (ml_b, FStar_Extraction_ML_Syntax.ml_unit_ty)  in
                        ((ml_b1 :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____4246 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____4246 with
                         | (env1,b2,uu____4271) ->
                             let ml_b = (b2, t)  in ((ml_b :: ml_bs), env1)))
             ([], g))
         in
      match uu____4094 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        let uu____4356 = extraction_norm_steps ()  in
        let uu____4357 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Normalize.normalize uu____4356 uu____4357 t0  in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____4376) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4379,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4383 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____4417 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4418 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4419 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4428 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____4456 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____4456 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____4463 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____4496 -> p))
      | uu____4499 -> p
  
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
                       (fun uu____4601  ->
                          let uu____4602 =
                            let uu____4604 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4604 t'
                             in
                          let uu____4605 =
                            let uu____4607 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4607 t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4602 uu____4605)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____4642 = FStar_Options.codegen ()  in
                uu____4642 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4647 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4660 =
                        let uu____4661 =
                          let uu____4662 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4662  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4661
                         in
                      (uu____4660, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        let uu____4684 =
                          let uu____4685 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                          uu____4685.FStar_TypeChecker_Env.dsenv  in
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          uu____4684 c sw FStar_Range.dummyRange
                         in
                      let uu____4686 = term_as_mlexpr g source_term  in
                      (match uu____4686 with
                       | (mlterm,uu____4698,mlty) -> (mlterm, mlty))
                   in
                (match uu____4647 with
                 | (mlc,ml_ty) ->
                     let uu____4717 = FStar_Extraction_ML_UEnv.new_mlident g
                        in
                     (match uu____4717 with
                      | (g1,x) ->
                          let when_clause =
                            let uu____4743 =
                              let uu____4744 =
                                let uu____4751 =
                                  let uu____4754 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         ml_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Var x)
                                     in
                                  [uu____4754; mlc]  in
                                (FStar_Extraction_ML_Util.prims_op_equality,
                                  uu____4751)
                                 in
                              FStar_Extraction_ML_Syntax.MLE_App uu____4744
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_bool_ty)
                              uu____4743
                             in
                          let uu____4757 = ok ml_ty  in
                          (g1,
                            (FStar_Pervasives_Native.Some
                               ((FStar_Extraction_ML_Syntax.MLP_Var x),
                                 [when_clause])), uu____4757)))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  let uu____4778 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_TcTerm.tc_constant uu____4778
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____4780 =
                  let uu____4789 =
                    let uu____4796 =
                      let uu____4797 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4797  in
                    (uu____4796, [])  in
                  FStar_Pervasives_Native.Some uu____4789  in
                let uu____4806 = ok mlty  in (g, uu____4780, uu____4806)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4819 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4819 with
                 | (g1,x1,uu____4847) ->
                     let uu____4850 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4850))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4888 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4888 with
                 | (g1,x1,uu____4916) ->
                     let uu____4919 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4919))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4955 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____4998 =
                  let uu____5007 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____5007 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____5016;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____5018;
                          FStar_Extraction_ML_Syntax.loc = uu____5019;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____5021;_}
                      -> (n1, ttys)
                  | uu____5028 -> failwith "Expected a constructor"  in
                (match uu____4998 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____5065 = FStar_Util.first_N nTyVars pats  in
                     (match uu____5065 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___848_5169  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____5200  ->
                                               match uu____5200 with
                                               | (p1,uu____5207) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5210,t) ->
                                                        term_as_mlty g t
                                                    | uu____5216 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5220 
                                                              ->
                                                              let uu____5221
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5221);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____5225 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____5225)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____5254 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____5291  ->
                                   match uu____5291 with
                                   | (p1,imp1) ->
                                       let uu____5313 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____5313 with
                                        | (g2,p2,uu____5344) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____5254 with
                           | (g1,tyMLPats) ->
                               let uu____5408 =
                                 FStar_Util.fold_map
                                   (fun uu____5473  ->
                                      fun uu____5474  ->
                                        match (uu____5473, uu____5474) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____5572 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____5632 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____5572 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____5703 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____5703 with
                                                  | (g3,p2,uu____5746) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____5408 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____5867 =
                                      let uu____5878 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5929  ->
                                                match uu___0_5929 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____5971 -> []))
                                         in
                                      FStar_All.pipe_right uu____5878
                                        FStar_List.split
                                       in
                                    (match uu____5867 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____6047 -> false  in
                                         let uu____6057 =
                                           let uu____6066 =
                                             let uu____6073 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____6076 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____6073, uu____6076)  in
                                           FStar_Pervasives_Native.Some
                                             uu____6066
                                            in
                                         (g2, uu____6057, pat_ty_compat))))))
  
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
            let uu____6208 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____6208 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____6271 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____6319 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____6319
             in
          let uu____6320 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____6320 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____6485,t1) ->
                let uu____6487 = FStar_Extraction_ML_UEnv.new_mlident g1  in
                (match uu____6487 with
                 | (g2,x) ->
                     let uu____6512 =
                       let uu____6524 =
                         let uu____6534 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty t0)
                             (FStar_Extraction_ML_Syntax.MLE_Var x)
                            in
                         ((x, t0), uu____6534)  in
                       uu____6524 :: more_args  in
                     eta_args g2 uu____6512 t1)
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6550,uu____6551)
                -> ((FStar_List.rev more_args), t)
            | uu____6576 ->
                let uu____6577 =
                  let uu____6579 =
                    let uu____6581 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu____6581
                      mlAppExpr
                     in
                  let uu____6582 =
                    let uu____6584 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlty uu____6584 t  in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6579 uu____6582
                   in
                failwith uu____6577
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____6618,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6655 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____6677 = eta_args g [] residualType  in
            match uu____6677 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____6735 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____6735
                 | uu____6736 ->
                     let uu____6748 = FStar_List.unzip eargs  in
                     (match uu____6748 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____6794 =
                                   let uu____6795 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6795
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6794
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6805 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6809,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6813;
                FStar_Extraction_ML_Syntax.loc = uu____6814;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____6837 ->
                    let uu____6840 =
                      let uu____6847 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6847, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6840
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
                     FStar_Extraction_ML_Syntax.mlty = uu____6851;
                     FStar_Extraction_ML_Syntax.loc = uu____6852;_},uu____6853);
                FStar_Extraction_ML_Syntax.mlty = uu____6854;
                FStar_Extraction_ML_Syntax.loc = uu____6855;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____6882 ->
                    let uu____6885 =
                      let uu____6892 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6892, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6885
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6896;
                FStar_Extraction_ML_Syntax.loc = uu____6897;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6905 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6905
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6909;
                FStar_Extraction_ML_Syntax.loc = uu____6910;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6912)) ->
              let uu____6925 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6925
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6929;
                     FStar_Extraction_ML_Syntax.loc = uu____6930;_},uu____6931);
                FStar_Extraction_ML_Syntax.mlty = uu____6932;
                FStar_Extraction_ML_Syntax.loc = uu____6933;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6945 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6945
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6949;
                     FStar_Extraction_ML_Syntax.loc = uu____6950;_},uu____6951);
                FStar_Extraction_ML_Syntax.mlty = uu____6952;
                FStar_Extraction_ML_Syntax.loc = uu____6953;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6955)) ->
              let uu____6972 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6972
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____6978 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6978
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6982)) ->
              let uu____6991 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6991
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6995;
                FStar_Extraction_ML_Syntax.loc = uu____6996;_},uu____6997),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____7004 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7004
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7008;
                FStar_Extraction_ML_Syntax.loc = uu____7009;_},uu____7010),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7011)) ->
              let uu____7024 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7024
          | uu____7027 -> mlAppExpr
  
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
        | uu____7058 -> (ml_e, tag)
  
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
      let maybe_generalize uu____7119 =
        match uu____7119 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____7140;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____7145;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____7226 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____7303 =
              let uu____7305 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Util.must_erase_for_extraction uu____7305
                lbtyp1
               in
            if uu____7303
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____7390 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____7390 (is_type_binder g) ->
                   let uu____7412 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____7412 with
                    | (bs1,c1) ->
                        let uu____7438 =
                          let uu____7451 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____7497 = is_type_binder g x  in
                                 Prims.op_Negation uu____7497) bs1
                             in
                          match uu____7451 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____7624 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____7624)
                           in
                        (match uu____7438 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____7686 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____7686
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____7735 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____7735 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7787 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____7787 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7890  ->
                                                       fun uu____7891  ->
                                                         match (uu____7890,
                                                                 uu____7891)
                                                         with
                                                         | ((x,uu____7917),
                                                            (y,uu____7919))
                                                             ->
                                                             let uu____7940 =
                                                               let uu____7947
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____7947)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7940)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____7964  ->
                                                       match uu____7964 with
                                                       | (a,uu____7972) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a false) g
                                                  targs
                                                 in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty
                                                 in
                                              let polytype =
                                                let uu____7984 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____8004  ->
                                                          match uu____8004
                                                          with
                                                          | (x,uu____8013) ->
                                                              let uu____8018
                                                                =
                                                                FStar_Extraction_ML_UEnv.lookup_ty
                                                                  env x
                                                                 in
                                                              uu____8018.FStar_Extraction_ML_UEnv.ty_b_name))
                                                   in
                                                (uu____7984, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____8030 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____8030)
                                                      ||
                                                      (let uu____8033 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____8033)
                                                | uu____8035 -> false  in
                                              let rest_args1 =
                                                if add_unit
                                                then
                                                  let uu____8047 =
                                                    unit_binder ()  in
                                                  uu____8047 :: rest_args
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____8104 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8123  ->
                                           match uu____8123 with
                                           | (a,uu____8131) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8143 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8163  ->
                                              match uu____8163 with
                                              | (x,uu____8172) ->
                                                  let uu____8177 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8177.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8143, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8217  ->
                                            match uu____8217 with
                                            | (bv,uu____8225) ->
                                                let uu____8230 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8230
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____8260 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8273  ->
                                           match uu____8273 with
                                           | (a,uu____8281) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8293 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8313  ->
                                              match uu____8313 with
                                              | (x,uu____8322) ->
                                                  let uu____8327 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8327.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8293, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8367  ->
                                            match uu____8367 with
                                            | (bv,uu____8375) ->
                                                let uu____8380 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8380
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
                              | FStar_Syntax_Syntax.Tm_name uu____8410 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8423  ->
                                           match uu____8423 with
                                           | (a,uu____8431) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8443 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8463  ->
                                              match uu____8463 with
                                              | (x,uu____8472) ->
                                                  let uu____8477 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8477.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8443, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8517  ->
                                            match uu____8517 with
                                            | (bv,uu____8525) ->
                                                let uu____8530 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8530
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
                              | uu____8560 -> err_value_restriction lbdef1)))
               | uu____8580 -> no_gen ())
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
           fun uu____8731  ->
             match uu____8731 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____8792 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____8792 with
                  | (env1,uu____8809,exp_binding) ->
                      let uu____8813 =
                        let uu____8818 = FStar_Util.right lbname  in
                        (uu____8818, exp_binding)  in
                      (env1, uu____8813))) g lbs1
  
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
            (fun uu____8885  ->
               let uu____8886 = FStar_Syntax_Print.term_to_string e  in
               let uu____8888 =
                 let uu____8890 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g  in
                 FStar_Extraction_ML_Code.string_of_mlty uu____8890 ty  in
               let uu____8891 = FStar_Extraction_ML_Util.eff_to_string f  in
               FStar_Util.print3 "Checking %s at type %s and eff %s\n"
                 uu____8886 uu____8888 uu____8891);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____8898) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8899 ->
               let uu____8904 = term_as_mlexpr g e  in
               (match uu____8904 with
                | (ml_e,tag,t) ->
                    let uu____8918 = FStar_Extraction_ML_Util.eff_leq tag f
                       in
                    if uu____8918
                    then
                      let uu____8925 =
                        maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t ty
                         in
                      (uu____8925, ty)
                    else
                      (match (tag, f, ty) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST
                          ,FStar_Extraction_ML_Syntax.E_PURE
                          ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                           let uu____8932 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t
                               ty
                              in
                           (uu____8932, ty)
                       | uu____8933 ->
                           (err_unexpected_eff g e ty f tag;
                            (let uu____8941 =
                               maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e
                                 t ty
                                in
                             (uu____8941, ty))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____8950 = term_as_mlexpr' g e  in
      match uu____8950 with
      | (e1,f,t) ->
          let uu____8966 = maybe_promote_effect e1 f t  in
          (match uu____8966 with | (e2,f1) -> (e2, f1, t))

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
           let uu____8992 =
             let uu____8994 =
               FStar_Range.string_of_range top1.FStar_Syntax_Syntax.pos  in
             let uu____8996 = FStar_Syntax_Print.tag_of_term top1  in
             let uu____8998 = FStar_Syntax_Print.term_to_string top1  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____8994 uu____8996 uu____8998
              in
           FStar_Util.print_string uu____8992);
      (let is_match t =
         let uu____9008 =
           let uu____9009 =
             let uu____9012 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9012 FStar_Syntax_Util.unascribe  in
           uu____9009.FStar_Syntax_Syntax.n  in
         match uu____9008 with
         | FStar_Syntax_Syntax.Tm_match uu____9016 -> true
         | uu____9040 -> false  in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____9059  ->
              match uu____9059 with
              | (t,uu____9068) ->
                  let uu____9073 =
                    let uu____9074 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
                    uu____9074.FStar_Syntax_Syntax.n  in
                  (match uu____9073 with
                   | FStar_Syntax_Syntax.Tm_name uu____9080 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____9082 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____9084 -> true
                   | uu____9086 -> false))
          in
       let apply_to_match_branches head1 args =
         let uu____9125 =
           let uu____9126 =
             let uu____9129 =
               FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9129 FStar_Syntax_Util.unascribe  in
           uu____9126.FStar_Syntax_Syntax.n  in
         match uu____9125 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee,branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____9253  ->
                       match uu____9253 with
                       | (pat,when_opt,body) ->
                           (pat, when_opt,
                             (let uu___1316_9310 = body  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1316_9310.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1316_9310.FStar_Syntax_Syntax.vars)
                              }))))
                in
             let uu___1319_9325 = head1  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1319_9325.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1319_9325.FStar_Syntax_Syntax.vars)
             }
         | uu____9346 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match"
          in
       let t = FStar_Syntax_Subst.compress top1  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9357 =
             let uu____9359 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9359
              in
           failwith uu____9357
       | FStar_Syntax_Syntax.Tm_delayed uu____9368 ->
           let uu____9391 =
             let uu____9393 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9393
              in
           failwith uu____9391
       | FStar_Syntax_Syntax.Tm_uvar uu____9402 ->
           let uu____9415 =
             let uu____9417 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9417
              in
           failwith uu____9415
       | FStar_Syntax_Syntax.Tm_bvar uu____9426 ->
           let uu____9427 =
             let uu____9429 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9429
              in
           failwith uu____9427
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9439 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____9439
       | FStar_Syntax_Syntax.Tm_type uu____9440 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9441 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9448 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____9464;_})
           ->
           let uu____9477 =
             let uu____9478 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9478  in
           (match uu____9477 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9485;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9487;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9488;_} ->
                let uu____9491 =
                  let uu____9492 =
                    let uu____9493 =
                      let uu____9500 =
                        let uu____9503 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____9503]  in
                      (fw, uu____9500)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9493  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9492
                   in
                (uu____9491, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9521 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____9521 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9529 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____9529 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____9540 =
                         let uu____9547 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____9547
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____9540 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____9555 =
                         let uu____9566 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____9566]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9555
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9593 =
                    let uu____9600 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____9600 tv  in
                  uu____9593 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____9608 =
                    let uu____9619 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____9619]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9608
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____9646)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9679 =
                  let uu____9686 =
                    let uu____9695 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.effect_decl_opt uu____9695 m  in
                  FStar_Util.must uu____9686  in
                (match uu____9679 with
                 | (ed,qualifiers) ->
                     let uu____9714 =
                       let uu____9716 =
                         let uu____9718 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                         FStar_TypeChecker_Env.is_reifiable_effect uu____9718
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____9716  in
                     if uu____9714
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9735 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9737) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9743) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9749 =
             let uu____9756 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_TcTerm.type_of_tot_term uu____9756 t  in
           (match uu____9749 with
            | (uu____9763,ty,uu____9765) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____9767 =
                  let uu____9768 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9768  in
                (uu____9767, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9769 ->
           let uu____9770 = is_type g t  in
           if uu____9770
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9781 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____9781 with
              | (FStar_Util.Inl uu____9794,uu____9795) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9800;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9803;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____9821 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____9821, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9822 -> instantiate_maybe_partial g x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9824 = is_type g t  in
           if uu____9824
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9835 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____9835 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9844;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9847;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9855  ->
                        let uu____9856 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____9858 =
                          let uu____9860 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            uu____9860 x
                           in
                        let uu____9861 =
                          let uu____9863 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlty uu____9863
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9856 uu____9858 uu____9861);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____9875 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____9875, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9876 -> instantiate_maybe_partial g x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____9904 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____9904 with
            | (bs1,body1) ->
                let uu____9917 = binders_as_ml_binders g bs1  in
                (match uu____9917 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9953 =
                             let uu____9955 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Env.is_reifiable_rc uu____9955
                               rc
                              in
                           if uu____9953
                           then
                             let uu____9957 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Util.reify_body uu____9957
                               [FStar_TypeChecker_Env.Inlining] body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9963  ->
                                 let uu____9964 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9964);
                            body1)
                        in
                     let uu____9967 = term_as_mlexpr env body2  in
                     (match uu____9967 with
                      | (ml_body,f,t1) ->
                          let uu____9983 =
                            FStar_List.fold_right
                              (fun uu____10003  ->
                                 fun uu____10004  ->
                                   match (uu____10003, uu____10004) with
                                   | ((uu____10027,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____9983 with
                           | (f1,tfun) ->
                               let uu____10050 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____10050, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____10058;
              FStar_Syntax_Syntax.vars = uu____10059;_},(a1,uu____10061)::[])
           ->
           let ty =
             let uu____10101 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____10101  in
           let uu____10102 =
             let uu____10103 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____10103
              in
           (uu____10102, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____10104;
              FStar_Syntax_Syntax.vars = uu____10105;_},(t1,uu____10107)::
            (r,uu____10109)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____10164);
              FStar_Syntax_Syntax.pos = uu____10165;
              FStar_Syntax_Syntax.vars = uu____10166;_},uu____10167)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (is_match head1) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____10226 =
             FStar_All.pipe_right args (apply_to_match_branches head1)  in
           FStar_All.pipe_right uu____10226 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_10280  ->
                        match uu___1_10280 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____10283 -> false)))
              in
           let uu____10285 =
             let uu____10286 =
               let uu____10289 =
                 FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
               FStar_All.pipe_right uu____10289 FStar_Syntax_Util.unascribe
                in
             uu____10286.FStar_Syntax_Syntax.n  in
           (match uu____10285 with
            | FStar_Syntax_Syntax.Tm_abs (bs,uu____10299,_rc) ->
                let uu____10325 =
                  let uu____10326 =
                    let uu____10331 =
                      FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses]
                      uu____10331
                     in
                  FStar_All.pipe_right t uu____10326  in
                FStar_All.pipe_right uu____10325 (term_as_mlexpr g)
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                let e =
                  let uu____10339 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  let uu____10340 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg uu____10339
                    [FStar_TypeChecker_Env.Inlining] head1 uu____10340
                   in
                let tm =
                  let uu____10352 =
                    let uu____10357 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____10358 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____10357 uu____10358  in
                  uu____10352 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____10367 ->
                let rec extract_app is_data uu____10416 uu____10417 restArgs
                  =
                  match (uu____10416, uu____10417) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____10498 =
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
                         (fun uu____10525  ->
                            let uu____10526 =
                              let uu____10528 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              let uu____10529 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____10528 uu____10529
                               in
                            let uu____10530 =
                              let uu____10532 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlty
                                uu____10532 t1
                               in
                            let uu____10533 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____10544)::uu____10545 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10526 uu____10530 uu____10533);
                       (match (restArgs, t1) with
                        | ([],uu____10579) ->
                            let app =
                              let uu____10595 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10595
                               in
                            (app, f, t1)
                        | ((arg,uu____10597)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10628 =
                              let uu____10633 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____10633, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10628 rest
                        | ((e0,uu____10645)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____10678 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____10678
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____10683 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____10683 with
                             | (e01,tInferred) ->
                                 let uu____10696 =
                                   let uu____10701 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____10701, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10696 rest)
                        | uu____10712 ->
                            let uu____10725 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____10725 with
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
                                  | uu____10797 ->
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
                let extract_app_maybe_projector is_data mlhead uu____10868
                  args1 =
                  match uu____10868 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10898)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10982))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____10984,f',t3)) ->
                                 let uu____11022 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____11022 t3
                             | uu____11023 -> (args2, f1, t2)  in
                           let uu____11048 = remove_implicits args1 f t1  in
                           (match uu____11048 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____11104 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____11128 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____11136 ->
                      let uu____11137 =
                        let uu____11158 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____11158 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11197  ->
                                  let uu____11198 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____11200 =
                                    let uu____11202 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11202
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11203 =
                                    let uu____11205 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11205
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11206 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11198 uu____11200 uu____11203
                                    uu____11206);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11233 -> failwith "FIXME Ty"  in
                      (match uu____11137 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11309)::uu____11310 -> is_type g a
                             | uu____11337 -> false  in
                           let uu____11349 =
                             match vars with
                             | uu____11378::uu____11379 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11393 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____11399 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____11437 =
                                       FStar_List.map
                                         (fun uu____11449  ->
                                            match uu____11449 with
                                            | (x,uu____11457) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____11437, [])
                                   else
                                     (let uu____11480 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____11480 with
                                      | (prefix1,rest) ->
                                          let uu____11569 =
                                            FStar_List.map
                                              (fun uu____11581  ->
                                                 match uu____11581 with
                                                 | (x,uu____11589) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____11569, rest))
                                    in
                                 (match uu____11399 with
                                  | (provided_type_args,rest) ->
                                      let uu____11640 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____11649 ->
                                            let uu____11650 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11650 with
                                             | (head3,uu____11662,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____11664 ->
                                            let uu____11666 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11666 with
                                             | (head3,uu____11678,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____11681;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____11682;_}::[])
                                            ->
                                            let uu____11685 =
                                              instantiate_maybe_partial g
                                                head3 (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11685 with
                                             | (head4,uu____11697,t2) ->
                                                 let uu____11699 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____11699, t2))
                                        | uu____11702 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____11640 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____11349 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11769 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____11769,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11770 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11779 ->
                      let uu____11780 =
                        let uu____11801 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____11801 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11840  ->
                                  let uu____11841 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____11843 =
                                    let uu____11845 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11845
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11846 =
                                    let uu____11848 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11848
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11849 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11841 uu____11843 uu____11846
                                    uu____11849);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11876 -> failwith "FIXME Ty"  in
                      (match uu____11780 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11952)::uu____11953 -> is_type g a
                             | uu____11980 -> false  in
                           let uu____11992 =
                             match vars with
                             | uu____12021::uu____12022 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____12036 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____12042 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____12080 =
                                       FStar_List.map
                                         (fun uu____12092  ->
                                            match uu____12092 with
                                            | (x,uu____12100) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____12080, [])
                                   else
                                     (let uu____12123 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____12123 with
                                      | (prefix1,rest) ->
                                          let uu____12212 =
                                            FStar_List.map
                                              (fun uu____12224  ->
                                                 match uu____12224 with
                                                 | (x,uu____12232) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____12212, rest))
                                    in
                                 (match uu____12042 with
                                  | (provided_type_args,rest) ->
                                      let uu____12283 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____12292 ->
                                            let uu____12293 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12293 with
                                             | (head3,uu____12305,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____12307 ->
                                            let uu____12309 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12309 with
                                             | (head3,uu____12321,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____12324;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____12325;_}::[])
                                            ->
                                            let uu____12328 =
                                              instantiate_maybe_partial g
                                                head3 (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12328 with
                                             | (head4,uu____12340,t2) ->
                                                 let uu____12342 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____12342, t2))
                                        | uu____12345 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____12283 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____11992 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12412 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____12412,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12413 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12422 ->
                      let uu____12423 = term_as_mlexpr g head2  in
                      (match uu____12423 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____12439 = is_type g t  in
                if uu____12439
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12450 =
                     let uu____12451 = FStar_Syntax_Util.un_uinst head1  in
                     uu____12451.FStar_Syntax_Syntax.n  in
                   match uu____12450 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12461 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____12461 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12470 -> extract_app_with_instantiations ())
                   | uu____12473 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____12476),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12541 =
                   let uu____12542 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                      in
                   maybe_reify_comp g uu____12542 c  in
                 term_as_mlty g uu____12541
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____12546 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____12546 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e') when
           (let uu____12578 = FStar_Syntax_Syntax.is_top_level [lb]  in
            Prims.op_Negation uu____12578) &&
             (let uu____12581 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs
                 in
              FStar_Util.is_some uu____12581)
           ->
           let b =
             let uu____12591 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                in
             (uu____12591, FStar_Pervasives_Native.None)  in
           let uu____12594 = FStar_Syntax_Subst.open_term [b] e'  in
           (match uu____12594 with
            | ((x,uu____12618)::uu____12619,body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str,uu____12648)::[]) ->
                      let uu____12673 =
                        let uu____12674 = FStar_Syntax_Subst.compress str  in
                        uu____12674.FStar_Syntax_Syntax.n  in
                      (match uu____12673 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s,uu____12680)) ->
                           let id1 =
                             let uu____12684 =
                               let uu____12690 =
                                 FStar_Syntax_Syntax.range_of_bv x  in
                               (s, uu____12690)  in
                             FStar_Ident.mk_ident uu____12684  in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id1;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             }  in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv  in
                           FStar_Pervasives_Native.Some bv1
                       | uu____12695 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                   in
                let remove_attr1 attrs =
                  let uu____12712 =
                    FStar_List.partition
                      (fun attr  ->
                         let uu____12724 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr]
                            in
                         FStar_Util.is_some uu____12724)
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match uu____12712 with
                  | (uu____12729,other_attrs) -> other_attrs  in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None  ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1778_12757 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1778_12757.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1778_12757.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1778_12757.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1778_12757.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1778_12757.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1778_12757.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      let rename =
                        let uu____12765 =
                          let uu____12766 =
                            let uu____12773 =
                              FStar_Syntax_Syntax.bv_to_name y  in
                            (x, uu____12773)  in
                          FStar_Syntax_Syntax.NT uu____12766  in
                        [uu____12765]  in
                      let body1 =
                        let uu____12779 =
                          FStar_Syntax_Subst.subst rename body  in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____12779
                         in
                      let lb1 =
                        let uu___1785_12795 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1785_12795.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1785_12795.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1785_12795.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1785_12795.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1785_12795.FStar_Syntax_Syntax.lbpos)
                        }  in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1)
                   in
                let top2 =
                  let uu___1789_12812 = top1  in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1789_12812.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1789_12812.FStar_Syntax_Syntax.vars)
                  }  in
                term_as_mlexpr' g top2)
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____12835 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12851 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____12851
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____12866 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____12866  in
                   let lb1 =
                     let uu___1803_12868 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1803_12868.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1803_12868.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1803_12868.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1803_12868.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1803_12868.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1803_12868.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____12835 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____12893 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      let uu____12894 =
                        let uu____12895 =
                          let uu____12896 =
                            let uu____12900 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Pervasives_Native.fst uu____12900  in
                          let uu____12913 =
                            let uu____12917 =
                              let uu____12919 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Pervasives_Native.snd uu____12919  in
                            [uu____12917]  in
                          FStar_List.append uu____12896 uu____12913  in
                        FStar_Ident.lid_of_path uu____12895
                          FStar_Range.dummyRange
                         in
                      FStar_TypeChecker_Env.set_current_module uu____12893
                        uu____12894
                       in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let lbdef =
                              let uu____12946 = FStar_Options.ml_ish ()  in
                              if uu____12946
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____12958 =
                                   let uu____12959 =
                                     let uu____12960 =
                                       extraction_norm_steps ()  in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____12960
                                      in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____12959 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____12963 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____12963
                                 then
                                   ((let uu____12973 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____12973);
                                    (let a =
                                       let uu____12979 =
                                         let uu____12981 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____12981
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____12979 norm_call
                                        in
                                     a))
                                 else norm_call ())
                               in
                            let uu___1820_12988 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1820_12988.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1820_12988.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1820_12988.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1820_12988.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1820_12988.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1820_12988.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____13041 =
                  match uu____13041 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____13197  ->
                               match uu____13197 with
                               | (a,uu____13205) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     false) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____13212 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____13212 with
                       | (e1,ty) ->
                           let uu____13223 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____13223 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____13235 -> []  in
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
                let uu____13266 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____13363  ->
                         match uu____13363 with
                         | (env,lbs4) ->
                             let uu____13497 = lb  in
                             (match uu____13497 with
                              | (lbname,uu____13548,(t1,(uu____13550,polytype)),add_unit,uu____13553)
                                  ->
                                  let uu____13568 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____13568 with
                                   | (env1,nm,uu____13609) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____13266 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____13888 = term_as_mlexpr env_body e'1  in
                     (match uu____13888 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____13905 =
                              let uu____13908 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____13908  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13905
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____13921 =
                            let uu____13922 =
                              let uu____13923 =
                                let uu____13924 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____13924)  in
                              mk_MLE_Let top_level uu____13923 e'2  in
                            let uu____13933 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13922 uu____13933
                             in
                          (uu____13921, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____13972 = term_as_mlexpr g scrutinee  in
           (match uu____13972 with
            | (e,f_e,t_e) ->
                let uu____13988 = check_pats_for_ite pats  in
                (match uu____13988 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____14053 = term_as_mlexpr g then_e1  in
                            (match uu____14053 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____14069 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____14069 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____14085 =
                                        let uu____14096 =
                                          type_leq g t_then t_else  in
                                        if uu____14096
                                        then (t_else, no_lift)
                                        else
                                          (let uu____14117 =
                                             type_leq g t_else t_then  in
                                           if uu____14117
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____14085 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____14164 =
                                             let uu____14165 =
                                               let uu____14166 =
                                                 let uu____14175 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____14176 =
                                                   let uu____14179 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____14179
                                                    in
                                                 (e, uu____14175,
                                                   uu____14176)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____14166
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____14165
                                              in
                                           let uu____14182 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____14164, uu____14182,
                                             t_branch))))
                        | uu____14183 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____14201 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____14300 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____14300 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____14345 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____14345 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____14407 =
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
                                                   let uu____14430 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____14430 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____14407 with
                                              | (when_opt1,f_when) ->
                                                  let uu____14480 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____14480 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____14515 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14592 
                                                                 ->
                                                                 match uu____14592
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
                                                         uu____14515)))))
                               true)
                           in
                        match uu____14201 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14763  ->
                                      let uu____14764 =
                                        let uu____14766 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu____14766 e
                                         in
                                      let uu____14767 =
                                        let uu____14769 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu____14769 t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14764 uu____14767);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14795 =
                                   let uu____14796 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14796
                                    in
                                 (match uu____14795 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14803;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14805;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____14806;_}
                                      ->
                                      let uu____14809 =
                                        let uu____14810 =
                                          let uu____14811 =
                                            let uu____14818 =
                                              let uu____14821 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____14821]  in
                                            (fw, uu____14818)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14811
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14810
                                         in
                                      (uu____14809,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14825,uu____14826,(uu____14827,f_first,t_first))::rest
                                 ->
                                 let uu____14887 =
                                   FStar_List.fold_left
                                     (fun uu____14929  ->
                                        fun uu____14930  ->
                                          match (uu____14929, uu____14930)
                                          with
                                          | ((topt,f),(uu____14987,uu____14988,
                                                       (uu____14989,f_branch,t_branch)))
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
                                                    let uu____15045 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____15045
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____15052 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____15052
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
                                 (match uu____14887 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____15150  ->
                                                match uu____15150 with
                                                | (p,(wopt,uu____15179),
                                                   (b1,uu____15181,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____15200 -> b1
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
                                      let uu____15205 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____15205, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____15232 =
          let uu____15237 =
            let uu____15246 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_lid uu____15246 discName  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15237  in
        match uu____15232 with
        | (uu____15263,fstar_disc_type) ->
            let uu____15265 =
              let uu____15277 =
                let uu____15278 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____15278.FStar_Syntax_Syntax.n  in
              match uu____15277 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15293) ->
                  let binders1 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_15348  ->
                            match uu___2_15348 with
                            | (uu____15356,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15357)) ->
                                true
                            | uu____15362 -> false))
                     in
                  FStar_List.fold_right
                    (fun uu____15394  ->
                       fun uu____15395  ->
                         match uu____15395 with
                         | (g,vs) ->
                             let uu____15440 =
                               FStar_Extraction_ML_UEnv.new_mlident g  in
                             (match uu____15440 with
                              | (g1,v1) ->
                                  (g1,
                                    ((v1,
                                       FStar_Extraction_ML_Syntax.MLTY_Top)
                                    :: vs)))) binders1 (env, [])
              | uu____15486 -> failwith "Discriminator must be a function"
               in
            (match uu____15265 with
             | (g,wildcards) ->
                 let uu____15515 = FStar_Extraction_ML_UEnv.new_mlident g  in
                 (match uu____15515 with
                  | (g1,mlid) ->
                      let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let discrBody =
                        let uu____15528 =
                          let uu____15529 =
                            let uu____15541 =
                              let uu____15542 =
                                let uu____15543 =
                                  let uu____15558 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         targ)
                                      (FStar_Extraction_ML_Syntax.MLE_Name
                                         ([], mlid))
                                     in
                                  let uu____15564 =
                                    let uu____15575 =
                                      let uu____15584 =
                                        let uu____15585 =
                                          let uu____15592 =
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                              constrName
                                             in
                                          (uu____15592,
                                            [FStar_Extraction_ML_Syntax.MLP_Wild])
                                           in
                                        FStar_Extraction_ML_Syntax.MLP_CTor
                                          uu____15585
                                         in
                                      let uu____15595 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_bool_ty)
                                          (FStar_Extraction_ML_Syntax.MLE_Const
                                             (FStar_Extraction_ML_Syntax.MLC_Bool
                                                true))
                                         in
                                      (uu____15584,
                                        FStar_Pervasives_Native.None,
                                        uu____15595)
                                       in
                                    let uu____15599 =
                                      let uu____15610 =
                                        let uu____15619 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.ml_bool_ty)
                                            (FStar_Extraction_ML_Syntax.MLE_Const
                                               (FStar_Extraction_ML_Syntax.MLC_Bool
                                                  false))
                                           in
                                        (FStar_Extraction_ML_Syntax.MLP_Wild,
                                          FStar_Pervasives_Native.None,
                                          uu____15619)
                                         in
                                      [uu____15610]  in
                                    uu____15575 :: uu____15599  in
                                  (uu____15558, uu____15564)  in
                                FStar_Extraction_ML_Syntax.MLE_Match
                                  uu____15543
                                 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                uu____15542
                               in
                            ((FStar_List.append wildcards [(mlid, targ)]),
                              uu____15541)
                             in
                          FStar_Extraction_ML_Syntax.MLE_Fun uu____15529  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty disc_ty)
                          uu____15528
                         in
                      let uu____15680 =
                        let uu____15681 =
                          let uu____15684 =
                            let uu____15685 =
                              FStar_Extraction_ML_UEnv.convIdent
                                discName.FStar_Ident.ident
                               in
                            {
                              FStar_Extraction_ML_Syntax.mllb_name =
                                uu____15685;
                              FStar_Extraction_ML_Syntax.mllb_tysc =
                                FStar_Pervasives_Native.None;
                              FStar_Extraction_ML_Syntax.mllb_add_unit =
                                false;
                              FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                              FStar_Extraction_ML_Syntax.mllb_meta = [];
                              FStar_Extraction_ML_Syntax.print_typ = false
                            }  in
                          [uu____15684]  in
                        (FStar_Extraction_ML_Syntax.NonRec, uu____15681)  in
                      FStar_Extraction_ML_Syntax.MLM_Let uu____15680))
  