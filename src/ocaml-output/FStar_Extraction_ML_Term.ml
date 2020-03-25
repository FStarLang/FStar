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
             (fun uu____4183  ->
                fun b  ->
                  match uu____4183 with
                  | (ml_bs,env) ->
                      let uu____4229 = is_type_binder g b  in
                      if uu____4229
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1 true  in
                        let ml_b =
                          let uu____4252 =
                            FStar_Extraction_ML_UEnv.lookup_ty env1 b1  in
                          uu____4252.FStar_Extraction_ML_UEnv.ty_b_name  in
                        let ml_b1 =
                          (ml_b, FStar_Extraction_ML_Syntax.ml_unit_ty)  in
                        ((ml_b1 :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____4278 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____4278 with
                         | (env1,b2,uu____4303) ->
                             let ml_b = (b2, t)  in ((ml_b :: ml_bs), env1)))
             ([], g))
         in
      match uu____4126 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        let uu____4388 = extraction_norm_steps ()  in
        let uu____4389 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Normalize.normalize uu____4388 uu____4389 t0  in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____4408) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4411,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4415 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____4449 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4450 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4451 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4460 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____4488 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____4488 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____4495 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____4528 -> p))
      | uu____4531 -> p
  
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
                       (fun uu____4633  ->
                          let uu____4634 =
                            let uu____4636 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4636 t'
                             in
                          let uu____4637 =
                            let uu____4639 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4639 t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4634 uu____4637)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____4674 = FStar_Options.codegen ()  in
                uu____4674 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4679 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4692 =
                        let uu____4693 =
                          let uu____4694 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4694  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4693
                         in
                      (uu____4692, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        let uu____4716 =
                          let uu____4717 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                          uu____4717.FStar_TypeChecker_Env.dsenv  in
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          uu____4716 c sw FStar_Range.dummyRange
                         in
                      let uu____4718 = term_as_mlexpr g source_term  in
                      (match uu____4718 with
                       | (mlterm,uu____4730,mlty) -> (mlterm, mlty))
                   in
                (match uu____4679 with
                 | (mlc,ml_ty) ->
                     let uu____4749 = FStar_Extraction_ML_UEnv.new_mlident g
                        in
                     (match uu____4749 with
                      | (g1,x) ->
                          let when_clause =
                            let uu____4775 =
                              let uu____4776 =
                                let uu____4783 =
                                  let uu____4786 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         ml_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Var x)
                                     in
                                  [uu____4786; mlc]  in
                                (FStar_Extraction_ML_Util.prims_op_equality,
                                  uu____4783)
                                 in
                              FStar_Extraction_ML_Syntax.MLE_App uu____4776
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_bool_ty)
                              uu____4775
                             in
                          let uu____4789 = ok ml_ty  in
                          (g1,
                            (FStar_Pervasives_Native.Some
                               ((FStar_Extraction_ML_Syntax.MLP_Var x),
                                 [when_clause])), uu____4789)))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  let uu____4810 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_TcTerm.tc_constant uu____4810
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____4812 =
                  let uu____4821 =
                    let uu____4828 =
                      let uu____4829 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4829  in
                    (uu____4828, [])  in
                  FStar_Pervasives_Native.Some uu____4821  in
                let uu____4838 = ok mlty  in (g, uu____4812, uu____4838)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4851 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4851 with
                 | (g1,x1,uu____4879) ->
                     let uu____4882 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4882))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4920 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4920 with
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
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____5050;
                          FStar_Extraction_ML_Syntax.loc = uu____5051;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____5053;_}
                      -> (n1, ttys)
                  | uu____5060 -> failwith "Expected a constructor"  in
                (match uu____5030 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____5097 = FStar_Util.first_N nTyVars pats  in
                     (match uu____5097 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___848_5201  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____5232  ->
                                               match uu____5232 with
                                               | (p1,uu____5239) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5242,t) ->
                                                        term_as_mlty g t
                                                    | uu____5248 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5252 
                                                              ->
                                                              let uu____5253
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5253);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____5257 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____5257)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____5286 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____5323  ->
                                   match uu____5323 with
                                   | (p1,imp1) ->
                                       let uu____5345 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____5345 with
                                        | (g2,p2,uu____5376) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____5286 with
                           | (g1,tyMLPats) ->
                               let uu____5440 =
                                 FStar_Util.fold_map
                                   (fun uu____5505  ->
                                      fun uu____5506  ->
                                        match (uu____5505, uu____5506) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____5604 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____5664 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____5604 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____5735 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____5735 with
                                                  | (g3,p2,uu____5778) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____5440 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____5899 =
                                      let uu____5910 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5961  ->
                                                match uu___0_5961 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____6003 -> []))
                                         in
                                      FStar_All.pipe_right uu____5910
                                        FStar_List.split
                                       in
                                    (match uu____5899 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____6079 -> false  in
                                         let uu____6089 =
                                           let uu____6098 =
                                             let uu____6105 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____6108 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____6105, uu____6108)  in
                                           FStar_Pervasives_Native.Some
                                             uu____6098
                                            in
                                         (g2, uu____6089, pat_ty_compat))))))
  
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
            let uu____6240 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____6240 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____6303 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____6351 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____6351
             in
          let uu____6352 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____6352 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____6517,t1) ->
                let uu____6519 = FStar_Extraction_ML_UEnv.new_mlident g1  in
                (match uu____6519 with
                 | (g2,x) ->
                     let uu____6544 =
                       let uu____6556 =
                         let uu____6566 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty t0)
                             (FStar_Extraction_ML_Syntax.MLE_Var x)
                            in
                         ((x, t0), uu____6566)  in
                       uu____6556 :: more_args  in
                     eta_args g2 uu____6544 t1)
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6582,uu____6583)
                -> ((FStar_List.rev more_args), t)
            | uu____6608 ->
                let uu____6609 =
                  let uu____6611 =
                    let uu____6613 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu____6613
                      mlAppExpr
                     in
                  let uu____6614 =
                    let uu____6616 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlty uu____6616 t  in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6611 uu____6614
                   in
                failwith uu____6609
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____6650,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6687 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____6709 = eta_args g [] residualType  in
            match uu____6709 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____6767 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____6767
                 | uu____6768 ->
                     let uu____6780 = FStar_List.unzip eargs  in
                     (match uu____6780 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____6826 =
                                   let uu____6827 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6827
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6826
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6837 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6841,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6845;
                FStar_Extraction_ML_Syntax.loc = uu____6846;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____6869 ->
                    let uu____6872 =
                      let uu____6879 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6879, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6872
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
                     FStar_Extraction_ML_Syntax.mlty = uu____6883;
                     FStar_Extraction_ML_Syntax.loc = uu____6884;_},uu____6885);
                FStar_Extraction_ML_Syntax.mlty = uu____6886;
                FStar_Extraction_ML_Syntax.loc = uu____6887;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____6914 ->
                    let uu____6917 =
                      let uu____6924 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6924, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6917
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6928;
                FStar_Extraction_ML_Syntax.loc = uu____6929;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6937 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6937
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6941;
                FStar_Extraction_ML_Syntax.loc = uu____6942;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6944)) ->
              let uu____6957 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6957
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6961;
                     FStar_Extraction_ML_Syntax.loc = uu____6962;_},uu____6963);
                FStar_Extraction_ML_Syntax.mlty = uu____6964;
                FStar_Extraction_ML_Syntax.loc = uu____6965;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6977 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6977
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6981;
                     FStar_Extraction_ML_Syntax.loc = uu____6982;_},uu____6983);
                FStar_Extraction_ML_Syntax.mlty = uu____6984;
                FStar_Extraction_ML_Syntax.loc = uu____6985;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6987)) ->
              let uu____7004 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7004
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____7010 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7010
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7014)) ->
              let uu____7023 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7023
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7027;
                FStar_Extraction_ML_Syntax.loc = uu____7028;_},uu____7029),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____7036 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7036
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7040;
                FStar_Extraction_ML_Syntax.loc = uu____7041;_},uu____7042),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7043)) ->
              let uu____7056 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7056
          | uu____7059 -> mlAppExpr
  
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
        | uu____7090 -> (ml_e, tag)
  
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
      let maybe_generalize uu____7151 =
        match uu____7151 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____7172;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____7177;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____7258 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____7335 =
              let uu____7337 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Util.must_erase_for_extraction uu____7337
                lbtyp1
               in
            if uu____7335
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____7422 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____7422 (is_type_binder g) ->
                   let uu____7444 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____7444 with
                    | (bs1,c1) ->
                        let uu____7470 =
                          let uu____7483 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____7529 = is_type_binder g x  in
                                 Prims.op_Negation uu____7529) bs1
                             in
                          match uu____7483 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____7656 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____7656)
                           in
                        (match uu____7470 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____7718 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____7718
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____7767 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____7767 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7819 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____7819 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7922  ->
                                                       fun uu____7923  ->
                                                         match (uu____7922,
                                                                 uu____7923)
                                                         with
                                                         | ((x,uu____7949),
                                                            (y,uu____7951))
                                                             ->
                                                             let uu____7972 =
                                                               let uu____7979
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____7979)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7972)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____7996  ->
                                                       match uu____7996 with
                                                       | (a,uu____8004) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a false) g
                                                  targs
                                                 in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty
                                                 in
                                              let polytype =
                                                let uu____8016 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____8036  ->
                                                          match uu____8036
                                                          with
                                                          | (x,uu____8045) ->
                                                              let uu____8050
                                                                =
                                                                FStar_Extraction_ML_UEnv.lookup_ty
                                                                  env x
                                                                 in
                                                              uu____8050.FStar_Extraction_ML_UEnv.ty_b_name))
                                                   in
                                                (uu____8016, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____8062 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____8062)
                                                      ||
                                                      (let uu____8065 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____8065)
                                                | uu____8067 -> false  in
                                              let rest_args1 =
                                                if add_unit
                                                then
                                                  let uu____8079 =
                                                    unit_binder ()  in
                                                  uu____8079 :: rest_args
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____8136 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8155  ->
                                           match uu____8155 with
                                           | (a,uu____8163) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8175 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8195  ->
                                              match uu____8195 with
                                              | (x,uu____8204) ->
                                                  let uu____8209 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8209.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8175, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8249  ->
                                            match uu____8249 with
                                            | (bv,uu____8257) ->
                                                let uu____8262 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8262
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____8292 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8305  ->
                                           match uu____8305 with
                                           | (a,uu____8313) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8325 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8345  ->
                                              match uu____8345 with
                                              | (x,uu____8354) ->
                                                  let uu____8359 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8359.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8325, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8399  ->
                                            match uu____8399 with
                                            | (bv,uu____8407) ->
                                                let uu____8412 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8412
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
                              | FStar_Syntax_Syntax.Tm_name uu____8442 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8455  ->
                                           match uu____8455 with
                                           | (a,uu____8463) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8475 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8495  ->
                                              match uu____8495 with
                                              | (x,uu____8504) ->
                                                  let uu____8509 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8509.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8475, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8549  ->
                                            match uu____8549 with
                                            | (bv,uu____8557) ->
                                                let uu____8562 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8562
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
                              | uu____8592 -> err_value_restriction lbdef1)))
               | uu____8612 -> no_gen ())
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
           fun uu____8763  ->
             match uu____8763 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____8824 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____8824 with
                  | (env1,uu____8841,exp_binding) ->
                      let uu____8845 =
                        let uu____8850 = FStar_Util.right lbname  in
                        (uu____8850, exp_binding)  in
                      (env1, uu____8845))) g lbs1
  
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
            (fun uu____8916  ->
               let uu____8917 = FStar_Syntax_Print.term_to_string e  in
               let uu____8919 =
                 let uu____8921 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g  in
                 FStar_Extraction_ML_Code.string_of_mlty uu____8921 ty  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____8917
                 uu____8919);
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
                    let uu____8947 = maybe_promote_effect ml_e tag t  in
                    (match uu____8947 with
                     | (ml_e1,tag1) ->
                         let uu____8958 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____8958
                         then
                           let uu____8965 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____8965, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____8972 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____8972, ty)
                            | uu____8973 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____8981 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____8981, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____8984 = term_as_mlexpr' g e  in
      match uu____8984 with
      | (e1,f,t) ->
          let uu____9000 = maybe_promote_effect e1 f t  in
          (match uu____9000 with | (e2,f1) -> (e2, f1, t))

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
           let uu____9025 =
             let uu____9027 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____9029 = FStar_Syntax_Print.tag_of_term top  in
             let uu____9031 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____9027 uu____9029 uu____9031
              in
           FStar_Util.print_string uu____9025);
      (let is_match t =
         let uu____9041 =
           let uu____9042 =
             let uu____9045 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9045 FStar_Syntax_Util.unascribe  in
           uu____9042.FStar_Syntax_Syntax.n  in
         match uu____9041 with
         | FStar_Syntax_Syntax.Tm_match uu____9049 -> true
         | uu____9073 -> false  in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____9092  ->
              match uu____9092 with
              | (t,uu____9101) ->
                  let uu____9106 =
                    let uu____9107 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
                    uu____9107.FStar_Syntax_Syntax.n  in
                  (match uu____9106 with
                   | FStar_Syntax_Syntax.Tm_name uu____9113 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____9115 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____9117 -> true
                   | uu____9119 -> false))
          in
       let apply_to_match_branches head1 args =
         let uu____9158 =
           let uu____9159 =
             let uu____9162 =
               FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9162 FStar_Syntax_Util.unascribe  in
           uu____9159.FStar_Syntax_Syntax.n  in
         match uu____9158 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee,branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____9286  ->
                       match uu____9286 with
                       | (pat,when_opt,body) ->
                           (pat, when_opt,
                             (let uu___1318_9343 = body  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1318_9343.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1318_9343.FStar_Syntax_Syntax.vars)
                              }))))
                in
             let uu___1321_9358 = head1  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1321_9358.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1321_9358.FStar_Syntax_Syntax.vars)
             }
         | uu____9379 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match"
          in
       let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9390 =
             let uu____9392 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9392
              in
           failwith uu____9390
       | FStar_Syntax_Syntax.Tm_delayed uu____9401 ->
           let uu____9424 =
             let uu____9426 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9426
              in
           failwith uu____9424
       | FStar_Syntax_Syntax.Tm_uvar uu____9435 ->
           let uu____9448 =
             let uu____9450 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9450
              in
           failwith uu____9448
       | FStar_Syntax_Syntax.Tm_bvar uu____9459 ->
           let uu____9460 =
             let uu____9462 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9462
              in
           failwith uu____9460
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9472 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____9472
       | FStar_Syntax_Syntax.Tm_type uu____9473 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9474 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9481 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____9497;_})
           ->
           let uu____9510 =
             let uu____9511 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9511  in
           (match uu____9510 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9518;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9520;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9521;_} ->
                let uu____9524 =
                  let uu____9525 =
                    let uu____9526 =
                      let uu____9533 =
                        let uu____9536 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____9536]  in
                      (fw, uu____9533)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9526  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9525
                   in
                (uu____9524, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9554 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____9554 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9562 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____9562 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____9573 =
                         let uu____9580 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____9580
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____9573 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____9588 =
                         let uu____9599 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____9599]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9588
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9626 =
                    let uu____9633 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____9633 tv  in
                  uu____9626 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____9641 =
                    let uu____9652 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____9652]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9641
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____9679)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9712 =
                  let uu____9719 =
                    let uu____9728 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.effect_decl_opt uu____9728 m  in
                  FStar_Util.must uu____9719  in
                (match uu____9712 with
                 | (ed,qualifiers) ->
                     let uu____9747 =
                       let uu____9749 =
                         let uu____9751 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                         FStar_TypeChecker_Env.is_reifiable_effect uu____9751
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____9749  in
                     if uu____9747
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9768 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9770) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9776) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9782 =
             let uu____9789 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_TcTerm.type_of_tot_term uu____9789 t  in
           (match uu____9782 with
            | (uu____9796,ty,uu____9798) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____9800 =
                  let uu____9801 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9801  in
                (uu____9800, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9802 ->
           let uu____9803 = is_type g t  in
           if uu____9803
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9814 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____9814 with
              | (FStar_Util.Inl uu____9827,uu____9828) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9833;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9836;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____9854 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____9854, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9855 -> instantiate_maybe_partial g x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9857 = is_type g t  in
           if uu____9857
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9868 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____9868 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9877;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9880;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9888  ->
                        let uu____9889 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____9891 =
                          let uu____9893 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            uu____9893 x
                           in
                        let uu____9894 =
                          let uu____9896 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlty uu____9896
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9889 uu____9891 uu____9894);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____9908 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____9908, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9909 -> instantiate_maybe_partial g x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____9937 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____9937 with
            | (bs1,body1) ->
                let uu____9950 = binders_as_ml_binders g bs1  in
                (match uu____9950 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9986 =
                             let uu____9988 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Env.is_reifiable_rc uu____9988
                               rc
                              in
                           if uu____9986
                           then
                             let uu____9990 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Util.reify_body uu____9990
                               [FStar_TypeChecker_Env.Inlining] body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9996  ->
                                 let uu____9997 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9997);
                            body1)
                        in
                     let uu____10000 = term_as_mlexpr env body2  in
                     (match uu____10000 with
                      | (ml_body,f,t1) ->
                          let uu____10016 =
                            FStar_List.fold_right
                              (fun uu____10036  ->
                                 fun uu____10037  ->
                                   match (uu____10036, uu____10037) with
                                   | ((uu____10060,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____10016 with
                           | (f1,tfun) ->
                               let uu____10083 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____10083, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____10091;
              FStar_Syntax_Syntax.vars = uu____10092;_},(a1,uu____10094)::[])
           ->
           let ty =
             let uu____10134 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____10134  in
           let uu____10135 =
             let uu____10136 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____10136
              in
           (uu____10135, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____10137;
              FStar_Syntax_Syntax.vars = uu____10138;_},(t1,uu____10140)::
            (r,uu____10142)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____10197);
              FStar_Syntax_Syntax.pos = uu____10198;
              FStar_Syntax_Syntax.vars = uu____10199;_},uu____10200)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (is_match head1) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____10259 =
             FStar_All.pipe_right args (apply_to_match_branches head1)  in
           FStar_All.pipe_right uu____10259 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_10313  ->
                        match uu___1_10313 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____10316 -> false)))
              in
           let uu____10318 =
             let uu____10323 =
               let uu____10324 =
                 let uu____10327 =
                   FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
                 FStar_All.pipe_right uu____10327 FStar_Syntax_Util.unascribe
                  in
               uu____10324.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____10323)  in
           (match uu____10318 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____10336,uu____10337) ->
                let t1 =
                  let uu____10351 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Iota;
                    FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.AllowUnboundUniverses] uu____10351
                    t
                   in
                term_as_mlexpr g t1
            | (uu____10352,FStar_Syntax_Syntax.Tm_abs (bs,uu____10354,_rc))
                ->
                let uu____10380 =
                  let uu____10381 =
                    let uu____10386 =
                      FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses]
                      uu____10386
                     in
                  FStar_All.pipe_right t uu____10381  in
                FStar_All.pipe_right uu____10380 (term_as_mlexpr g)
            | (uu____10393,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____10395 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  let uu____10396 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg uu____10395
                    [FStar_TypeChecker_Env.Inlining] head1 uu____10396
                   in
                let tm =
                  let uu____10408 =
                    let uu____10413 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____10414 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____10413 uu____10414  in
                  uu____10408 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____10423 ->
                let rec extract_app is_data uu____10476 uu____10477 restArgs
                  =
                  match (uu____10476, uu____10477) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____10558 =
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
                         (fun uu____10585  ->
                            let uu____10586 =
                              let uu____10588 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              let uu____10589 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____10588 uu____10589
                               in
                            let uu____10590 =
                              let uu____10592 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlty
                                uu____10592 t1
                               in
                            let uu____10593 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____10604)::uu____10605 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10586 uu____10590 uu____10593);
                       (match (restArgs, t1) with
                        | ([],uu____10639) ->
                            let app =
                              let uu____10655 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10655
                               in
                            (app, f, t1)
                        | ((arg,uu____10657)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10688 =
                              let uu____10693 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____10693, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10688 rest
                        | ((e0,uu____10705)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____10738 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____10738
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____10743 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____10743 with
                             | (e01,tInferred) ->
                                 let uu____10756 =
                                   let uu____10761 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____10761, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10756 rest)
                        | uu____10772 ->
                            let uu____10785 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____10785 with
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
                                  | uu____10857 ->
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
                let extract_app_maybe_projector is_data mlhead uu____10928
                  args1 =
                  match uu____10928 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10958)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____11042))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____11044,f',t3)) ->
                                 let uu____11082 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____11082 t3
                             | uu____11083 -> (args2, f1, t2)  in
                           let uu____11108 = remove_implicits args1 f t1  in
                           (match uu____11108 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____11164 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____11188 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____11196 ->
                      let uu____11197 =
                        let uu____11218 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____11218 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11257  ->
                                  let uu____11258 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____11260 =
                                    let uu____11262 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11262
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11263 =
                                    let uu____11265 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11265
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11266 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11258 uu____11260 uu____11263
                                    uu____11266);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11293 -> failwith "FIXME Ty"  in
                      (match uu____11197 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11369)::uu____11370 -> is_type g a
                             | uu____11397 -> false  in
                           let uu____11409 =
                             match vars with
                             | uu____11438::uu____11439 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11453 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____11459 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____11497 =
                                       FStar_List.map
                                         (fun uu____11509  ->
                                            match uu____11509 with
                                            | (x,uu____11517) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____11497, [])
                                   else
                                     (let uu____11540 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____11540 with
                                      | (prefix1,rest) ->
                                          let uu____11629 =
                                            FStar_List.map
                                              (fun uu____11641  ->
                                                 match uu____11641 with
                                                 | (x,uu____11649) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____11629, rest))
                                    in
                                 (match uu____11459 with
                                  | (provided_type_args,rest) ->
                                      let uu____11700 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____11709 ->
                                            let uu____11710 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11710 with
                                             | (head3,uu____11722,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____11724 ->
                                            let uu____11726 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11726 with
                                             | (head3,uu____11738,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____11741;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____11742;_}::[])
                                            ->
                                            let uu____11745 =
                                              instantiate_maybe_partial g
                                                head3 (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11745 with
                                             | (head4,uu____11757,t2) ->
                                                 let uu____11759 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____11759, t2))
                                        | uu____11762 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____11700 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____11409 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11829 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____11829,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11830 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11839 ->
                      let uu____11840 =
                        let uu____11861 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____11861 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11900  ->
                                  let uu____11901 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____11903 =
                                    let uu____11905 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11905
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11906 =
                                    let uu____11908 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11908
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11909 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11901 uu____11903 uu____11906
                                    uu____11909);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11936 -> failwith "FIXME Ty"  in
                      (match uu____11840 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____12012)::uu____12013 -> is_type g a
                             | uu____12040 -> false  in
                           let uu____12052 =
                             match vars with
                             | uu____12081::uu____12082 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____12096 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____12102 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____12140 =
                                       FStar_List.map
                                         (fun uu____12152  ->
                                            match uu____12152 with
                                            | (x,uu____12160) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____12140, [])
                                   else
                                     (let uu____12183 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____12183 with
                                      | (prefix1,rest) ->
                                          let uu____12272 =
                                            FStar_List.map
                                              (fun uu____12284  ->
                                                 match uu____12284 with
                                                 | (x,uu____12292) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____12272, rest))
                                    in
                                 (match uu____12102 with
                                  | (provided_type_args,rest) ->
                                      let uu____12343 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____12352 ->
                                            let uu____12353 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12353 with
                                             | (head3,uu____12365,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____12367 ->
                                            let uu____12369 =
                                              instantiate_maybe_partial g
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12369 with
                                             | (head3,uu____12381,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____12384;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____12385;_}::[])
                                            ->
                                            let uu____12388 =
                                              instantiate_maybe_partial g
                                                head3 (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12388 with
                                             | (head4,uu____12400,t2) ->
                                                 let uu____12402 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____12402, t2))
                                        | uu____12405 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____12343 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____12052 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12472 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____12472,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12473 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12482 ->
                      let uu____12483 = term_as_mlexpr g head2  in
                      (match uu____12483 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____12499 = is_type g t  in
                if uu____12499
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12510 =
                     let uu____12511 = FStar_Syntax_Util.un_uinst head1  in
                     uu____12511.FStar_Syntax_Syntax.n  in
                   match uu____12510 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12521 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____12521 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12530 -> extract_app_with_instantiations ())
                   | uu____12533 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____12536),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12601 =
                   let uu____12602 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                      in
                   maybe_reify_comp g uu____12602 c  in
                 term_as_mlty g uu____12601
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____12606 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____12606 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e') when
           (let uu____12638 = FStar_Syntax_Syntax.is_top_level [lb]  in
            Prims.op_Negation uu____12638) &&
             (let uu____12641 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs
                 in
              FStar_Util.is_some uu____12641)
           ->
           let b =
             let uu____12651 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                in
             (uu____12651, FStar_Pervasives_Native.None)  in
           let uu____12654 = FStar_Syntax_Subst.open_term [b] e'  in
           (match uu____12654 with
            | ((x,uu____12678)::uu____12679,body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str,uu____12708)::[]) ->
                      let uu____12733 =
                        let uu____12734 = FStar_Syntax_Subst.compress str  in
                        uu____12734.FStar_Syntax_Syntax.n  in
                      (match uu____12733 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s,uu____12740)) ->
                           let id1 =
                             let uu____12744 =
                               let uu____12750 =
                                 FStar_Syntax_Syntax.range_of_bv x  in
                               (s, uu____12750)  in
                             FStar_Ident.mk_ident uu____12744  in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id1;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             }  in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv  in
                           FStar_Pervasives_Native.Some bv1
                       | uu____12755 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                   in
                let remove_attr1 attrs =
                  let uu____12772 =
                    FStar_List.partition
                      (fun attr  ->
                         let uu____12784 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr]
                            in
                         FStar_Util.is_some uu____12784)
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match uu____12772 with
                  | (uu____12789,other_attrs) -> other_attrs  in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None  ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1789_12817 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1789_12817.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1789_12817.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1789_12817.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1789_12817.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1789_12817.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1789_12817.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      let rename =
                        let uu____12825 =
                          let uu____12826 =
                            let uu____12833 =
                              FStar_Syntax_Syntax.bv_to_name y  in
                            (x, uu____12833)  in
                          FStar_Syntax_Syntax.NT uu____12826  in
                        [uu____12825]  in
                      let body1 =
                        let uu____12839 =
                          FStar_Syntax_Subst.subst rename body  in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____12839
                         in
                      let lb1 =
                        let uu___1796_12855 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1796_12855.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1796_12855.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1796_12855.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1796_12855.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1796_12855.FStar_Syntax_Syntax.lbpos)
                        }  in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1)
                   in
                let top1 =
                  let uu___1800_12872 = top  in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1800_12872.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1800_12872.FStar_Syntax_Syntax.vars)
                  }  in
                term_as_mlexpr' g top1)
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____12895 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12911 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____12911
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____12926 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____12926  in
                   let lb1 =
                     let uu___1814_12928 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1814_12928.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1814_12928.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1814_12928.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1814_12928.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1814_12928.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1814_12928.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____12895 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____12953 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      let uu____12954 =
                        let uu____12955 =
                          let uu____12956 =
                            let uu____12960 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Pervasives_Native.fst uu____12960  in
                          let uu____12973 =
                            let uu____12977 =
                              let uu____12979 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Pervasives_Native.snd uu____12979  in
                            [uu____12977]  in
                          FStar_List.append uu____12956 uu____12973  in
                        FStar_Ident.lid_of_path uu____12955
                          FStar_Range.dummyRange
                         in
                      FStar_TypeChecker_Env.set_current_module uu____12953
                        uu____12954
                       in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let lbdef =
                              let uu____13006 = FStar_Options.ml_ish ()  in
                              if uu____13006
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____13018 =
                                   let uu____13019 =
                                     let uu____13020 =
                                       extraction_norm_steps ()  in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____13020
                                      in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____13019 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____13023 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____13023
                                 then
                                   ((let uu____13033 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____13033);
                                    (let a =
                                       let uu____13039 =
                                         let uu____13041 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____13041
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____13039 norm_call
                                        in
                                     a))
                                 else norm_call ())
                               in
                            let uu___1831_13048 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1831_13048.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1831_13048.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1831_13048.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1831_13048.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1831_13048.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1831_13048.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____13101 =
                  match uu____13101 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____13257  ->
                               match uu____13257 with
                               | (a,uu____13265) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     false) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____13272 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____13272 with
                       | (e1,ty) ->
                           let uu____13283 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____13283 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____13295 -> []  in
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
                let uu____13326 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____13423  ->
                         match uu____13423 with
                         | (env,lbs4) ->
                             let uu____13557 = lb  in
                             (match uu____13557 with
                              | (lbname,uu____13608,(t1,(uu____13610,polytype)),add_unit,uu____13613)
                                  ->
                                  let uu____13628 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____13628 with
                                   | (env1,nm,uu____13669) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____13326 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____13948 = term_as_mlexpr env_body e'1  in
                     (match uu____13948 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____13965 =
                              let uu____13968 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____13968  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13965
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____13981 =
                            let uu____13982 =
                              let uu____13983 =
                                let uu____13984 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____13984)  in
                              mk_MLE_Let top_level uu____13983 e'2  in
                            let uu____13993 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13982 uu____13993
                             in
                          (uu____13981, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____14032 = term_as_mlexpr g scrutinee  in
           (match uu____14032 with
            | (e,f_e,t_e) ->
                let uu____14048 = check_pats_for_ite pats  in
                (match uu____14048 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____14113 = term_as_mlexpr g then_e1  in
                            (match uu____14113 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____14129 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____14129 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____14145 =
                                        let uu____14156 =
                                          type_leq g t_then t_else  in
                                        if uu____14156
                                        then (t_else, no_lift)
                                        else
                                          (let uu____14177 =
                                             type_leq g t_else t_then  in
                                           if uu____14177
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____14145 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____14224 =
                                             let uu____14225 =
                                               let uu____14226 =
                                                 let uu____14235 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____14236 =
                                                   let uu____14239 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____14239
                                                    in
                                                 (e, uu____14235,
                                                   uu____14236)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____14226
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____14225
                                              in
                                           let uu____14242 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____14224, uu____14242,
                                             t_branch))))
                        | uu____14243 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____14261 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____14360 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____14360 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____14405 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____14405 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____14467 =
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
                                                   let uu____14490 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____14490 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____14467 with
                                              | (when_opt1,f_when) ->
                                                  let uu____14540 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____14540 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____14575 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14652 
                                                                 ->
                                                                 match uu____14652
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
                                                         uu____14575)))))
                               true)
                           in
                        match uu____14261 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14823  ->
                                      let uu____14824 =
                                        let uu____14826 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu____14826 e
                                         in
                                      let uu____14827 =
                                        let uu____14829 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu____14829 t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14824 uu____14827);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14855 =
                                   let uu____14856 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14856
                                    in
                                 (match uu____14855 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14863;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14865;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____14866;_}
                                      ->
                                      let uu____14869 =
                                        let uu____14870 =
                                          let uu____14871 =
                                            let uu____14878 =
                                              let uu____14881 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____14881]  in
                                            (fw, uu____14878)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14871
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14870
                                         in
                                      (uu____14869,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14885,uu____14886,(uu____14887,f_first,t_first))::rest
                                 ->
                                 let uu____14947 =
                                   FStar_List.fold_left
                                     (fun uu____14989  ->
                                        fun uu____14990  ->
                                          match (uu____14989, uu____14990)
                                          with
                                          | ((topt,f),(uu____15047,uu____15048,
                                                       (uu____15049,f_branch,t_branch)))
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
                                                    let uu____15105 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____15105
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____15112 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____15112
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
                                 (match uu____14947 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____15210  ->
                                                match uu____15210 with
                                                | (p,(wopt,uu____15239),
                                                   (b1,uu____15241,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____15260 -> b1
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
                                      let uu____15265 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____15265, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____15292 =
          let uu____15297 =
            let uu____15306 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_lid uu____15306 discName  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15297  in
        match uu____15292 with
        | (uu____15323,fstar_disc_type) ->
            let uu____15325 =
              let uu____15337 =
                let uu____15338 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____15338.FStar_Syntax_Syntax.n  in
              match uu____15337 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15353) ->
                  let binders1 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_15408  ->
                            match uu___2_15408 with
                            | (uu____15416,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15417)) ->
                                true
                            | uu____15422 -> false))
                     in
                  FStar_List.fold_right
                    (fun uu____15454  ->
                       fun uu____15455  ->
                         match uu____15455 with
                         | (g,vs) ->
                             let uu____15500 =
                               FStar_Extraction_ML_UEnv.new_mlident g  in
                             (match uu____15500 with
                              | (g1,v1) ->
                                  (g1,
                                    ((v1,
                                       FStar_Extraction_ML_Syntax.MLTY_Top)
                                    :: vs)))) binders1 (env, [])
              | uu____15546 -> failwith "Discriminator must be a function"
               in
            (match uu____15325 with
             | (g,wildcards) ->
                 let uu____15575 = FStar_Extraction_ML_UEnv.new_mlident g  in
                 (match uu____15575 with
                  | (g1,mlid) ->
                      let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let discrBody =
                        let uu____15588 =
                          let uu____15589 =
                            let uu____15601 =
                              let uu____15602 =
                                let uu____15603 =
                                  let uu____15618 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         targ)
                                      (FStar_Extraction_ML_Syntax.MLE_Name
                                         ([], mlid))
                                     in
                                  let uu____15624 =
                                    let uu____15635 =
                                      let uu____15644 =
                                        let uu____15645 =
                                          let uu____15652 =
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident
                                              constrName
                                             in
                                          (uu____15652,
                                            [FStar_Extraction_ML_Syntax.MLP_Wild])
                                           in
                                        FStar_Extraction_ML_Syntax.MLP_CTor
                                          uu____15645
                                         in
                                      let uu____15655 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_bool_ty)
                                          (FStar_Extraction_ML_Syntax.MLE_Const
                                             (FStar_Extraction_ML_Syntax.MLC_Bool
                                                true))
                                         in
                                      (uu____15644,
                                        FStar_Pervasives_Native.None,
                                        uu____15655)
                                       in
                                    let uu____15659 =
                                      let uu____15670 =
                                        let uu____15679 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.ml_bool_ty)
                                            (FStar_Extraction_ML_Syntax.MLE_Const
                                               (FStar_Extraction_ML_Syntax.MLC_Bool
                                                  false))
                                           in
                                        (FStar_Extraction_ML_Syntax.MLP_Wild,
                                          FStar_Pervasives_Native.None,
                                          uu____15679)
                                         in
                                      [uu____15670]  in
                                    uu____15635 :: uu____15659  in
                                  (uu____15618, uu____15624)  in
                                FStar_Extraction_ML_Syntax.MLE_Match
                                  uu____15603
                                 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                uu____15602
                               in
                            ((FStar_List.append wildcards [(mlid, targ)]),
                              uu____15601)
                             in
                          FStar_Extraction_ML_Syntax.MLE_Fun uu____15589  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty disc_ty)
                          uu____15588
                         in
                      let uu____15740 =
                        let uu____15741 =
                          let uu____15744 =
                            let uu____15745 =
                              FStar_Extraction_ML_UEnv.convIdent
                                discName.FStar_Ident.ident
                               in
                            {
                              FStar_Extraction_ML_Syntax.mllb_name =
                                uu____15745;
                              FStar_Extraction_ML_Syntax.mllb_tysc =
                                FStar_Pervasives_Native.None;
                              FStar_Extraction_ML_Syntax.mllb_add_unit =
                                false;
                              FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                              FStar_Extraction_ML_Syntax.mllb_meta = [];
                              FStar_Extraction_ML_Syntax.print_typ = false
                            }  in
                          [uu____15744]  in
                        (FStar_Extraction_ML_Syntax.NonRec, uu____15741)  in
                      FStar_Extraction_ML_Syntax.MLM_Let uu____15740))
  