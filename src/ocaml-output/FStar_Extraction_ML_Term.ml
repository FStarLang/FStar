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
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref Prims.int_zero  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1679 =
       let uu____1681 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____1681  in
     Prims.op_Hat x uu____1679)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1784 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1786 = FStar_Syntax_Util.is_fun e'  in
          if uu____1786
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1800 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1800 
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
      (let uu____1891 = FStar_List.hd l  in
       match uu____1891 with
       | (p1,w1,e1) ->
           let uu____1926 =
             let uu____1935 = FStar_List.tl l  in FStar_List.hd uu____1935
              in
           (match uu____1926 with
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
                 | uu____2019 -> def)))
  
let (instantiate_tyscheme :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  = fun s  -> fun args  -> FStar_Extraction_ML_Util.subst s args 
let (instantiate_maybe_partial :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mltyscheme ->
      FStar_Extraction_ML_Syntax.mlty Prims.list ->
        (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag
          * FStar_Extraction_ML_Syntax.mlty))
  =
  fun e  ->
    fun s  ->
      fun tyargs  ->
        let uu____2079 = s  in
        match uu____2079 with
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
                    let uu___365_2111 = e  in
                    {
                      FStar_Extraction_ML_Syntax.expr =
                        (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                      FStar_Extraction_ML_Syntax.mlty = ts;
                      FStar_Extraction_ML_Syntax.loc =
                        (uu___365_2111.FStar_Extraction_ML_Syntax.loc)
                    }  in
                  (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
            else
              if n_args < n_vars
              then
                (let extra_tyargs =
                   let uu____2126 = FStar_Util.first_N n_args vars  in
                   match uu____2126 with
                   | (uu____2140,rest_vars) ->
                       FStar_All.pipe_right rest_vars
                         (FStar_List.map
                            (fun uu____2161  ->
                               FStar_Extraction_ML_Syntax.MLTY_Erased))
                    in
                 let tyargs1 = FStar_List.append tyargs extra_tyargs  in
                 let ts = instantiate_tyscheme (vars, t) tyargs1  in
                 let tapp =
                   let uu___376_2168 = e  in
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                     FStar_Extraction_ML_Syntax.mlty = ts;
                     FStar_Extraction_ML_Syntax.loc =
                       (uu___376_2168.FStar_Extraction_ML_Syntax.loc)
                   }  in
                 let t1 =
                   FStar_List.fold_left
                     (fun out  ->
                        fun t1  ->
                          FStar_Extraction_ML_Syntax.MLTY_Fun
                            (t1, FStar_Extraction_ML_Syntax.E_PURE, out)) ts
                     extra_tyargs
                    in
                 let f =
                   let vs_ts =
                     FStar_List.map
                       (fun t2  ->
                          let uu____2193 = fresh "t"  in (uu____2193, t2))
                       extra_tyargs
                      in
                   FStar_All.pipe_left
                     (FStar_Extraction_ML_Syntax.with_ty t1)
                     (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, tapp))
                    in
                 (f, FStar_Extraction_ML_Syntax.E_PURE, t1))
              else
                failwith
                  "Impossible: instantiate_maybe_partial called with too many arguments"
  
let (eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun t  ->
    fun e  ->
      let uu____2224 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2224 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____2248  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____2262 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____2279  ->
                    match uu____2279 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____2262
                in
             let body =
               FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r)
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
      let uu____2310 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2310 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____2330 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____2330 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2334 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____2346  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____2357 =
               let uu____2358 =
                 let uu____2370 = body r  in (vs_ts, uu____2370)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____2358  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____2357)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____2389 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____2392 = FStar_Options.codegen ()  in
           uu____2392 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____2389 then e else eta_expand expect e
  
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
            | uu____2470 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____2525 =
              match uu____2525 with
              | (pat,w,b) ->
                  let uu____2549 = aux b ty1 expect1  in (pat, w, uu____2549)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____2556,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____2559,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____2591 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____2607 = type_leq g s0 t0  in
                if uu____2607
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____2613 =
                       let uu____2614 =
                         let uu____2615 =
                           let uu____2622 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____2622, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____2615  in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____2614  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____2613;
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
               (lbs,body),uu____2641,uu____2642) ->
                let uu____2655 =
                  let uu____2656 =
                    let uu____2667 = aux body ty1 expect1  in
                    (lbs, uu____2667)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____2656  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2655
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____2676,uu____2677) ->
                let uu____2698 =
                  let uu____2699 =
                    let uu____2714 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2714)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____2699  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2698
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____2754,uu____2755) ->
                let uu____2760 =
                  let uu____2761 =
                    let uu____2770 = aux b1 ty1 expect1  in
                    let uu____2771 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____2770, uu____2771)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____2761  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2760
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____2779,uu____2780)
                ->
                let uu____2783 = FStar_Util.prefix es  in
                (match uu____2783 with
                 | (prefix1,last1) ->
                     let uu____2796 =
                       let uu____2797 =
                         let uu____2800 =
                           let uu____2803 = aux last1 ty1 expect1  in
                           [uu____2803]  in
                         FStar_List.append prefix1 uu____2800  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____2797  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____2796)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____2806,uu____2807) ->
                let uu____2828 =
                  let uu____2829 =
                    let uu____2844 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2844)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____2829  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2828
            | uu____2881 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'Auu____2901 .
    'Auu____2901 ->
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
            let uu____2928 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____2928 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____2941 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____2949 ->
                     let uu____2950 =
                       let uu____2952 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____2953 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____2952 uu____2953  in
                     if uu____2950
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____2959  ->
                             let uu____2960 =
                               let uu____2962 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____2962 e
                                in
                             let uu____2963 =
                               let uu____2965 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____2965 ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____2960 uu____2963);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____2974  ->
                             let uu____2975 =
                               let uu____2977 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____2977 e
                                in
                             let uu____2978 =
                               let uu____2980 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____2980 ty1
                                in
                             let uu____2981 =
                               let uu____2983 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____2983 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____2975 uu____2978 uu____2981);
                        (let uu____2985 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand expect uu____2985)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____2997 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____2997 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____2999 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
  fun uu____3013  ->
    let uu____3014 = FStar_Options.use_nbe_for_extraction ()  in
    if uu____3014
    then extraction_norm_steps_nbe
    else extraction_norm_steps_core
  
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____3035 -> c
    | FStar_Syntax_Syntax.GTotal uu____3044 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____3080  ->
               match uu____3080 with
               | (uu____3095,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___540_3108 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___540_3108.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___540_3108.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___540_3108.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___540_3108.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___543_3112 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___543_3112.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___543_3112.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let maybe_reify_comp :
  'Auu____3124 .
    'Auu____3124 ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun g  ->
    fun env  ->
      fun c  ->
        let c1 = comp_no_args c  in
        let uu____3143 =
          let uu____3145 =
            let uu____3146 =
              FStar_All.pipe_right c1 FStar_Syntax_Util.comp_effect_name  in
            FStar_All.pipe_right uu____3146
              (FStar_TypeChecker_Env.norm_eff_name env)
             in
          FStar_All.pipe_right uu____3145
            (FStar_TypeChecker_Env.is_reifiable_effect env)
           in
        if uu____3143
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
      let arg_as_mlty g1 uu____3199 =
        match uu____3199 with
        | (a,uu____3207) ->
            let uu____3212 = is_type g1 a  in
            if uu____3212
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____3233 =
          let uu____3235 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____3235  in
        if uu____3233
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____3240 =
             let uu____3255 =
               let uu____3264 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
               FStar_TypeChecker_Env.lookup_lid uu____3264
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____3255 with
             | ((uu____3279,fvty),uu____3281) ->
                 let fvty1 =
                   let uu____3287 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1
                      in
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant] uu____3287 fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____3240 with
           | (formals,uu____3289) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3342 = FStar_Util.first_N n_args formals  in
                   match uu____3342 with
                   | (uu____3371,rest) ->
                       let uu____3405 =
                         FStar_List.map
                           (fun uu____3415  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____3405
                 else mlargs  in
               let nm =
                 let uu____3425 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____3425 with
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
        | FStar_Syntax_Syntax.Tm_type uu____3443 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3444 ->
            let uu____3445 =
              let uu____3447 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3447
               in
            failwith uu____3445
        | FStar_Syntax_Syntax.Tm_delayed uu____3450 ->
            let uu____3473 =
              let uu____3475 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3475
               in
            failwith uu____3473
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3478 =
              let uu____3480 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3480
               in
            failwith uu____3478
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3484 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____3484
        | FStar_Syntax_Syntax.Tm_constant uu____3485 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____3486 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____3493 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____3507) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3512;
               FStar_Syntax_Syntax.index = uu____3513;
               FStar_Syntax_Syntax.sort = t2;_},uu____3515)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3524) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3530,uu____3531) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____3604 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____3604 with
             | (bs1,c1) ->
                 let uu____3611 = binders_as_ml_binders env bs1  in
                 (match uu____3611 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let uu____3640 =
                          let uu____3641 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv env1  in
                          maybe_reify_comp env1 uu____3641 c1  in
                        translate_term_to_mlty env1 uu____3640  in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____3643 =
                        FStar_List.fold_right
                          (fun uu____3663  ->
                             fun uu____3664  ->
                               match (uu____3663, uu____3664) with
                               | ((uu____3687,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____3643 with | (uu____3702,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____3731 =
                let uu____3732 = FStar_Syntax_Util.un_uinst head1  in
                uu____3732.FStar_Syntax_Syntax.n  in
              match uu____3731 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____3763 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____3763
              | uu____3784 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____3787) ->
            let uu____3812 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____3812 with
             | (bs1,ty1) ->
                 let uu____3819 = binders_as_ml_binders env bs1  in
                 (match uu____3819 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____3847 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____3861 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____3893 ->
            let uu____3900 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____3900 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____3906 -> false  in
      let uu____3908 =
        let uu____3910 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Util.must_erase_for_extraction uu____3910 t0  in
      if uu____3908
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____3915 = is_top_ty mlt  in
         if uu____3915 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____3933 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____3989  ->
                fun b  ->
                  match uu____3989 with
                  | (ml_bs,env) ->
                      let uu____4035 = is_type_binder g b  in
                      if uu____4035
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____4061 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____4061, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____4082 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____4082 with
                         | (env1,b2,uu____4107) ->
                             let ml_b =
                               let uu____4116 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____4116, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____3933 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        let uu____4194 = extraction_norm_steps ()  in
        let uu____4195 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Normalize.normalize uu____4194 uu____4195 t0  in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____4214) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4217,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4221 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____4255 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4256 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4257 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4266 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____4294 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____4294 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____4301 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____4334 -> p))
      | uu____4337 -> p
  
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
                       (fun uu____4439  ->
                          let uu____4440 =
                            let uu____4442 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4442 t'
                             in
                          let uu____4443 =
                            let uu____4445 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Extraction_ML_Code.string_of_mlty
                              uu____4445 t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4440 uu____4443)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____4480 = FStar_Options.codegen ()  in
                uu____4480 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4485 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4498 =
                        let uu____4499 =
                          let uu____4500 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4500  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4499
                         in
                      (uu____4498, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        let uu____4522 =
                          let uu____4523 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                          uu____4523.FStar_TypeChecker_Env.dsenv  in
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          uu____4522 c sw FStar_Range.dummyRange
                         in
                      let uu____4524 = term_as_mlexpr g source_term  in
                      (match uu____4524 with
                       | (mlterm,uu____4536,mlty) -> (mlterm, mlty))
                   in
                (match uu____4485 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____4558 =
                         let uu____4559 =
                           let uu____4566 =
                             let uu____4569 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____4569; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____4566)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____4559  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____4558
                        in
                     let uu____4572 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____4572))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  let uu____4593 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_TcTerm.tc_constant uu____4593
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____4595 =
                  let uu____4604 =
                    let uu____4611 =
                      let uu____4612 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4612  in
                    (uu____4611, [])  in
                  FStar_Pervasives_Native.Some uu____4604  in
                let uu____4621 = ok mlty  in (g, uu____4595, uu____4621)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4634 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4634 with
                 | (g1,x1,uu____4662) ->
                     let uu____4665 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4665))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4703 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4703 with
                 | (g1,x1,uu____4731) ->
                     let uu____4734 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4734))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4770 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____4813 =
                  let uu____4822 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____4822 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____4831;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____4833;
                          FStar_Extraction_ML_Syntax.loc = uu____4834;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____4836;_}
                      -> (n1, ttys)
                  | uu____4843 -> failwith "Expected a constructor"  in
                (match uu____4813 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____4880 = FStar_Util.first_N nTyVars pats  in
                     (match uu____4880 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___831_4984  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____5015  ->
                                               match uu____5015 with
                                               | (p1,uu____5022) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5025,t) ->
                                                        term_as_mlty g t
                                                    | uu____5031 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5035 
                                                              ->
                                                              let uu____5036
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5036);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____5040 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____5040)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____5069 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____5106  ->
                                   match uu____5106 with
                                   | (p1,imp1) ->
                                       let uu____5128 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____5128 with
                                        | (g2,p2,uu____5159) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____5069 with
                           | (g1,tyMLPats) ->
                               let uu____5223 =
                                 FStar_Util.fold_map
                                   (fun uu____5288  ->
                                      fun uu____5289  ->
                                        match (uu____5288, uu____5289) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____5387 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____5447 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____5387 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____5518 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____5518 with
                                                  | (g3,p2,uu____5561) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____5223 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____5682 =
                                      let uu____5693 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5744  ->
                                                match uu___0_5744 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____5786 -> []))
                                         in
                                      FStar_All.pipe_right uu____5693
                                        FStar_List.split
                                       in
                                    (match uu____5682 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____5862 -> false  in
                                         let uu____5872 =
                                           let uu____5881 =
                                             let uu____5888 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____5891 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____5888, uu____5891)  in
                                           FStar_Pervasives_Native.Some
                                             uu____5881
                                            in
                                         (g2, uu____5872, pat_ty_compat))))))
  
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
            let uu____6023 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____6023 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____6086 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____6134 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____6134
             in
          let uu____6135 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____6135 with
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
          let rec eta_args more_args t =
            match t with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____6295,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____6299 =
                  let uu____6311 =
                    let uu____6321 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____6321)  in
                  uu____6311 :: more_args  in
                eta_args uu____6299 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6337,uu____6338)
                -> ((FStar_List.rev more_args), t)
            | uu____6363 ->
                let uu____6364 =
                  let uu____6366 =
                    let uu____6368 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g  in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu____6368
                      mlAppExpr
                     in
                  let uu____6369 =
                    let uu____6371 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g  in
                    FStar_Extraction_ML_Code.string_of_mlty uu____6371 t  in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6366 uu____6369
                   in
                failwith uu____6364
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____6405,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6442 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____6464 = eta_args [] residualType  in
            match uu____6464 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____6522 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____6522
                 | uu____6523 ->
                     let uu____6535 = FStar_List.unzip eargs  in
                     (match uu____6535 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____6581 =
                                   let uu____6582 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6582
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6581
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6592 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6596,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6600;
                FStar_Extraction_ML_Syntax.loc = uu____6601;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____6624 ->
                    let uu____6627 =
                      let uu____6634 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6634, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6627
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
                     FStar_Extraction_ML_Syntax.mlty = uu____6638;
                     FStar_Extraction_ML_Syntax.loc = uu____6639;_},uu____6640);
                FStar_Extraction_ML_Syntax.mlty = uu____6641;
                FStar_Extraction_ML_Syntax.loc = uu____6642;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____6669 ->
                    let uu____6672 =
                      let uu____6679 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6679, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6672
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6683;
                FStar_Extraction_ML_Syntax.loc = uu____6684;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6692 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6692
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6696;
                FStar_Extraction_ML_Syntax.loc = uu____6697;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6699)) ->
              let uu____6712 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6712
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6716;
                     FStar_Extraction_ML_Syntax.loc = uu____6717;_},uu____6718);
                FStar_Extraction_ML_Syntax.mlty = uu____6719;
                FStar_Extraction_ML_Syntax.loc = uu____6720;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6732 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6732
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6736;
                     FStar_Extraction_ML_Syntax.loc = uu____6737;_},uu____6738);
                FStar_Extraction_ML_Syntax.mlty = uu____6739;
                FStar_Extraction_ML_Syntax.loc = uu____6740;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6742)) ->
              let uu____6759 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6759
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____6765 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6765
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6769)) ->
              let uu____6778 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6778
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6782;
                FStar_Extraction_ML_Syntax.loc = uu____6783;_},uu____6784),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6791 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6791
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6795;
                FStar_Extraction_ML_Syntax.loc = uu____6796;_},uu____6797),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6798)) ->
              let uu____6811 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6811
          | uu____6814 -> mlAppExpr
  
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
        | uu____6845 -> (ml_e, tag)
  
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
      let maybe_generalize uu____6906 =
        match uu____6906 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____6927;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____6932;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____7013 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____7090 =
              let uu____7092 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Util.must_erase_for_extraction uu____7092
                lbtyp1
               in
            if uu____7090
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____7177 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____7177 (is_type_binder g) ->
                   let uu____7199 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____7199 with
                    | (bs1,c1) ->
                        let uu____7225 =
                          let uu____7238 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____7284 = is_type_binder g x  in
                                 Prims.op_Negation uu____7284) bs1
                             in
                          match uu____7238 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____7411 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____7411)
                           in
                        (match uu____7225 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____7473 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____7473
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____7522 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____7522 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7574 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____7574 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7677  ->
                                                       fun uu____7678  ->
                                                         match (uu____7677,
                                                                 uu____7678)
                                                         with
                                                         | ((x,uu____7704),
                                                            (y,uu____7706))
                                                             ->
                                                             let uu____7727 =
                                                               let uu____7734
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____7734)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7727)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____7751  ->
                                                       match uu____7751 with
                                                       | (a,uu____7759) ->
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
                                                let uu____7770 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____7789  ->
                                                          match uu____7789
                                                          with
                                                          | (x,uu____7798) ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____7770, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____7814 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____7814)
                                                      ||
                                                      (let uu____7817 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____7817)
                                                | uu____7819 -> false  in
                                              let rest_args1 =
                                                if add_unit
                                                then unit_binder :: rest_args
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____7881 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____7900  ->
                                           match uu____7900 with
                                           | (a,uu____7908) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____7919 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____7938  ->
                                              match uu____7938 with
                                              | (x,uu____7947) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____7919, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____7991  ->
                                            match uu____7991 with
                                            | (bv,uu____7999) ->
                                                let uu____8004 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8004
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____8034 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8047  ->
                                           match uu____8047 with
                                           | (a,uu____8055) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8066 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8085  ->
                                              match uu____8085 with
                                              | (x,uu____8094) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____8066, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8138  ->
                                            match uu____8138 with
                                            | (bv,uu____8146) ->
                                                let uu____8151 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8151
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
                              | FStar_Syntax_Syntax.Tm_name uu____8181 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8194  ->
                                           match uu____8194 with
                                           | (a,uu____8202) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8213 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8232  ->
                                              match uu____8232 with
                                              | (x,uu____8241) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____8213, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8285  ->
                                            match uu____8285 with
                                            | (bv,uu____8293) ->
                                                let uu____8298 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8298
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
                              | uu____8328 -> err_value_restriction lbdef1)))
               | uu____8348 -> no_gen ())
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
           fun uu____8499  ->
             match uu____8499 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____8560 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____8560 with
                  | (env1,uu____8577,exp_binding) ->
                      let uu____8581 =
                        let uu____8586 = FStar_Util.right lbname  in
                        (uu____8586, exp_binding)  in
                      (env1, uu____8581))) g lbs1
  
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
            (fun uu____8652  ->
               let uu____8653 = FStar_Syntax_Print.term_to_string e  in
               let uu____8655 =
                 let uu____8657 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g  in
                 FStar_Extraction_ML_Code.string_of_mlty uu____8657 ty  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____8653
                 uu____8655);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____8663) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8664 ->
               let uu____8669 = term_as_mlexpr g e  in
               (match uu____8669 with
                | (ml_e,tag,t) ->
                    let uu____8683 = maybe_promote_effect ml_e tag t  in
                    (match uu____8683 with
                     | (ml_e1,tag1) ->
                         let uu____8694 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____8694
                         then
                           let uu____8701 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____8701, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____8708 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____8708, ty)
                            | uu____8709 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____8717 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____8717, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____8720 = term_as_mlexpr' g e  in
      match uu____8720 with
      | (e1,f,t) ->
          let uu____8736 = maybe_promote_effect e1 f t  in
          (match uu____8736 with | (e2,f1) -> (e2, f1, t))

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
           let uu____8761 =
             let uu____8763 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____8765 = FStar_Syntax_Print.tag_of_term top  in
             let uu____8767 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____8763 uu____8765 uu____8767
              in
           FStar_Util.print_string uu____8761);
      (let is_match t =
         let uu____8777 =
           let uu____8778 =
             let uu____8781 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____8781 FStar_Syntax_Util.unascribe  in
           uu____8778.FStar_Syntax_Syntax.n  in
         match uu____8777 with
         | FStar_Syntax_Syntax.Tm_match uu____8785 -> true
         | uu____8809 -> false  in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____8828  ->
              match uu____8828 with
              | (t,uu____8837) ->
                  let uu____8842 =
                    let uu____8843 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
                    uu____8843.FStar_Syntax_Syntax.n  in
                  (match uu____8842 with
                   | FStar_Syntax_Syntax.Tm_name uu____8849 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____8851 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____8853 -> true
                   | uu____8855 -> false))
          in
       let apply_to_match_branches head1 args =
         let uu____8894 =
           let uu____8895 =
             let uu____8898 =
               FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____8898 FStar_Syntax_Util.unascribe  in
           uu____8895.FStar_Syntax_Syntax.n  in
         match uu____8894 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee,branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____9022  ->
                       match uu____9022 with
                       | (pat,when_opt,body) ->
                           (pat, when_opt,
                             (let uu___1298_9079 = body  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1298_9079.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1298_9079.FStar_Syntax_Syntax.vars)
                              }))))
                in
             let uu___1301_9094 = head1  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1301_9094.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1301_9094.FStar_Syntax_Syntax.vars)
             }
         | uu____9115 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match"
          in
       let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9126 =
             let uu____9128 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9128
              in
           failwith uu____9126
       | FStar_Syntax_Syntax.Tm_delayed uu____9137 ->
           let uu____9160 =
             let uu____9162 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9162
              in
           failwith uu____9160
       | FStar_Syntax_Syntax.Tm_uvar uu____9171 ->
           let uu____9184 =
             let uu____9186 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9186
              in
           failwith uu____9184
       | FStar_Syntax_Syntax.Tm_bvar uu____9195 ->
           let uu____9196 =
             let uu____9198 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9198
              in
           failwith uu____9196
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9208 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____9208
       | FStar_Syntax_Syntax.Tm_type uu____9209 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9210 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9217 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____9233;_})
           ->
           let uu____9246 =
             let uu____9247 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9247  in
           (match uu____9246 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9254;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9256;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9257;_} ->
                let uu____9260 =
                  let uu____9261 =
                    let uu____9262 =
                      let uu____9269 =
                        let uu____9272 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____9272]  in
                      (fw, uu____9269)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9262  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9261
                   in
                (uu____9260, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9290 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____9290 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9298 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____9298 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____9309 =
                         let uu____9316 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____9316
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____9309 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____9324 =
                         let uu____9335 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____9335]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9324
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9362 =
                    let uu____9369 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____9369 tv  in
                  uu____9362 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____9377 =
                    let uu____9388 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____9388]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9377
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____9415)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9448 =
                  let uu____9455 =
                    let uu____9464 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.effect_decl_opt uu____9464 m  in
                  FStar_Util.must uu____9455  in
                (match uu____9448 with
                 | (ed,qualifiers) ->
                     let uu____9483 =
                       let uu____9485 =
                         let uu____9487 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                         FStar_TypeChecker_Env.is_reifiable_effect uu____9487
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____9485  in
                     if uu____9483
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9504 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9506) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9512) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9518 =
             let uu____9525 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_TcTerm.type_of_tot_term uu____9525 t  in
           (match uu____9518 with
            | (uu____9532,ty,uu____9534) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____9536 =
                  let uu____9537 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9537  in
                (uu____9536, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9538 ->
           let uu____9539 = is_type g t  in
           if uu____9539
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9550 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____9550 with
              | (FStar_Util.Inl uu____9563,uu____9564) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9569;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9572;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____9590 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____9590, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9591 -> instantiate_maybe_partial x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9593 = is_type g t  in
           if uu____9593
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9604 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____9604 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9613;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9616;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9624  ->
                        let uu____9625 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____9627 =
                          let uu____9629 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            uu____9629 x
                           in
                        let uu____9630 =
                          let uu____9632 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlty uu____9632
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9625 uu____9627 uu____9630);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____9644 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____9644, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9645 -> instantiate_maybe_partial x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____9673 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____9673 with
            | (bs1,body1) ->
                let uu____9686 = binders_as_ml_binders g bs1  in
                (match uu____9686 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9722 =
                             let uu____9724 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Env.is_reifiable_rc uu____9724
                               rc
                              in
                           if uu____9722
                           then
                             let uu____9726 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Util.reify_body uu____9726
                               [FStar_TypeChecker_Env.Inlining] body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9732  ->
                                 let uu____9733 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9733);
                            body1)
                        in
                     let uu____9736 = term_as_mlexpr env body2  in
                     (match uu____9736 with
                      | (ml_body,f,t1) ->
                          let uu____9752 =
                            FStar_List.fold_right
                              (fun uu____9772  ->
                                 fun uu____9773  ->
                                   match (uu____9772, uu____9773) with
                                   | ((uu____9796,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____9752 with
                           | (f1,tfun) ->
                               let uu____9819 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____9819, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____9827;
              FStar_Syntax_Syntax.vars = uu____9828;_},(a1,uu____9830)::[])
           ->
           let ty =
             let uu____9870 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____9870  in
           let uu____9871 =
             let uu____9872 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____9872
              in
           (uu____9871, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____9873;
              FStar_Syntax_Syntax.vars = uu____9874;_},(t1,uu____9876)::
            (r,uu____9878)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____9933);
              FStar_Syntax_Syntax.pos = uu____9934;
              FStar_Syntax_Syntax.vars = uu____9935;_},uu____9936)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (is_match head1) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____9995 =
             FStar_All.pipe_right args (apply_to_match_branches head1)  in
           FStar_All.pipe_right uu____9995 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_10049  ->
                        match uu___1_10049 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____10052 -> false)))
              in
           let uu____10054 =
             let uu____10059 =
               let uu____10060 =
                 let uu____10063 =
                   FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
                 FStar_All.pipe_right uu____10063 FStar_Syntax_Util.unascribe
                  in
               uu____10060.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____10059)  in
           (match uu____10054 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____10072,uu____10073) ->
                let t1 =
                  let uu____10087 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Iota;
                    FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.AllowUnboundUniverses] uu____10087
                    t
                   in
                term_as_mlexpr g t1
            | (uu____10088,FStar_Syntax_Syntax.Tm_abs (bs,uu____10090,_rc))
                ->
                let uu____10116 =
                  let uu____10117 =
                    let uu____10122 =
                      FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses]
                      uu____10122
                     in
                  FStar_All.pipe_right t uu____10117  in
                FStar_All.pipe_right uu____10116 (term_as_mlexpr g)
            | (uu____10129,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____10131 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  let uu____10132 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg uu____10131
                    [FStar_TypeChecker_Env.Inlining] head1 uu____10132
                   in
                let tm =
                  let uu____10144 =
                    let uu____10149 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____10150 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____10149 uu____10150  in
                  uu____10144 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____10159 ->
                let rec extract_app is_data uu____10212 uu____10213 restArgs
                  =
                  match (uu____10212, uu____10213) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____10294 =
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
                         (fun uu____10321  ->
                            let uu____10322 =
                              let uu____10324 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              let uu____10325 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____10324 uu____10325
                               in
                            let uu____10326 =
                              let uu____10328 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlty
                                uu____10328 t1
                               in
                            let uu____10329 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____10340)::uu____10341 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10322 uu____10326 uu____10329);
                       (match (restArgs, t1) with
                        | ([],uu____10375) ->
                            let app =
                              let uu____10391 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10391
                               in
                            (app, f, t1)
                        | ((arg,uu____10393)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10424 =
                              let uu____10429 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____10429, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10424 rest
                        | ((e0,uu____10441)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____10474 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____10474
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____10479 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____10479 with
                             | (e01,tInferred) ->
                                 let uu____10492 =
                                   let uu____10497 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____10497, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10492 rest)
                        | uu____10508 ->
                            let uu____10521 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____10521 with
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
                                  | uu____10593 ->
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
                let extract_app_maybe_projector is_data mlhead uu____10664
                  args1 =
                  match uu____10664 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10694)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10778))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____10780,f',t3)) ->
                                 let uu____10818 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____10818 t3
                             | uu____10819 -> (args2, f1, t2)  in
                           let uu____10844 = remove_implicits args1 f t1  in
                           (match uu____10844 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____10900 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____10924 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____10932 ->
                      let uu____10933 =
                        let uu____10954 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____10954 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____10993  ->
                                  let uu____10994 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____10996 =
                                    let uu____10998 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____10998
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____10999 =
                                    let uu____11001 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11001
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11002 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____10994 uu____10996 uu____10999
                                    uu____11002);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11029 -> failwith "FIXME Ty"  in
                      (match uu____10933 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11105)::uu____11106 -> is_type g a
                             | uu____11133 -> false  in
                           let uu____11145 =
                             match vars with
                             | uu____11174::uu____11175 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11189 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____11195 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____11233 =
                                       FStar_List.map
                                         (fun uu____11245  ->
                                            match uu____11245 with
                                            | (x,uu____11253) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____11233, [])
                                   else
                                     (let uu____11276 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____11276 with
                                      | (prefix1,rest) ->
                                          let uu____11365 =
                                            FStar_List.map
                                              (fun uu____11377  ->
                                                 match uu____11377 with
                                                 | (x,uu____11385) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____11365, rest))
                                    in
                                 (match uu____11195 with
                                  | (provided_type_args,rest) ->
                                      let uu____11436 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____11445 ->
                                            let uu____11446 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11446 with
                                             | (head3,uu____11458,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____11460 ->
                                            let uu____11462 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11462 with
                                             | (head3,uu____11474,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____11477;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____11478;_}::[])
                                            ->
                                            let uu____11481 =
                                              instantiate_maybe_partial head3
                                                (vars, t1) provided_type_args
                                               in
                                            (match uu____11481 with
                                             | (head4,uu____11493,t2) ->
                                                 let uu____11495 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____11495, t2))
                                        | uu____11498 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____11436 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____11145 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11565 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____11565,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11566 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11575 ->
                      let uu____11576 =
                        let uu____11597 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____11597 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11636  ->
                                  let uu____11637 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____11639 =
                                    let uu____11641 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11641
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11642 =
                                    let uu____11644 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11644
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11645 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11637 uu____11639 uu____11642
                                    uu____11645);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11672 -> failwith "FIXME Ty"  in
                      (match uu____11576 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11748)::uu____11749 -> is_type g a
                             | uu____11776 -> false  in
                           let uu____11788 =
                             match vars with
                             | uu____11817::uu____11818 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11832 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____11838 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____11876 =
                                       FStar_List.map
                                         (fun uu____11888  ->
                                            match uu____11888 with
                                            | (x,uu____11896) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____11876, [])
                                   else
                                     (let uu____11919 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____11919 with
                                      | (prefix1,rest) ->
                                          let uu____12008 =
                                            FStar_List.map
                                              (fun uu____12020  ->
                                                 match uu____12020 with
                                                 | (x,uu____12028) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____12008, rest))
                                    in
                                 (match uu____11838 with
                                  | (provided_type_args,rest) ->
                                      let uu____12079 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____12088 ->
                                            let uu____12089 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12089 with
                                             | (head3,uu____12101,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____12103 ->
                                            let uu____12105 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12105 with
                                             | (head3,uu____12117,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____12120;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____12121;_}::[])
                                            ->
                                            let uu____12124 =
                                              instantiate_maybe_partial head3
                                                (vars, t1) provided_type_args
                                               in
                                            (match uu____12124 with
                                             | (head4,uu____12136,t2) ->
                                                 let uu____12138 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____12138, t2))
                                        | uu____12141 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____12079 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____11788 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12208 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____12208,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12209 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12218 ->
                      let uu____12219 = term_as_mlexpr g head2  in
                      (match uu____12219 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____12235 = is_type g t  in
                if uu____12235
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12246 =
                     let uu____12247 = FStar_Syntax_Util.un_uinst head1  in
                     uu____12247.FStar_Syntax_Syntax.n  in
                   match uu____12246 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12257 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____12257 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12266 -> extract_app_with_instantiations ())
                   | uu____12269 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____12272),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12337 =
                   let uu____12338 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                      in
                   maybe_reify_comp g uu____12338 c  in
                 term_as_mlty g uu____12337
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____12342 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____12342 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e') when
           (let uu____12374 = FStar_Syntax_Syntax.is_top_level [lb]  in
            Prims.op_Negation uu____12374) &&
             (let uu____12377 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs
                 in
              FStar_Util.is_some uu____12377)
           ->
           let b =
             let uu____12387 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                in
             (uu____12387, FStar_Pervasives_Native.None)  in
           let uu____12390 = FStar_Syntax_Subst.open_term [b] e'  in
           (match uu____12390 with
            | ((x,uu____12414)::uu____12415,body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str,uu____12444)::[]) ->
                      let uu____12469 =
                        let uu____12470 = FStar_Syntax_Subst.compress str  in
                        uu____12470.FStar_Syntax_Syntax.n  in
                      (match uu____12469 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s,uu____12476)) ->
                           let id1 =
                             let uu____12480 =
                               let uu____12486 =
                                 FStar_Syntax_Syntax.range_of_bv x  in
                               (s, uu____12486)  in
                             FStar_Ident.mk_ident uu____12480  in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id1;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             }  in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv  in
                           FStar_Pervasives_Native.Some bv1
                       | uu____12491 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                   in
                let remove_attr1 attrs =
                  let uu____12508 =
                    FStar_List.partition
                      (fun attr  ->
                         let uu____12520 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr]
                            in
                         FStar_Util.is_some uu____12520)
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match uu____12508 with
                  | (uu____12525,other_attrs) -> other_attrs  in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None  ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1769_12553 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1769_12553.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1769_12553.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1769_12553.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1769_12553.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1769_12553.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1769_12553.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      let rename =
                        let uu____12561 =
                          let uu____12562 =
                            let uu____12569 =
                              FStar_Syntax_Syntax.bv_to_name y  in
                            (x, uu____12569)  in
                          FStar_Syntax_Syntax.NT uu____12562  in
                        [uu____12561]  in
                      let body1 =
                        let uu____12575 =
                          FStar_Syntax_Subst.subst rename body  in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____12575
                         in
                      let lb1 =
                        let uu___1776_12591 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1776_12591.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1776_12591.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1776_12591.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1776_12591.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1776_12591.FStar_Syntax_Syntax.lbpos)
                        }  in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1)
                   in
                let top1 =
                  let uu___1780_12608 = top  in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1780_12608.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1780_12608.FStar_Syntax_Syntax.vars)
                  }  in
                term_as_mlexpr' g top1)
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____12631 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12647 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____12647
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____12662 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____12662  in
                   let lb1 =
                     let uu___1794_12664 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1794_12664.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1794_12664.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1794_12664.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1794_12664.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1794_12664.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1794_12664.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____12631 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____12689 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      let uu____12690 =
                        let uu____12691 =
                          let uu____12692 =
                            let uu____12696 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Pervasives_Native.fst uu____12696  in
                          let uu____12709 =
                            let uu____12713 =
                              let uu____12715 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Pervasives_Native.snd uu____12715  in
                            [uu____12713]  in
                          FStar_List.append uu____12692 uu____12709  in
                        FStar_Ident.lid_of_path uu____12691
                          FStar_Range.dummyRange
                         in
                      FStar_TypeChecker_Env.set_current_module uu____12689
                        uu____12690
                       in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let lbdef =
                              let uu____12742 = FStar_Options.ml_ish ()  in
                              if uu____12742
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____12754 =
                                   let uu____12755 =
                                     let uu____12756 =
                                       extraction_norm_steps ()  in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____12756
                                      in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____12755 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____12759 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____12759
                                 then
                                   ((let uu____12769 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____12769);
                                    (let a =
                                       let uu____12775 =
                                         let uu____12777 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____12777
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____12775 norm_call
                                        in
                                     a))
                                 else norm_call ())
                               in
                            let uu___1811_12784 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1811_12784.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1811_12784.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1811_12784.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1811_12784.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1811_12784.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1811_12784.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____12837 =
                  match uu____12837 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____12993  ->
                               match uu____12993 with
                               | (a,uu____13001) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____13007 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____13007 with
                       | (e1,ty) ->
                           let uu____13018 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____13018 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____13030 -> []  in
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
                let uu____13061 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____13158  ->
                         match uu____13158 with
                         | (env,lbs4) ->
                             let uu____13292 = lb  in
                             (match uu____13292 with
                              | (lbname,uu____13343,(t1,(uu____13345,polytype)),add_unit,uu____13348)
                                  ->
                                  let uu____13363 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____13363 with
                                   | (env1,nm,uu____13404) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____13061 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____13683 = term_as_mlexpr env_body e'1  in
                     (match uu____13683 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____13700 =
                              let uu____13703 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____13703  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13700
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____13716 =
                            let uu____13717 =
                              let uu____13718 =
                                let uu____13719 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____13719)  in
                              mk_MLE_Let top_level uu____13718 e'2  in
                            let uu____13728 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13717 uu____13728
                             in
                          (uu____13716, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____13767 = term_as_mlexpr g scrutinee  in
           (match uu____13767 with
            | (e,f_e,t_e) ->
                let uu____13783 = check_pats_for_ite pats  in
                (match uu____13783 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____13848 = term_as_mlexpr g then_e1  in
                            (match uu____13848 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____13864 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____13864 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____13880 =
                                        let uu____13891 =
                                          type_leq g t_then t_else  in
                                        if uu____13891
                                        then (t_else, no_lift)
                                        else
                                          (let uu____13912 =
                                             type_leq g t_else t_then  in
                                           if uu____13912
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____13880 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____13959 =
                                             let uu____13960 =
                                               let uu____13961 =
                                                 let uu____13970 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____13971 =
                                                   let uu____13974 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____13974
                                                    in
                                                 (e, uu____13970,
                                                   uu____13971)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____13961
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____13960
                                              in
                                           let uu____13977 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____13959, uu____13977,
                                             t_branch))))
                        | uu____13978 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____13996 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____14095 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____14095 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____14140 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____14140 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____14202 =
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
                                                   let uu____14225 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____14225 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____14202 with
                                              | (when_opt1,f_when) ->
                                                  let uu____14275 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____14275 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____14310 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14387 
                                                                 ->
                                                                 match uu____14387
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
                                                         uu____14310)))))
                               true)
                           in
                        match uu____13996 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14558  ->
                                      let uu____14559 =
                                        let uu____14561 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu____14561 e
                                         in
                                      let uu____14562 =
                                        let uu____14564 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu____14564 t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14559 uu____14562);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14590 =
                                   let uu____14591 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14591
                                    in
                                 (match uu____14590 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14598;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14600;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____14601;_}
                                      ->
                                      let uu____14604 =
                                        let uu____14605 =
                                          let uu____14606 =
                                            let uu____14613 =
                                              let uu____14616 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____14616]  in
                                            (fw, uu____14613)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14606
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14605
                                         in
                                      (uu____14604,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14620,uu____14621,(uu____14622,f_first,t_first))::rest
                                 ->
                                 let uu____14682 =
                                   FStar_List.fold_left
                                     (fun uu____14724  ->
                                        fun uu____14725  ->
                                          match (uu____14724, uu____14725)
                                          with
                                          | ((topt,f),(uu____14782,uu____14783,
                                                       (uu____14784,f_branch,t_branch)))
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
                                                    let uu____14840 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____14840
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____14847 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____14847
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
                                 (match uu____14682 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____14945  ->
                                                match uu____14945 with
                                                | (p,(wopt,uu____14974),
                                                   (b1,uu____14976,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____14995 -> b1
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
                                      let uu____15000 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____15000, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____15027 =
          let uu____15032 =
            let uu____15041 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_lid uu____15041 discName  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15032  in
        match uu____15027 with
        | (uu____15058,fstar_disc_type) ->
            let wildcards =
              let uu____15068 =
                let uu____15069 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____15069.FStar_Syntax_Syntax.n  in
              match uu____15068 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15080) ->
                  let uu____15101 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_15135  ->
                            match uu___2_15135 with
                            | (uu____15143,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15144)) ->
                                true
                            | uu____15149 -> false))
                     in
                  FStar_All.pipe_right uu____15101
                    (FStar_List.map
                       (fun uu____15185  ->
                          let uu____15192 = fresh "_"  in
                          (uu____15192, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____15196 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____15211 =
                let uu____15212 =
                  let uu____15224 =
                    let uu____15225 =
                      let uu____15226 =
                        let uu____15241 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____15247 =
                          let uu____15258 =
                            let uu____15267 =
                              let uu____15268 =
                                let uu____15275 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____15275,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____15268
                               in
                            let uu____15278 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____15267, FStar_Pervasives_Native.None,
                              uu____15278)
                             in
                          let uu____15282 =
                            let uu____15293 =
                              let uu____15302 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____15302)
                               in
                            [uu____15293]  in
                          uu____15258 :: uu____15282  in
                        (uu____15241, uu____15247)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____15226  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____15225
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____15224)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____15212  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____15211
               in
            let uu____15363 =
              let uu____15364 =
                let uu____15367 =
                  let uu____15368 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____15368;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____15367]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____15364)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____15363
  