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
  'uuuuuu77 .
    FStar_Ident.ident Prims.list ->
      'uuuuuu77 Prims.list -> (Prims.string * 'uuuuuu77) Prims.list
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
  'uuuuuu123 .
    FStar_Range.range ->
      (FStar_Errors.raw_error * Prims.string) -> 'uuuuuu123
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_ill_typed_application :
  'uuuuuu159 'uuuuuu160 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'uuuuuu159) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'uuuuuu160
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
                  FStar_Extraction_ML_Code.string_of_mlexpr
                    env.FStar_Extraction_ML_UEnv.currentModule mlhead
                   in
                let uu____210 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____212 =
                  let uu____214 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____235  ->
                            match uu____235 with
                            | (x,uu____242) ->
                                FStar_Syntax_Print.term_to_string x))
                     in
                  FStar_All.pipe_right uu____214 (FStar_String.concat " ")
                   in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____206 uu____208 uu____210 uu____212
                 in
              (FStar_Errors.Fatal_IllTyped, uu____204)  in
            fail t.FStar_Syntax_Syntax.pos uu____198
  
let err_ill_typed_erasure :
  'uuuuuu259 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'uuuuuu259
  =
  fun env  ->
    fun pos  ->
      fun ty  ->
        let uu____275 =
          let uu____281 =
            let uu____283 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty
               in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____283
             in
          (FStar_Errors.Fatal_IllTyped, uu____281)  in
        fail pos uu____275
  
let err_value_restriction :
  'uuuuuu292 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'uuuuuu292
  =
  fun t  ->
    let uu____302 =
      let uu____308 =
        let uu____310 = FStar_Syntax_Print.tag_of_term t  in
        let uu____312 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____310 uu____312
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____308)  in
    fail t.FStar_Syntax_Syntax.pos uu____302
  
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
            let uu____346 =
              let uu____352 =
                let uu____354 = FStar_Syntax_Print.term_to_string t  in
                let uu____356 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____358 = FStar_Extraction_ML_Util.eff_to_string f0  in
                let uu____360 = FStar_Extraction_ML_Util.eff_to_string f1  in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____354 uu____356 uu____358 uu____360
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____352)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____346
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.of_int (20))  in
  let rec delta_norm_eff g l =
    let uu____388 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____388 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____393 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.env_tcenv
              [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____393 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____404,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____414 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____414
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____419 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____419
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.env_tcenv l1
               in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____445 =
                  FStar_TypeChecker_Env.is_reifiable_effect
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    ed.FStar_Syntax_Syntax.mname
                   in
                if uu____445
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____469 =
        let uu____470 = FStar_Syntax_Subst.compress t1  in
        uu____470.FStar_Syntax_Syntax.n  in
      match uu____469 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____476 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____501 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____530 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____540 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____540
      | FStar_Syntax_Syntax.Tm_uvar uu____541 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____555 -> false
      | FStar_Syntax_Syntax.Tm_name uu____557 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____559 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____567 -> false
      | FStar_Syntax_Syntax.Tm_type uu____569 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____571,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let topt =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant]
              env.FStar_Extraction_ML_UEnv.env_tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match topt with
           | FStar_Pervasives_Native.None  -> false
           | FStar_Pervasives_Native.Some (uu____607,t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____613 ->
          let uu____630 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____630 with | (head1,uu____649) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____675) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____681) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____686,body,uu____688) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____713,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____733,branches) ->
          (match branches with
           | (uu____772,uu____773,e)::uu____775 -> is_arity env e
           | uu____822 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____854 ->
          let uu____877 =
            let uu____879 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____879  in
          failwith uu____877
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____883 =
            let uu____885 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____885  in
          failwith uu____883
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____890 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____890
      | FStar_Syntax_Syntax.Tm_constant uu____891 -> false
      | FStar_Syntax_Syntax.Tm_type uu____893 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____895 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____903 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____922;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____923;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____924;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____926;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____927;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____928;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____929;_},s)
          ->
          let uu____978 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____978
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____979;
            FStar_Syntax_Syntax.index = uu____980;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____985;
            FStar_Syntax_Syntax.index = uu____986;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____992,uu____993) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1035) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1042) ->
          let uu____1067 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____1067 with
           | (uu____1073,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____1093 =
            let uu____1098 =
              let uu____1099 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1099]  in
            FStar_Syntax_Subst.open_term uu____1098 body  in
          (match uu____1093 with
           | (uu____1119,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1121,lbs),body) ->
          let uu____1141 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____1141 with
           | (uu____1149,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1155,branches) ->
          (match branches with
           | b::uu____1195 ->
               let uu____1240 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1240 with
                | (uu____1242,uu____1243,e) -> is_type_aux env e)
           | uu____1261 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1279 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1288) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1294) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1335  ->
           let uu____1336 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1338 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1336
             uu____1338);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1347  ->
            if b
            then
              let uu____1349 = FStar_Syntax_Print.term_to_string t  in
              let uu____1351 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1349
                uu____1351
            else
              (let uu____1356 = FStar_Syntax_Print.term_to_string t  in
               let uu____1358 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1356 uu____1358));
       b)
  
let is_type_binder :
  'uuuuuu1368 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu1368) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1395 =
      let uu____1396 = FStar_Syntax_Subst.compress t  in
      uu____1396.FStar_Syntax_Syntax.n  in
    match uu____1395 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1400;
          FStar_Syntax_Syntax.fv_delta = uu____1401;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1403;
          FStar_Syntax_Syntax.fv_delta = uu____1404;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1405);_}
        -> true
    | uu____1413 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1422 =
      let uu____1423 = FStar_Syntax_Subst.compress t  in
      uu____1423.FStar_Syntax_Syntax.n  in
    match uu____1422 with
    | FStar_Syntax_Syntax.Tm_constant uu____1427 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1429 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1431 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1433 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1479 = is_constructor head1  in
        if uu____1479
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1501  ->
                  match uu____1501 with
                  | (te,uu____1510) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1519) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1525,uu____1526) ->
        is_fstar_value t1
    | uu____1567 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1577 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1579 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1582 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1584 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1597,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1606,fields) ->
        FStar_Util.for_all
          (fun uu____1636  ->
             match uu____1636 with | (uu____1643,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1648) -> is_ml_value h
    | uu____1653 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref Prims.int_zero  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1671 =
       let uu____1673 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____1673  in
     Prims.op_Hat x uu____1671)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1776 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1778 = FStar_Syntax_Util.is_fun e'  in
          if uu____1778
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1792 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1792 
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
      (let uu____1883 = FStar_List.hd l  in
       match uu____1883 with
       | (p1,w1,e1) ->
           let uu____1918 =
             let uu____1927 = FStar_List.tl l  in FStar_List.hd uu____1927
              in
           (match uu____1918 with
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
                 | uu____2011 -> def)))
  
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
        let uu____2071 = s  in
        match uu____2071 with
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
                    let uu___365_2103 = e  in
                    {
                      FStar_Extraction_ML_Syntax.expr =
                        (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                      FStar_Extraction_ML_Syntax.mlty = ts;
                      FStar_Extraction_ML_Syntax.loc =
                        (uu___365_2103.FStar_Extraction_ML_Syntax.loc)
                    }  in
                  (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
            else
              if n_args < n_vars
              then
                (let extra_tyargs =
                   let uu____2118 = FStar_Util.first_N n_args vars  in
                   match uu____2118 with
                   | (uu____2132,rest_vars) ->
                       FStar_All.pipe_right rest_vars
                         (FStar_List.map
                            (fun uu____2153  ->
                               FStar_Extraction_ML_Syntax.MLTY_Erased))
                    in
                 let tyargs1 = FStar_List.append tyargs extra_tyargs  in
                 let ts = instantiate_tyscheme (vars, t) tyargs1  in
                 let tapp =
                   let uu___376_2160 = e  in
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                     FStar_Extraction_ML_Syntax.mlty = ts;
                     FStar_Extraction_ML_Syntax.loc =
                       (uu___376_2160.FStar_Extraction_ML_Syntax.loc)
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
                          let uu____2185 = fresh "t"  in (uu____2185, t2))
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
      let uu____2216 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2216 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____2240  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____2254 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____2271  ->
                    match uu____2271 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____2254
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
      let uu____2302 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2302 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____2322 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____2322 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2326 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____2338  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____2349 =
               let uu____2350 =
                 let uu____2362 = body r  in (vs_ts, uu____2362)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____2350  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____2349)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____2381 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____2384 = FStar_Options.codegen ()  in
           uu____2384 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____2381 then e else eta_expand expect e
  
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
            | uu____2462 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____2517 =
              match uu____2517 with
              | (pat,w,b) ->
                  let uu____2541 = aux b ty1 expect1  in (pat, w, uu____2541)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____2548,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____2551,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____2583 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____2599 = type_leq g s0 t0  in
                if uu____2599
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____2605 =
                       let uu____2606 =
                         let uu____2607 =
                           let uu____2614 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____2614, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____2607  in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____2606  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____2605;
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
               (lbs,body),uu____2633,uu____2634) ->
                let uu____2647 =
                  let uu____2648 =
                    let uu____2659 = aux body ty1 expect1  in
                    (lbs, uu____2659)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____2648  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2647
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____2668,uu____2669) ->
                let uu____2690 =
                  let uu____2691 =
                    let uu____2706 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2706)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____2691  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2690
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____2746,uu____2747) ->
                let uu____2752 =
                  let uu____2753 =
                    let uu____2762 = aux b1 ty1 expect1  in
                    let uu____2763 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____2762, uu____2763)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____2753  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2752
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____2771,uu____2772)
                ->
                let uu____2775 = FStar_Util.prefix es  in
                (match uu____2775 with
                 | (prefix1,last1) ->
                     let uu____2788 =
                       let uu____2789 =
                         let uu____2792 =
                           let uu____2795 = aux last1 ty1 expect1  in
                           [uu____2795]  in
                         FStar_List.append prefix1 uu____2792  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____2789  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____2788)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____2798,uu____2799) ->
                let uu____2820 =
                  let uu____2821 =
                    let uu____2836 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2836)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____2821  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2820
            | uu____2873 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'uuuuuu2893 .
    'uuuuuu2893 ->
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
            let uu____2920 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____2920 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____2933 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____2941 ->
                     let uu____2942 =
                       let uu____2944 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____2945 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____2944 uu____2945  in
                     if uu____2942
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____2951  ->
                             let uu____2952 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____2954 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____2952 uu____2954);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____2964  ->
                             let uu____2965 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____2967 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             let uu____2969 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule
                                 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____2965 uu____2967 uu____2969);
                        (let uu____2972 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand expect uu____2972)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____2984 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____2984 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____2986 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
  fun uu____3000  ->
    let uu____3001 = FStar_Options.use_nbe_for_extraction ()  in
    if uu____3001
    then extraction_norm_steps_nbe
    else extraction_norm_steps_core
  
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____3022 -> c
    | FStar_Syntax_Syntax.GTotal uu____3031 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____3067  ->
               match uu____3067 with
               | (uu____3082,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___540_3095 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___540_3095.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___540_3095.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___540_3095.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___540_3095.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___543_3099 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___543_3099.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___543_3099.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let maybe_reify_comp :
  'uuuuuu3111 .
    'uuuuuu3111 ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun g  ->
    fun env  ->
      fun c  ->
        let c1 = comp_no_args c  in
        let uu____3130 =
          let uu____3132 =
            let uu____3133 =
              FStar_All.pipe_right c1 FStar_Syntax_Util.comp_effect_name  in
            FStar_All.pipe_right uu____3133
              (FStar_TypeChecker_Env.norm_eff_name env)
             in
          FStar_All.pipe_right uu____3132
            (FStar_TypeChecker_Env.is_reifiable_effect env)
           in
        if uu____3130
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
      let arg_as_mlty g1 uu____3186 =
        match uu____3186 with
        | (a,uu____3194) ->
            let uu____3199 = is_type g1 a  in
            if uu____3199
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____3220 =
          let uu____3222 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____3222  in
        if uu____3220
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____3227 =
             let uu____3242 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.env_tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____3242 with
             | ((uu____3265,fvty),uu____3267) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant]
                     g1.FStar_Extraction_ML_UEnv.env_tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____3227 with
           | (formals,uu____3274) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3327 = FStar_Util.first_N n_args formals  in
                   match uu____3327 with
                   | (uu____3356,rest) ->
                       let uu____3390 =
                         FStar_List.map
                           (fun uu____3400  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____3390
                 else mlargs  in
               let nm =
                 let uu____3410 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____3410 with
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
        | FStar_Syntax_Syntax.Tm_type uu____3428 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3429 ->
            let uu____3430 =
              let uu____3432 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3432
               in
            failwith uu____3430
        | FStar_Syntax_Syntax.Tm_delayed uu____3435 ->
            let uu____3458 =
              let uu____3460 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3460
               in
            failwith uu____3458
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3463 =
              let uu____3465 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3465
               in
            failwith uu____3463
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3469 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____3469
        | FStar_Syntax_Syntax.Tm_constant uu____3470 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____3471 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____3478 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____3492) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3497;
               FStar_Syntax_Syntax.index = uu____3498;
               FStar_Syntax_Syntax.sort = t2;_},uu____3500)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3509) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3515,uu____3516) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____3589 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____3589 with
             | (bs1,c1) ->
                 let uu____3596 = binders_as_ml_binders env bs1  in
                 (match uu____3596 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let uu____3625 =
                          maybe_reify_comp env1
                            env1.FStar_Extraction_ML_UEnv.env_tcenv c1
                           in
                        translate_term_to_mlty env1 uu____3625  in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____3627 =
                        FStar_List.fold_right
                          (fun uu____3647  ->
                             fun uu____3648  ->
                               match (uu____3647, uu____3648) with
                               | ((uu____3671,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____3627 with | (uu____3686,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____3715 =
                let uu____3716 = FStar_Syntax_Util.un_uinst head1  in
                uu____3716.FStar_Syntax_Syntax.n  in
              match uu____3715 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____3747 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____3747
              | uu____3768 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____3771) ->
            let uu____3796 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____3796 with
             | (bs1,ty1) ->
                 let uu____3803 = binders_as_ml_binders env bs1  in
                 (match uu____3803 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____3831 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____3845 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____3877 ->
            let uu____3884 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____3884 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____3890 -> false  in
      let uu____3892 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.env_tcenv t0
         in
      if uu____3892
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____3898 = is_top_ty mlt  in
         if uu____3898 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____3916 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____3972  ->
                fun b  ->
                  match uu____3972 with
                  | (ml_bs,env) ->
                      let uu____4018 = is_type_binder g b  in
                      if uu____4018
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____4044 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____4044, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____4065 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____4065 with
                         | (env1,b2,uu____4090) ->
                             let ml_b =
                               let uu____4099 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____4099, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____3916 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        let uu____4177 = extraction_norm_steps ()  in
        FStar_TypeChecker_Normalize.normalize uu____4177
          g.FStar_Extraction_ML_UEnv.env_tcenv t0
         in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____4196) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4199,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4203 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____4237 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4238 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4239 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4248 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____4276 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____4276 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____4283 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____4316 -> p))
      | uu____4319 -> p
  
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
                       (fun uu____4421  ->
                          let uu____4422 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____4424 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4422 uu____4424)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____4460 = FStar_Options.codegen ()  in
                uu____4460 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4465 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4478 =
                        let uu____4479 =
                          let uu____4480 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4480  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4479
                         in
                      (uu____4478, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____4502 = term_as_mlexpr g source_term  in
                      (match uu____4502 with
                       | (mlterm,uu____4514,mlty) -> (mlterm, mlty))
                   in
                (match uu____4465 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____4536 =
                         let uu____4537 =
                           let uu____4544 =
                             let uu____4547 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____4547; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____4544)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____4537  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____4536
                        in
                     let uu____4550 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____4550))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____4572 =
                  let uu____4581 =
                    let uu____4588 =
                      let uu____4589 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4589  in
                    (uu____4588, [])  in
                  FStar_Pervasives_Native.Some uu____4581  in
                let uu____4598 = ok mlty  in (g, uu____4572, uu____4598)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4611 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4611 with
                 | (g1,x1,uu____4639) ->
                     let uu____4642 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4642))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4680 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4680 with
                 | (g1,x1,uu____4708) ->
                     let uu____4711 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4711))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4747 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____4790 =
                  let uu____4799 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____4799 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____4808;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____4810;
                          FStar_Extraction_ML_Syntax.loc = uu____4811;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____4813;_}
                      -> (n1, ttys)
                  | uu____4820 -> failwith "Expected a constructor"  in
                (match uu____4790 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____4857 = FStar_Util.first_N nTyVars pats  in
                     (match uu____4857 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___831_4961  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____4992  ->
                                               match uu____4992 with
                                               | (p1,uu____4999) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5002,t) ->
                                                        term_as_mlty g t
                                                    | uu____5008 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5012 
                                                              ->
                                                              let uu____5013
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5013);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____5017 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____5017)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____5046 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____5083  ->
                                   match uu____5083 with
                                   | (p1,imp1) ->
                                       let uu____5105 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____5105 with
                                        | (g2,p2,uu____5136) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____5046 with
                           | (g1,tyMLPats) ->
                               let uu____5200 =
                                 FStar_Util.fold_map
                                   (fun uu____5265  ->
                                      fun uu____5266  ->
                                        match (uu____5265, uu____5266) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____5364 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____5424 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____5364 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____5495 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____5495 with
                                                  | (g3,p2,uu____5538) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____5200 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____5659 =
                                      let uu____5670 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5721  ->
                                                match uu___0_5721 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____5763 -> []))
                                         in
                                      FStar_All.pipe_right uu____5670
                                        FStar_List.split
                                       in
                                    (match uu____5659 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____5839 -> false  in
                                         let uu____5849 =
                                           let uu____5858 =
                                             let uu____5865 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____5868 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____5865, uu____5868)  in
                                           FStar_Pervasives_Native.Some
                                             uu____5858
                                            in
                                         (g2, uu____5849, pat_ty_compat))))))
  
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
            let uu____6000 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____6000 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____6063 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____6111 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____6111
             in
          let uu____6112 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____6112 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____6272,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____6276 =
                  let uu____6288 =
                    let uu____6298 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____6298)  in
                  uu____6288 :: more_args  in
                eta_args uu____6276 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6314,uu____6315)
                -> ((FStar_List.rev more_args), t)
            | uu____6340 ->
                let uu____6341 =
                  let uu____6343 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____6345 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6343 uu____6345
                   in
                failwith uu____6341
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____6380,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6417 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____6439 = eta_args [] residualType  in
            match uu____6439 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____6497 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____6497
                 | uu____6498 ->
                     let uu____6510 = FStar_List.unzip eargs  in
                     (match uu____6510 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____6556 =
                                   let uu____6557 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6557
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6556
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6567 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6571,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6575;
                FStar_Extraction_ML_Syntax.loc = uu____6576;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____6599 ->
                    let uu____6602 =
                      let uu____6609 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6609, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6602
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
                     FStar_Extraction_ML_Syntax.mlty = uu____6613;
                     FStar_Extraction_ML_Syntax.loc = uu____6614;_},uu____6615);
                FStar_Extraction_ML_Syntax.mlty = uu____6616;
                FStar_Extraction_ML_Syntax.loc = uu____6617;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____6644 ->
                    let uu____6647 =
                      let uu____6654 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6654, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6647
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6658;
                FStar_Extraction_ML_Syntax.loc = uu____6659;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6667 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6667
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6671;
                FStar_Extraction_ML_Syntax.loc = uu____6672;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6674)) ->
              let uu____6687 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6687
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6691;
                     FStar_Extraction_ML_Syntax.loc = uu____6692;_},uu____6693);
                FStar_Extraction_ML_Syntax.mlty = uu____6694;
                FStar_Extraction_ML_Syntax.loc = uu____6695;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6707 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6707
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6711;
                     FStar_Extraction_ML_Syntax.loc = uu____6712;_},uu____6713);
                FStar_Extraction_ML_Syntax.mlty = uu____6714;
                FStar_Extraction_ML_Syntax.loc = uu____6715;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6717)) ->
              let uu____6734 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6734
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____6740 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6740
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6744)) ->
              let uu____6753 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6753
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6757;
                FStar_Extraction_ML_Syntax.loc = uu____6758;_},uu____6759),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6766 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6766
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6770;
                FStar_Extraction_ML_Syntax.loc = uu____6771;_},uu____6772),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6773)) ->
              let uu____6786 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6786
          | uu____6789 -> mlAppExpr
  
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
        | uu____6820 -> (ml_e, tag)
  
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
      let maybe_generalize uu____6881 =
        match uu____6881 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____6902;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____6907;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____6988 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____7065 =
              FStar_TypeChecker_Util.must_erase_for_extraction
                g.FStar_Extraction_ML_UEnv.env_tcenv lbtyp1
               in
            if uu____7065
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____7151 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____7151 (is_type_binder g) ->
                   let uu____7173 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____7173 with
                    | (bs1,c1) ->
                        let uu____7199 =
                          let uu____7212 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____7258 = is_type_binder g x  in
                                 Prims.op_Negation uu____7258) bs1
                             in
                          match uu____7212 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____7385 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____7385)
                           in
                        (match uu____7199 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____7447 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____7447
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____7496 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____7496 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7548 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____7548 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7651  ->
                                                       fun uu____7652  ->
                                                         match (uu____7651,
                                                                 uu____7652)
                                                         with
                                                         | ((x,uu____7678),
                                                            (y,uu____7680))
                                                             ->
                                                             let uu____7701 =
                                                               let uu____7708
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____7708)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7701)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____7725  ->
                                                       match uu____7725 with
                                                       | (a,uu____7733) ->
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
                                                let uu____7744 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____7763  ->
                                                          match uu____7763
                                                          with
                                                          | (x,uu____7772) ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____7744, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____7788 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____7788)
                                                      ||
                                                      (let uu____7791 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____7791)
                                                | uu____7793 -> false  in
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____7855 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____7874  ->
                                           match uu____7874 with
                                           | (a,uu____7882) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____7893 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____7912  ->
                                              match uu____7912 with
                                              | (x,uu____7921) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____7893, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____7965  ->
                                            match uu____7965 with
                                            | (bv,uu____7973) ->
                                                let uu____7978 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____7978
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____8008 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8021  ->
                                           match uu____8021 with
                                           | (a,uu____8029) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8040 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8059  ->
                                              match uu____8059 with
                                              | (x,uu____8068) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____8040, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8112  ->
                                            match uu____8112 with
                                            | (bv,uu____8120) ->
                                                let uu____8125 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8125
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
                              | FStar_Syntax_Syntax.Tm_name uu____8155 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8168  ->
                                           match uu____8168 with
                                           | (a,uu____8176) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8187 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8206  ->
                                              match uu____8206 with
                                              | (x,uu____8215) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____8187, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8259  ->
                                            match uu____8259 with
                                            | (bv,uu____8267) ->
                                                let uu____8272 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8272
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
                              | uu____8302 -> err_value_restriction lbdef1)))
               | uu____8322 -> no_gen ())
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
           fun uu____8473  ->
             match uu____8473 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____8534 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____8534 with
                  | (env1,uu____8551,exp_binding) ->
                      let uu____8555 =
                        let uu____8560 = FStar_Util.right lbname  in
                        (uu____8560, exp_binding)  in
                      (env1, uu____8555))) g lbs1
  
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
            (fun uu____8626  ->
               let uu____8627 = FStar_Syntax_Print.term_to_string e  in
               let uu____8629 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____8627
                 uu____8629);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____8636) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8637 ->
               let uu____8642 = term_as_mlexpr g e  in
               (match uu____8642 with
                | (ml_e,tag,t) ->
                    let uu____8656 = maybe_promote_effect ml_e tag t  in
                    (match uu____8656 with
                     | (ml_e1,tag1) ->
                         let uu____8667 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____8667
                         then
                           let uu____8674 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____8674, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____8681 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____8681, ty)
                            | uu____8682 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____8690 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____8690, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____8693 = term_as_mlexpr' g e  in
      match uu____8693 with
      | (e1,f,t) ->
          let uu____8709 = maybe_promote_effect e1 f t  in
          (match uu____8709 with | (e2,f1) -> (e2, f1, t))

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
           let uu____8734 =
             let uu____8736 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____8738 = FStar_Syntax_Print.tag_of_term top  in
             let uu____8740 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____8736 uu____8738 uu____8740
              in
           FStar_Util.print_string uu____8734);
      (let is_match t =
         let uu____8750 =
           let uu____8751 =
             let uu____8754 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____8754 FStar_Syntax_Util.unascribe  in
           uu____8751.FStar_Syntax_Syntax.n  in
         match uu____8750 with
         | FStar_Syntax_Syntax.Tm_match uu____8758 -> true
         | uu____8782 -> false  in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____8801  ->
              match uu____8801 with
              | (t,uu____8810) ->
                  let uu____8815 =
                    let uu____8816 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
                    uu____8816.FStar_Syntax_Syntax.n  in
                  (match uu____8815 with
                   | FStar_Syntax_Syntax.Tm_name uu____8822 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____8824 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____8826 -> true
                   | uu____8828 -> false))
          in
       let apply_to_match_branches head1 args =
         let uu____8867 =
           let uu____8868 =
             let uu____8871 =
               FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____8871 FStar_Syntax_Util.unascribe  in
           uu____8868.FStar_Syntax_Syntax.n  in
         match uu____8867 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee,branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____8995  ->
                       match uu____8995 with
                       | (pat,when_opt,body) ->
                           (pat, when_opt,
                             (let uu___1298_9052 = body  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1298_9052.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1298_9052.FStar_Syntax_Syntax.vars)
                              }))))
                in
             let uu___1301_9067 = head1  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1301_9067.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1301_9067.FStar_Syntax_Syntax.vars)
             }
         | uu____9088 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match"
          in
       let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9099 =
             let uu____9101 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9101
              in
           failwith uu____9099
       | FStar_Syntax_Syntax.Tm_delayed uu____9110 ->
           let uu____9133 =
             let uu____9135 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9135
              in
           failwith uu____9133
       | FStar_Syntax_Syntax.Tm_uvar uu____9144 ->
           let uu____9157 =
             let uu____9159 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9159
              in
           failwith uu____9157
       | FStar_Syntax_Syntax.Tm_bvar uu____9168 ->
           let uu____9169 =
             let uu____9171 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9171
              in
           failwith uu____9169
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9181 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____9181
       | FStar_Syntax_Syntax.Tm_type uu____9182 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9183 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9190 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____9206;_})
           ->
           let uu____9219 =
             let uu____9220 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9220  in
           (match uu____9219 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9227;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9229;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9230;_} ->
                let uu____9233 =
                  let uu____9234 =
                    let uu____9235 =
                      let uu____9242 =
                        let uu____9245 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____9245]  in
                      (fw, uu____9242)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9235  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9234
                   in
                (uu____9233, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9263 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____9263 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9271 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____9271 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____9282 =
                         let uu____9289 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____9289
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____9282 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____9297 =
                         let uu____9308 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____9308]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9297
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9335 =
                    let uu____9342 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____9342 tv  in
                  uu____9335 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____9350 =
                    let uu____9361 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____9361]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9350
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____9388)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9421 =
                  let uu____9428 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.env_tcenv m
                     in
                  FStar_Util.must uu____9428  in
                (match uu____9421 with
                 | (ed,qualifiers) ->
                     let uu____9455 =
                       let uu____9457 =
                         FStar_TypeChecker_Env.is_reifiable_effect
                           g.FStar_Extraction_ML_UEnv.env_tcenv
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____9457  in
                     if uu____9455
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9475 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9477) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9483) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9489 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.env_tcenv t
              in
           (match uu____9489 with
            | (uu____9502,ty,uu____9504) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____9506 =
                  let uu____9507 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9507  in
                (uu____9506, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9508 ->
           let uu____9509 = is_type g t  in
           if uu____9509
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9520 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____9520 with
              | (FStar_Util.Inl uu____9533,uu____9534) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9539;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9542;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____9560 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____9560, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9561 -> instantiate_maybe_partial x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9563 = is_type g t  in
           if uu____9563
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9574 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____9574 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9583;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9586;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9594  ->
                        let uu____9595 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____9597 =
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            g.FStar_Extraction_ML_UEnv.currentModule x
                           in
                        let uu____9599 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9595 uu____9597 uu____9599);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____9612 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____9612, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9613 -> instantiate_maybe_partial x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____9641 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____9641 with
            | (bs1,body1) ->
                let uu____9654 = binders_as_ml_binders g bs1  in
                (match uu____9654 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9690 =
                             FStar_TypeChecker_Env.is_reifiable_rc
                               env.FStar_Extraction_ML_UEnv.env_tcenv rc
                              in
                           if uu____9690
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.env_tcenv
                               [FStar_TypeChecker_Env.Inlining] body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9698  ->
                                 let uu____9699 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9699);
                            body1)
                        in
                     let uu____9702 = term_as_mlexpr env body2  in
                     (match uu____9702 with
                      | (ml_body,f,t1) ->
                          let uu____9718 =
                            FStar_List.fold_right
                              (fun uu____9738  ->
                                 fun uu____9739  ->
                                   match (uu____9738, uu____9739) with
                                   | ((uu____9762,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____9718 with
                           | (f1,tfun) ->
                               let uu____9785 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____9785, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____9793;
              FStar_Syntax_Syntax.vars = uu____9794;_},(a1,uu____9796)::[])
           ->
           let ty =
             let uu____9836 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____9836  in
           let uu____9837 =
             let uu____9838 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____9838
              in
           (uu____9837, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____9839;
              FStar_Syntax_Syntax.vars = uu____9840;_},(t1,uu____9842)::
            (r,uu____9844)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____9899);
              FStar_Syntax_Syntax.pos = uu____9900;
              FStar_Syntax_Syntax.vars = uu____9901;_},uu____9902)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (is_match head1) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____9961 =
             FStar_All.pipe_right args (apply_to_match_branches head1)  in
           FStar_All.pipe_right uu____9961 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_10015  ->
                        match uu___1_10015 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____10018 -> false)))
              in
           let uu____10020 =
             let uu____10025 =
               let uu____10026 =
                 let uu____10029 =
                   FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
                 FStar_All.pipe_right uu____10029 FStar_Syntax_Util.unascribe
                  in
               uu____10026.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____10025)  in
           (match uu____10020 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____10038,uu____10039) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Iota;
                    FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                term_as_mlexpr g t1
            | (uu____10053,FStar_Syntax_Syntax.Tm_abs (bs,uu____10055,_rc))
                ->
                let uu____10081 =
                  FStar_All.pipe_right t
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Beta;
                       FStar_TypeChecker_Env.Iota;
                       FStar_TypeChecker_Env.Zeta;
                       FStar_TypeChecker_Env.EraseUniverses;
                       FStar_TypeChecker_Env.AllowUnboundUniverses]
                       g.FStar_Extraction_ML_UEnv.env_tcenv)
                   in
                FStar_All.pipe_right uu____10081 (term_as_mlexpr g)
            | (uu____10088,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____10090 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    [FStar_TypeChecker_Env.Inlining] head1 uu____10090
                   in
                let tm =
                  let uu____10102 =
                    let uu____10107 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____10108 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____10107 uu____10108  in
                  uu____10102 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____10117 ->
                let rec extract_app is_data uu____10170 uu____10171 restArgs
                  =
                  match (uu____10170, uu____10171) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____10252 =
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
                         (fun uu____10279  ->
                            let uu____10280 =
                              let uu____10282 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                uu____10282
                               in
                            let uu____10283 =
                              FStar_Extraction_ML_Code.string_of_mlty
                                g.FStar_Extraction_ML_UEnv.currentModule t1
                               in
                            let uu____10285 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____10296)::uu____10297 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10280 uu____10283 uu____10285);
                       (match (restArgs, t1) with
                        | ([],uu____10331) ->
                            let app =
                              let uu____10347 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10347
                               in
                            (app, f, t1)
                        | ((arg,uu____10349)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10380 =
                              let uu____10385 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____10385, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10380 rest
                        | ((e0,uu____10397)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____10430 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____10430
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____10435 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____10435 with
                             | (e01,tInferred) ->
                                 let uu____10448 =
                                   let uu____10453 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____10453, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10448 rest)
                        | uu____10464 ->
                            let uu____10477 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____10477 with
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
                                  | uu____10549 ->
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
                let extract_app_maybe_projector is_data mlhead uu____10620
                  args1 =
                  match uu____10620 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10650)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10734))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____10736,f',t3)) ->
                                 let uu____10774 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____10774 t3
                             | uu____10775 -> (args2, f1, t2)  in
                           let uu____10800 = remove_implicits args1 f t1  in
                           (match uu____10800 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____10856 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____10880 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____10888 ->
                      let uu____10889 =
                        let uu____10910 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____10910 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____10949  ->
                                  let uu____10950 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____10952 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____10954 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____10956 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____10950 uu____10952 uu____10954
                                    uu____10956);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____10983 -> failwith "FIXME Ty"  in
                      (match uu____10889 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11059)::uu____11060 -> is_type g a
                             | uu____11087 -> false  in
                           let uu____11099 =
                             match vars with
                             | uu____11128::uu____11129 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11143 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____11149 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____11187 =
                                       FStar_List.map
                                         (fun uu____11199  ->
                                            match uu____11199 with
                                            | (x,uu____11207) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____11187, [])
                                   else
                                     (let uu____11230 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____11230 with
                                      | (prefix1,rest) ->
                                          let uu____11319 =
                                            FStar_List.map
                                              (fun uu____11331  ->
                                                 match uu____11331 with
                                                 | (x,uu____11339) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____11319, rest))
                                    in
                                 (match uu____11149 with
                                  | (provided_type_args,rest) ->
                                      let uu____11390 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____11399 ->
                                            let uu____11400 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11400 with
                                             | (head3,uu____11412,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____11414 ->
                                            let uu____11416 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11416 with
                                             | (head3,uu____11428,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____11431;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____11432;_}::[])
                                            ->
                                            let uu____11435 =
                                              instantiate_maybe_partial head3
                                                (vars, t1) provided_type_args
                                               in
                                            (match uu____11435 with
                                             | (head4,uu____11447,t2) ->
                                                 let uu____11449 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____11449, t2))
                                        | uu____11452 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____11390 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____11099 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11519 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____11519,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11520 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11529 ->
                      let uu____11530 =
                        let uu____11551 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____11551 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11590  ->
                                  let uu____11591 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____11593 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11595 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11597 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11591 uu____11593 uu____11595
                                    uu____11597);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11624 -> failwith "FIXME Ty"  in
                      (match uu____11530 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11700)::uu____11701 -> is_type g a
                             | uu____11728 -> false  in
                           let uu____11740 =
                             match vars with
                             | uu____11769::uu____11770 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11784 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____11790 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____11828 =
                                       FStar_List.map
                                         (fun uu____11840  ->
                                            match uu____11840 with
                                            | (x,uu____11848) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____11828, [])
                                   else
                                     (let uu____11871 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____11871 with
                                      | (prefix1,rest) ->
                                          let uu____11960 =
                                            FStar_List.map
                                              (fun uu____11972  ->
                                                 match uu____11972 with
                                                 | (x,uu____11980) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____11960, rest))
                                    in
                                 (match uu____11790 with
                                  | (provided_type_args,rest) ->
                                      let uu____12031 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____12040 ->
                                            let uu____12041 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12041 with
                                             | (head3,uu____12053,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____12055 ->
                                            let uu____12057 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12057 with
                                             | (head3,uu____12069,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____12072;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____12073;_}::[])
                                            ->
                                            let uu____12076 =
                                              instantiate_maybe_partial head3
                                                (vars, t1) provided_type_args
                                               in
                                            (match uu____12076 with
                                             | (head4,uu____12088,t2) ->
                                                 let uu____12090 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____12090, t2))
                                        | uu____12093 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____12031 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____11740 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12160 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____12160,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12161 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12170 ->
                      let uu____12171 = term_as_mlexpr g head2  in
                      (match uu____12171 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____12187 = is_type g t  in
                if uu____12187
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12198 =
                     let uu____12199 = FStar_Syntax_Util.un_uinst head1  in
                     uu____12199.FStar_Syntax_Syntax.n  in
                   match uu____12198 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12209 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____12209 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12218 -> extract_app_with_instantiations ())
                   | uu____12221 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____12224),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12289 =
                   maybe_reify_comp g g.FStar_Extraction_ML_UEnv.env_tcenv c
                    in
                 term_as_mlty g uu____12289
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____12293 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____12293 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e') when
           (let uu____12325 = FStar_Syntax_Syntax.is_top_level [lb]  in
            Prims.op_Negation uu____12325) &&
             (let uu____12328 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs
                 in
              FStar_Util.is_some uu____12328)
           ->
           let b =
             let uu____12338 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                in
             (uu____12338, FStar_Pervasives_Native.None)  in
           let uu____12341 = FStar_Syntax_Subst.open_term [b] e'  in
           (match uu____12341 with
            | ((x,uu____12365)::uu____12366,body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str,uu____12395)::[]) ->
                      let uu____12420 =
                        let uu____12421 = FStar_Syntax_Subst.compress str  in
                        uu____12421.FStar_Syntax_Syntax.n  in
                      (match uu____12420 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s,uu____12427)) ->
                           let id1 =
                             let uu____12431 =
                               let uu____12437 =
                                 FStar_Syntax_Syntax.range_of_bv x  in
                               (s, uu____12437)  in
                             FStar_Ident.mk_ident uu____12431  in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id1;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             }  in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv  in
                           FStar_Pervasives_Native.Some bv1
                       | uu____12442 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                   in
                let remove_attr1 attrs =
                  let uu____12459 =
                    FStar_List.partition
                      (fun attr  ->
                         let uu____12471 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr]
                            in
                         FStar_Util.is_some uu____12471)
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match uu____12459 with
                  | (uu____12476,other_attrs) -> other_attrs  in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None  ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1769_12504 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1769_12504.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1769_12504.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1769_12504.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1769_12504.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1769_12504.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1769_12504.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr1 lb.FStar_Syntax_Syntax.lbattrs  in
                      let rename =
                        let uu____12512 =
                          let uu____12513 =
                            let uu____12520 =
                              FStar_Syntax_Syntax.bv_to_name y  in
                            (x, uu____12520)  in
                          FStar_Syntax_Syntax.NT uu____12513  in
                        [uu____12512]  in
                      let body1 =
                        let uu____12526 =
                          FStar_Syntax_Subst.subst rename body  in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____12526
                         in
                      let lb1 =
                        let uu___1776_12542 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1776_12542.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1776_12542.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1776_12542.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1776_12542.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1776_12542.FStar_Syntax_Syntax.lbpos)
                        }  in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1)
                   in
                let top1 =
                  let uu___1780_12559 = top  in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1780_12559.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1780_12559.FStar_Syntax_Syntax.vars)
                  }  in
                term_as_mlexpr' g top1)
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____12582 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12598 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____12598
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____12613 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____12613  in
                   let lb1 =
                     let uu___1794_12615 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1794_12615.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1794_12615.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1794_12615.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1794_12615.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1794_12615.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1794_12615.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____12582 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____12640 =
                        FStar_Ident.lid_of_path
                          (FStar_List.append
                             (FStar_Pervasives_Native.fst
                                g.FStar_Extraction_ML_UEnv.currentModule)
                             [FStar_Pervasives_Native.snd
                                g.FStar_Extraction_ML_UEnv.currentModule])
                          FStar_Range.dummyRange
                         in
                      FStar_TypeChecker_Env.set_current_module
                        g.FStar_Extraction_ML_UEnv.env_tcenv uu____12640
                       in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let lbdef =
                              let uu____12663 = FStar_Options.ml_ish ()  in
                              if uu____12663
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____12675 =
                                   let uu____12676 =
                                     let uu____12677 =
                                       extraction_norm_steps ()  in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____12677
                                      in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____12676 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____12680 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____12680
                                 then
                                   ((let uu____12690 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____12690);
                                    (let a =
                                       let uu____12696 =
                                         let uu____12698 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____12698
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____12696 norm_call
                                        in
                                     a))
                                 else norm_call ())
                               in
                            let uu___1811_12705 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1811_12705.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1811_12705.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1811_12705.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1811_12705.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1811_12705.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1811_12705.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____12758 =
                  match uu____12758 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____12914  ->
                               match uu____12914 with
                               | (a,uu____12922) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____12928 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____12928 with
                       | (e1,ty) ->
                           let uu____12939 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____12939 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____12951 -> []  in
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
                let uu____12982 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____13079  ->
                         match uu____13079 with
                         | (env,lbs4) ->
                             let uu____13213 = lb  in
                             (match uu____13213 with
                              | (lbname,uu____13264,(t1,(uu____13266,polytype)),add_unit,uu____13269)
                                  ->
                                  let uu____13284 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____13284 with
                                   | (env1,nm,uu____13325) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____12982 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____13604 = term_as_mlexpr env_body e'1  in
                     (match uu____13604 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____13621 =
                              let uu____13624 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____13624  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13621
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____13637 =
                            let uu____13638 =
                              let uu____13639 =
                                let uu____13640 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____13640)  in
                              mk_MLE_Let top_level uu____13639 e'2  in
                            let uu____13649 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13638 uu____13649
                             in
                          (uu____13637, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____13688 = term_as_mlexpr g scrutinee  in
           (match uu____13688 with
            | (e,f_e,t_e) ->
                let uu____13704 = check_pats_for_ite pats  in
                (match uu____13704 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____13769 = term_as_mlexpr g then_e1  in
                            (match uu____13769 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____13785 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____13785 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____13801 =
                                        let uu____13812 =
                                          type_leq g t_then t_else  in
                                        if uu____13812
                                        then (t_else, no_lift)
                                        else
                                          (let uu____13833 =
                                             type_leq g t_else t_then  in
                                           if uu____13833
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____13801 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____13880 =
                                             let uu____13881 =
                                               let uu____13882 =
                                                 let uu____13891 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____13892 =
                                                   let uu____13895 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____13895
                                                    in
                                                 (e, uu____13891,
                                                   uu____13892)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____13882
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____13881
                                              in
                                           let uu____13898 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____13880, uu____13898,
                                             t_branch))))
                        | uu____13899 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____13917 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____14016 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____14016 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____14061 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____14061 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____14123 =
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
                                                   let uu____14146 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____14146 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____14123 with
                                              | (when_opt1,f_when) ->
                                                  let uu____14196 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____14196 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____14231 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14308 
                                                                 ->
                                                                 match uu____14308
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
                                                         uu____14231)))))
                               true)
                           in
                        match uu____13917 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14479  ->
                                      let uu____14480 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____14482 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14480 uu____14482);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14509 =
                                   let uu____14510 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14510
                                    in
                                 (match uu____14509 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14517;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14519;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____14520;_}
                                      ->
                                      let uu____14523 =
                                        let uu____14524 =
                                          let uu____14525 =
                                            let uu____14532 =
                                              let uu____14535 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____14535]  in
                                            (fw, uu____14532)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14525
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14524
                                         in
                                      (uu____14523,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14539,uu____14540,(uu____14541,f_first,t_first))::rest
                                 ->
                                 let uu____14601 =
                                   FStar_List.fold_left
                                     (fun uu____14643  ->
                                        fun uu____14644  ->
                                          match (uu____14643, uu____14644)
                                          with
                                          | ((topt,f),(uu____14701,uu____14702,
                                                       (uu____14703,f_branch,t_branch)))
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
                                                    let uu____14759 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____14759
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____14766 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____14766
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
                                 (match uu____14601 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____14864  ->
                                                match uu____14864 with
                                                | (p,(wopt,uu____14893),
                                                   (b1,uu____14895,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____14914 -> b1
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
                                      let uu____14919 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____14919, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____14946 =
          let uu____14951 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.env_tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____14951  in
        match uu____14946 with
        | (uu____14976,fstar_disc_type) ->
            let wildcards =
              let uu____14986 =
                let uu____14987 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____14987.FStar_Syntax_Syntax.n  in
              match uu____14986 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14998) ->
                  let uu____15019 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_15053  ->
                            match uu___2_15053 with
                            | (uu____15061,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15062)) ->
                                true
                            | uu____15067 -> false))
                     in
                  FStar_All.pipe_right uu____15019
                    (FStar_List.map
                       (fun uu____15103  ->
                          let uu____15110 = fresh "_"  in
                          (uu____15110, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____15114 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____15129 =
                let uu____15130 =
                  let uu____15142 =
                    let uu____15143 =
                      let uu____15144 =
                        let uu____15159 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____15165 =
                          let uu____15176 =
                            let uu____15185 =
                              let uu____15186 =
                                let uu____15193 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____15193,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____15186
                               in
                            let uu____15196 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____15185, FStar_Pervasives_Native.None,
                              uu____15196)
                             in
                          let uu____15200 =
                            let uu____15211 =
                              let uu____15220 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____15220)
                               in
                            [uu____15211]  in
                          uu____15176 :: uu____15200  in
                        (uu____15159, uu____15165)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____15144  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____15143
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____15142)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____15130  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____15129
               in
            let uu____15281 =
              let uu____15282 =
                let uu____15285 =
                  let uu____15286 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____15286;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____15285]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____15282)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____15281
  