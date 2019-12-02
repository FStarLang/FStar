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
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
  
let fail :
  'Auu____120 .
    FStar_Range.range ->
      (FStar_Errors.raw_error * Prims.string) -> 'Auu____120
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_ill_typed_application :
  'Auu____156 'Auu____157 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'Auu____156) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'Auu____157
  =
  fun env  ->
    fun t  ->
      fun mlhead  ->
        fun args  ->
          fun ty  ->
            let uu____195 =
              let uu____201 =
                let uu____203 = FStar_Syntax_Print.term_to_string t  in
                let uu____205 =
                  FStar_Extraction_ML_Code.string_of_mlexpr
                    env.FStar_Extraction_ML_UEnv.currentModule mlhead
                   in
                let uu____207 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____209 =
                  let uu____211 =
                    FStar_All.pipe_right args
                      (FStar_List.map
                         (fun uu____232  ->
                            match uu____232 with
                            | (x,uu____239) ->
                                FStar_Syntax_Print.term_to_string x))
                     in
                  FStar_All.pipe_right uu____211 (FStar_String.concat " ")
                   in
                FStar_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu____203 uu____205 uu____207 uu____209
                 in
              (FStar_Errors.Fatal_IllTyped, uu____201)  in
            fail t.FStar_Syntax_Syntax.pos uu____195
  
let err_ill_typed_erasure :
  'Auu____256 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____256
  =
  fun env  ->
    fun pos  ->
      fun ty  ->
        let uu____272 =
          let uu____278 =
            let uu____280 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty
               in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____280
             in
          (FStar_Errors.Fatal_IllTyped, uu____278)  in
        fail pos uu____272
  
let err_value_restriction :
  'Auu____289 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____289
  =
  fun t  ->
    let uu____299 =
      let uu____305 =
        let uu____307 = FStar_Syntax_Print.tag_of_term t  in
        let uu____309 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____307 uu____309
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____305)  in
    fail t.FStar_Syntax_Syntax.pos uu____299
  
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
            let uu____343 =
              let uu____349 =
                let uu____351 = FStar_Syntax_Print.term_to_string t  in
                let uu____353 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____355 = FStar_Extraction_ML_Util.eff_to_string f0  in
                let uu____357 = FStar_Extraction_ML_Util.eff_to_string f1  in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____351 uu____353 uu____355 uu____357
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____349)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____343
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.of_int (20))  in
  let rec delta_norm_eff g l =
    let uu____385 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____385 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____390 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.env_tcenv
              [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____390 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____401,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____411 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____411
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____416 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____416
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.env_tcenv l1
               in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____442 =
                  FStar_TypeChecker_Env.is_reifiable_effect
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    ed.FStar_Syntax_Syntax.mname
                   in
                if uu____442
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____466 =
        let uu____467 = FStar_Syntax_Subst.compress t1  in
        uu____467.FStar_Syntax_Syntax.n  in
      match uu____466 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____473 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____498 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____527 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____537 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____537
      | FStar_Syntax_Syntax.Tm_uvar uu____538 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____552 -> false
      | FStar_Syntax_Syntax.Tm_name uu____554 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____556 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____564 -> false
      | FStar_Syntax_Syntax.Tm_type uu____566 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____568,c) ->
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
           | FStar_Pervasives_Native.Some (uu____604,t2) -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____610 ->
          let uu____627 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____627 with | (head1,uu____646) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____672) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____678) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____683,body,uu____685) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____710,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____730,branches) ->
          (match branches with
           | (uu____769,uu____770,e)::uu____772 -> is_arity env e
           | uu____819 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____851 ->
          let uu____874 =
            let uu____876 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____876  in
          failwith uu____874
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____880 =
            let uu____882 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____882  in
          failwith uu____880
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____887 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____887
      | FStar_Syntax_Syntax.Tm_constant uu____888 -> false
      | FStar_Syntax_Syntax.Tm_type uu____890 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____892 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____900 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____919;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____920;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____921;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____923;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____924;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____925;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____926;_},s)
          ->
          let uu____975 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____975
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____976;
            FStar_Syntax_Syntax.index = uu____977;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____982;
            FStar_Syntax_Syntax.index = uu____983;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____989,uu____990) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1032) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1039) ->
          let uu____1064 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____1064 with
           | (uu____1070,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____1090 =
            let uu____1095 =
              let uu____1096 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1096]  in
            FStar_Syntax_Subst.open_term uu____1095 body  in
          (match uu____1090 with
           | (uu____1116,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1118,lbs),body) ->
          let uu____1138 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____1138 with
           | (uu____1146,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1152,branches) ->
          (match branches with
           | b::uu____1192 ->
               let uu____1237 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1237 with
                | (uu____1239,uu____1240,e) -> is_type_aux env e)
           | uu____1258 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1276 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1285) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1291) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1332  ->
           let uu____1333 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1335 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1333
             uu____1335);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1344  ->
            if b
            then
              let uu____1346 = FStar_Syntax_Print.term_to_string t  in
              let uu____1348 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1346
                uu____1348
            else
              (let uu____1353 = FStar_Syntax_Print.term_to_string t  in
               let uu____1355 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1353 uu____1355));
       b)
  
let is_type_binder :
  'Auu____1365 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____1365) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1392 =
      let uu____1393 = FStar_Syntax_Subst.compress t  in
      uu____1393.FStar_Syntax_Syntax.n  in
    match uu____1392 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1397;
          FStar_Syntax_Syntax.fv_delta = uu____1398;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1400;
          FStar_Syntax_Syntax.fv_delta = uu____1401;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1402);_}
        -> true
    | uu____1410 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1419 =
      let uu____1420 = FStar_Syntax_Subst.compress t  in
      uu____1420.FStar_Syntax_Syntax.n  in
    match uu____1419 with
    | FStar_Syntax_Syntax.Tm_constant uu____1424 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1426 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1428 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1430 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1476 = is_constructor head1  in
        if uu____1476
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1498  ->
                  match uu____1498 with
                  | (te,uu____1507) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1516) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1522,uu____1523) ->
        is_fstar_value t1
    | uu____1564 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1574 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1576 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1579 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1581 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1594,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1603,fields) ->
        FStar_Util.for_all
          (fun uu____1633  ->
             match uu____1633 with | (uu____1640,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1645) -> is_ml_value h
    | uu____1650 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref Prims.int_zero  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1668 =
       let uu____1670 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____1670  in
     Prims.op_Hat x uu____1668)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1773 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1775 = FStar_Syntax_Util.is_fun e'  in
          if uu____1775
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1789 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1789 
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
      (let uu____1880 = FStar_List.hd l  in
       match uu____1880 with
       | (p1,w1,e1) ->
           let uu____1915 =
             let uu____1924 = FStar_List.tl l  in FStar_List.hd uu____1924
              in
           (match uu____1915 with
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
                 | uu____2008 -> def)))
  
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
        let uu____2068 = s  in
        match uu____2068 with
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
                    let uu___365_2100 = e  in
                    {
                      FStar_Extraction_ML_Syntax.expr =
                        (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                      FStar_Extraction_ML_Syntax.mlty = ts;
                      FStar_Extraction_ML_Syntax.loc =
                        (uu___365_2100.FStar_Extraction_ML_Syntax.loc)
                    }  in
                  (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
            else
              if n_args < n_vars
              then
                (let extra_tyargs =
                   let uu____2115 = FStar_Util.first_N n_args vars  in
                   match uu____2115 with
                   | (uu____2129,rest_vars) ->
                       FStar_All.pipe_right rest_vars
                         (FStar_List.map
                            (fun uu____2150  ->
                               FStar_Extraction_ML_Syntax.MLTY_Erased))
                    in
                 let tyargs1 = FStar_List.append tyargs extra_tyargs  in
                 let ts = instantiate_tyscheme (vars, t) tyargs1  in
                 let tapp =
                   let uu___376_2157 = e  in
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                     FStar_Extraction_ML_Syntax.mlty = ts;
                     FStar_Extraction_ML_Syntax.loc =
                       (uu___376_2157.FStar_Extraction_ML_Syntax.loc)
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
                          let uu____2182 = fresh "t"  in (uu____2182, t2))
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
      let uu____2213 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2213 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____2237  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____2251 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____2268  ->
                    match uu____2268 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____2251
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
      let uu____2299 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2299 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____2319 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____2319 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2323 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____2335  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____2346 =
               let uu____2347 =
                 let uu____2359 = body r  in (vs_ts, uu____2359)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____2347  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____2346)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____2378 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____2381 = FStar_Options.codegen ()  in
           uu____2381 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____2378 then e else eta_expand expect e
  
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
            | uu____2459 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____2514 =
              match uu____2514 with
              | (pat,w,b) ->
                  let uu____2538 = aux b ty1 expect1  in (pat, w, uu____2538)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____2545,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____2548,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____2580 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____2596 = type_leq g s0 t0  in
                if uu____2596
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____2602 =
                       let uu____2603 =
                         let uu____2604 =
                           let uu____2611 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____2611, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____2604  in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____2603  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____2602;
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
               (lbs,body),uu____2630,uu____2631) ->
                let uu____2644 =
                  let uu____2645 =
                    let uu____2656 = aux body ty1 expect1  in
                    (lbs, uu____2656)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____2645  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2644
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____2665,uu____2666) ->
                let uu____2687 =
                  let uu____2688 =
                    let uu____2703 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2703)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____2688  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2687
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____2743,uu____2744) ->
                let uu____2749 =
                  let uu____2750 =
                    let uu____2759 = aux b1 ty1 expect1  in
                    let uu____2760 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____2759, uu____2760)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____2750  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2749
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____2768,uu____2769)
                ->
                let uu____2772 = FStar_Util.prefix es  in
                (match uu____2772 with
                 | (prefix1,last1) ->
                     let uu____2785 =
                       let uu____2786 =
                         let uu____2789 =
                           let uu____2792 = aux last1 ty1 expect1  in
                           [uu____2792]  in
                         FStar_List.append prefix1 uu____2789  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____2786  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____2785)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____2795,uu____2796) ->
                let uu____2817 =
                  let uu____2818 =
                    let uu____2833 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2833)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____2818  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2817
            | uu____2870 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'Auu____2890 .
    'Auu____2890 ->
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
            let uu____2917 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____2917 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____2930 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____2938 ->
                     let uu____2939 =
                       let uu____2941 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____2942 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____2941 uu____2942  in
                     if uu____2939
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____2948  ->
                             let uu____2949 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____2951 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____2949 uu____2951);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____2961  ->
                             let uu____2962 =
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 g.FStar_Extraction_ML_UEnv.currentModule e
                                in
                             let uu____2964 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule ty1
                                in
                             let uu____2966 =
                               FStar_Extraction_ML_Code.string_of_mlty
                                 g.FStar_Extraction_ML_UEnv.currentModule
                                 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____2962 uu____2964 uu____2966);
                        (let uu____2969 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand expect uu____2969)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____2981 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____2981 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____2983 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let (extraction_norm_steps : FStar_TypeChecker_Env.step Prims.list) =
  [FStar_TypeChecker_Env.AllowUnboundUniverses;
  FStar_TypeChecker_Env.EraseUniverses;
  FStar_TypeChecker_Env.Inlining;
  FStar_TypeChecker_Env.Eager_unfolding;
  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
  FStar_TypeChecker_Env.Primops;
  FStar_TypeChecker_Env.Unascribe;
  FStar_TypeChecker_Env.ForExtraction] 
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____3001 -> c
    | FStar_Syntax_Syntax.GTotal uu____3010 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____3046  ->
               match uu____3046 with
               | (uu____3061,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___538_3074 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___538_3074.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___538_3074.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___538_3074.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___538_3074.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___541_3078 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___541_3078.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___541_3078.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let maybe_reify_comp :
  'Auu____3090 .
    'Auu____3090 ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun g  ->
    fun env  ->
      fun c  ->
        let c1 = comp_no_args c  in
        let uu____3109 =
          let uu____3111 =
            let uu____3112 =
              FStar_All.pipe_right c1 FStar_Syntax_Util.comp_effect_name  in
            FStar_All.pipe_right uu____3112
              (FStar_TypeChecker_Env.norm_eff_name env)
             in
          FStar_All.pipe_right uu____3111
            (FStar_TypeChecker_Env.is_reifiable_effect env)
           in
        if uu____3109
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
      let arg_as_mlty g1 uu____3165 =
        match uu____3165 with
        | (a,uu____3173) ->
            let uu____3178 = is_type g1 a  in
            if uu____3178
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____3199 =
          let uu____3201 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____3201  in
        if uu____3199
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____3206 =
             let uu____3221 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.env_tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____3221 with
             | ((uu____3244,fvty),uu____3246) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant]
                     g1.FStar_Extraction_ML_UEnv.env_tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____3206 with
           | (formals,uu____3253) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3306 = FStar_Util.first_N n_args formals  in
                   match uu____3306 with
                   | (uu____3335,rest) ->
                       let uu____3369 =
                         FStar_List.map
                           (fun uu____3379  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____3369
                 else mlargs  in
               let nm =
                 let uu____3389 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____3389 with
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
        | FStar_Syntax_Syntax.Tm_type uu____3407 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3408 ->
            let uu____3409 =
              let uu____3411 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3411
               in
            failwith uu____3409
        | FStar_Syntax_Syntax.Tm_delayed uu____3414 ->
            let uu____3437 =
              let uu____3439 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3439
               in
            failwith uu____3437
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3442 =
              let uu____3444 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3444
               in
            failwith uu____3442
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3448 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____3448
        | FStar_Syntax_Syntax.Tm_constant uu____3449 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____3450 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____3457 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____3471) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3476;
               FStar_Syntax_Syntax.index = uu____3477;
               FStar_Syntax_Syntax.sort = t2;_},uu____3479)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3488) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3494,uu____3495) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____3568 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____3568 with
             | (bs1,c1) ->
                 let uu____3575 = binders_as_ml_binders env bs1  in
                 (match uu____3575 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let uu____3604 =
                          maybe_reify_comp env1
                            env1.FStar_Extraction_ML_UEnv.env_tcenv c1
                           in
                        translate_term_to_mlty env1 uu____3604  in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____3606 =
                        FStar_List.fold_right
                          (fun uu____3626  ->
                             fun uu____3627  ->
                               match (uu____3626, uu____3627) with
                               | ((uu____3650,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____3606 with | (uu____3665,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____3694 =
                let uu____3695 = FStar_Syntax_Util.un_uinst head1  in
                uu____3695.FStar_Syntax_Syntax.n  in
              match uu____3694 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____3726 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____3726
              | uu____3747 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____3750) ->
            let uu____3775 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____3775 with
             | (bs1,ty1) ->
                 let uu____3782 = binders_as_ml_binders env bs1  in
                 (match uu____3782 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____3810 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____3824 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____3856 ->
            let uu____3863 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____3863 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____3869 -> false  in
      let uu____3871 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.env_tcenv t0
         in
      if uu____3871
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____3877 = is_top_ty mlt  in
         if uu____3877 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____3895 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____3951  ->
                fun b  ->
                  match uu____3951 with
                  | (ml_bs,env) ->
                      let uu____3997 = is_type_binder g b  in
                      if uu____3997
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____4023 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____4023, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____4044 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____4044 with
                         | (env1,b2,uu____4069) ->
                             let ml_b =
                               let uu____4078 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____4078, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____3895 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize extraction_norm_steps
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____4174) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4177,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4181 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____4215 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4216 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4217 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4226 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____4254 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____4254 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____4261 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____4294 -> p))
      | uu____4297 -> p
  
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
                       (fun uu____4399  ->
                          let uu____4400 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____4402 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____4400 uu____4402)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____4438 = FStar_Options.codegen ()  in
                uu____4438 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____4443 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4456 =
                        let uu____4457 =
                          let uu____4458 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____4458  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____4457
                         in
                      (uu____4456, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____4480 = term_as_mlexpr g source_term  in
                      (match uu____4480 with
                       | (mlterm,uu____4492,mlty) -> (mlterm, mlty))
                   in
                (match uu____4443 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____4514 =
                         let uu____4515 =
                           let uu____4522 =
                             let uu____4525 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____4525; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____4522)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____4515  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____4514
                        in
                     let uu____4528 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____4528))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____4550 =
                  let uu____4559 =
                    let uu____4566 =
                      let uu____4567 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____4567  in
                    (uu____4566, [])  in
                  FStar_Pervasives_Native.Some uu____4559  in
                let uu____4576 = ok mlty  in (g, uu____4550, uu____4576)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4589 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4589 with
                 | (g1,x1,uu____4617) ->
                     let uu____4620 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4620))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____4658 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____4658 with
                 | (g1,x1,uu____4686) ->
                     let uu____4689 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4689))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4725 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____4768 =
                  let uu____4777 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____4777 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____4786;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n1;
                          FStar_Extraction_ML_Syntax.mlty = uu____4788;
                          FStar_Extraction_ML_Syntax.loc = uu____4789;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;
                      FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____4791;_}
                      -> (n1, ttys)
                  | uu____4798 -> failwith "Expected a constructor"  in
                (match uu____4768 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____4835 = FStar_Util.first_N nTyVars pats  in
                     (match uu____4835 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___829_4939  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____4970  ->
                                               match uu____4970 with
                                               | (p1,uu____4977) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____4980,t) ->
                                                        term_as_mlty g t
                                                    | uu____4986 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____4990 
                                                              ->
                                                              let uu____4991
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____4991);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____4995 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____4995)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____5024 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____5061  ->
                                   match uu____5061 with
                                   | (p1,imp1) ->
                                       let uu____5083 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____5083 with
                                        | (g2,p2,uu____5114) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____5024 with
                           | (g1,tyMLPats) ->
                               let uu____5178 =
                                 FStar_Util.fold_map
                                   (fun uu____5243  ->
                                      fun uu____5244  ->
                                        match (uu____5243, uu____5244) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____5342 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____5402 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____5342 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____5473 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____5473 with
                                                  | (g3,p2,uu____5516) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____5178 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____5637 =
                                      let uu____5648 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5699  ->
                                                match uu___0_5699 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____5741 -> []))
                                         in
                                      FStar_All.pipe_right uu____5648
                                        FStar_List.split
                                       in
                                    (match uu____5637 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____5817 -> false  in
                                         let uu____5827 =
                                           let uu____5836 =
                                             let uu____5843 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____5846 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____5843, uu____5846)  in
                                           FStar_Pervasives_Native.Some
                                             uu____5836
                                            in
                                         (g2, uu____5827, pat_ty_compat))))))
  
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
            let uu____5978 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____5978 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____6041 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____6089 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____6089
             in
          let uu____6090 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____6090 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____6250,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____6254 =
                  let uu____6266 =
                    let uu____6276 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____6276)  in
                  uu____6266 :: more_args  in
                eta_args uu____6254 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6292,uu____6293)
                -> ((FStar_List.rev more_args), t)
            | uu____6318 ->
                let uu____6319 =
                  let uu____6321 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____6323 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6321 uu____6323
                   in
                failwith uu____6319
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____6358,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____6395 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____6417 = eta_args [] residualType  in
            match uu____6417 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____6475 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____6475
                 | uu____6476 ->
                     let uu____6488 = FStar_List.unzip eargs  in
                     (match uu____6488 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____6534 =
                                   let uu____6535 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____6535
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____6534
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____6545 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____6549,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6553;
                FStar_Extraction_ML_Syntax.loc = uu____6554;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____6577 ->
                    let uu____6580 =
                      let uu____6587 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6587, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6580
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
                     FStar_Extraction_ML_Syntax.mlty = uu____6591;
                     FStar_Extraction_ML_Syntax.loc = uu____6592;_},uu____6593);
                FStar_Extraction_ML_Syntax.mlty = uu____6594;
                FStar_Extraction_ML_Syntax.loc = uu____6595;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____6622 ->
                    let uu____6625 =
                      let uu____6632 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6632, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6625
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6636;
                FStar_Extraction_ML_Syntax.loc = uu____6637;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6645 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6645
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6649;
                FStar_Extraction_ML_Syntax.loc = uu____6650;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6652)) ->
              let uu____6665 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6665
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6669;
                     FStar_Extraction_ML_Syntax.loc = uu____6670;_},uu____6671);
                FStar_Extraction_ML_Syntax.mlty = uu____6672;
                FStar_Extraction_ML_Syntax.loc = uu____6673;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6685 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6685
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6689;
                     FStar_Extraction_ML_Syntax.loc = uu____6690;_},uu____6691);
                FStar_Extraction_ML_Syntax.mlty = uu____6692;
                FStar_Extraction_ML_Syntax.loc = uu____6693;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6695)) ->
              let uu____6712 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6712
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____6718 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6718
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6722)) ->
              let uu____6731 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6731
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6735;
                FStar_Extraction_ML_Syntax.loc = uu____6736;_},uu____6737),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6744 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6744
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6748;
                FStar_Extraction_ML_Syntax.loc = uu____6749;_},uu____6750),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6751)) ->
              let uu____6764 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6764
          | uu____6767 -> mlAppExpr
  
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
        | uu____6798 -> (ml_e, tag)
  
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
      let maybe_generalize uu____6859 =
        match uu____6859 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____6880;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = uu____6884;
            FStar_Syntax_Syntax.lbpos = uu____6885;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____6966 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____7043 =
              FStar_TypeChecker_Util.must_erase_for_extraction
                g.FStar_Extraction_ML_UEnv.env_tcenv lbtyp1
               in
            if uu____7043
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____7129 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____7129 (is_type_binder g) ->
                   let uu____7151 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____7151 with
                    | (bs1,c1) ->
                        let uu____7177 =
                          let uu____7190 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____7236 = is_type_binder g x  in
                                 Prims.op_Negation uu____7236) bs1
                             in
                          match uu____7190 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____7363 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____7363)
                           in
                        (match uu____7177 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____7425 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____7425
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____7474 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____7474 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7526 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____7526 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7629  ->
                                                       fun uu____7630  ->
                                                         match (uu____7629,
                                                                 uu____7630)
                                                         with
                                                         | ((x,uu____7656),
                                                            (y,uu____7658))
                                                             ->
                                                             let uu____7679 =
                                                               let uu____7686
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____7686)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7679)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____7703  ->
                                                       match uu____7703 with
                                                       | (a,uu____7711) ->
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
                                                let uu____7722 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____7741  ->
                                                          match uu____7741
                                                          with
                                                          | (x,uu____7750) ->
                                                              FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                x))
                                                   in
                                                (uu____7722, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____7766 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____7766)
                                                      ||
                                                      (let uu____7769 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____7769)
                                                | uu____7771 -> false  in
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____7833 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____7852  ->
                                           match uu____7852 with
                                           | (a,uu____7860) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____7871 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____7890  ->
                                              match uu____7890 with
                                              | (x,uu____7899) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____7871, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____7943  ->
                                            match uu____7943 with
                                            | (bv,uu____7951) ->
                                                let uu____7956 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____7956
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____7986 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____7999  ->
                                           match uu____7999 with
                                           | (a,uu____8007) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8018 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8037  ->
                                              match uu____8037 with
                                              | (x,uu____8046) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____8018, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8090  ->
                                            match uu____8090 with
                                            | (bv,uu____8098) ->
                                                let uu____8103 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8103
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
                              | FStar_Syntax_Syntax.Tm_name uu____8133 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8146  ->
                                           match uu____8146 with
                                           | (a,uu____8154) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a
                                                 FStar_Pervasives_Native.None)
                                      g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8165 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8184  ->
                                              match uu____8184 with
                                              | (x,uu____8193) ->
                                                  FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                    x))
                                       in
                                    (uu____8165, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8237  ->
                                            match uu____8237 with
                                            | (bv,uu____8245) ->
                                                let uu____8250 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8250
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
                              | uu____8280 -> err_value_restriction lbdef1)))
               | uu____8300 -> no_gen ())
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
           fun uu____8451  ->
             match uu____8451 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____8512 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit is_rec
                    in
                 (match uu____8512 with
                  | (env1,uu____8529,exp_binding) ->
                      let uu____8533 =
                        let uu____8538 = FStar_Util.right lbname  in
                        (uu____8538, exp_binding)  in
                      (env1, uu____8533))) g lbs1
  
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
            (fun uu____8604  ->
               let uu____8605 = FStar_Syntax_Print.term_to_string e  in
               let uu____8607 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____8605
                 uu____8607);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____8614) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8615 ->
               let uu____8620 = term_as_mlexpr g e  in
               (match uu____8620 with
                | (ml_e,tag,t) ->
                    let uu____8634 = maybe_promote_effect ml_e tag t  in
                    (match uu____8634 with
                     | (ml_e1,tag1) ->
                         let uu____8645 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____8645
                         then
                           let uu____8652 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____8652, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____8659 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____8659, ty)
                            | uu____8660 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____8668 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____8668, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____8671 = term_as_mlexpr' g e  in
      match uu____8671 with
      | (e1,f,t) ->
          let uu____8687 = maybe_promote_effect e1 f t  in
          (match uu____8687 with | (e2,f1) -> (e2, f1, t))

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
           let uu____8712 =
             let uu____8714 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____8716 = FStar_Syntax_Print.tag_of_term top  in
             let uu____8718 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____8714 uu____8716 uu____8718
              in
           FStar_Util.print_string uu____8712);
      (let is_match t =
         let uu____8728 =
           let uu____8729 =
             let uu____8732 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____8732 FStar_Syntax_Util.unascribe  in
           uu____8729.FStar_Syntax_Syntax.n  in
         match uu____8728 with
         | FStar_Syntax_Syntax.Tm_match uu____8736 -> true
         | uu____8760 -> false  in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____8779  ->
              match uu____8779 with
              | (t,uu____8788) ->
                  let uu____8793 =
                    let uu____8794 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
                    uu____8794.FStar_Syntax_Syntax.n  in
                  (match uu____8793 with
                   | FStar_Syntax_Syntax.Tm_name uu____8800 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____8802 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____8804 -> true
                   | uu____8806 -> false))
          in
       let apply_to_match_branches head1 args =
         let uu____8845 =
           let uu____8846 =
             let uu____8849 =
               FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____8849 FStar_Syntax_Util.unascribe  in
           uu____8846.FStar_Syntax_Syntax.n  in
         match uu____8845 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee,branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____8973  ->
                       match uu____8973 with
                       | (pat,when_opt,body) ->
                           (pat, when_opt,
                             (let uu___1296_9030 = body  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1296_9030.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1296_9030.FStar_Syntax_Syntax.vars)
                              }))))
                in
             let uu___1299_9045 = head1  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1299_9045.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1299_9045.FStar_Syntax_Syntax.vars)
             }
         | uu____9066 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match"
          in
       let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9077 =
             let uu____9079 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9079
              in
           failwith uu____9077
       | FStar_Syntax_Syntax.Tm_delayed uu____9088 ->
           let uu____9111 =
             let uu____9113 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9113
              in
           failwith uu____9111
       | FStar_Syntax_Syntax.Tm_uvar uu____9122 ->
           let uu____9135 =
             let uu____9137 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9137
              in
           failwith uu____9135
       | FStar_Syntax_Syntax.Tm_bvar uu____9146 ->
           let uu____9147 =
             let uu____9149 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9149
              in
           failwith uu____9147
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9159 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____9159
       | FStar_Syntax_Syntax.Tm_type uu____9160 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9161 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9168 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____9184;_})
           ->
           let uu____9197 =
             let uu____9198 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9198  in
           (match uu____9197 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9205;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9207;
                FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9208;_} ->
                let uu____9211 =
                  let uu____9212 =
                    let uu____9213 =
                      let uu____9220 =
                        let uu____9223 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____9223]  in
                      (fw, uu____9220)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9213  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9212
                   in
                (uu____9211, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9241 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____9241 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9249 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____9249 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____9260 =
                         let uu____9267 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____9267
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____9260 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____9275 =
                         let uu____9286 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____9286]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9275
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9313 =
                    let uu____9320 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____9320 tv  in
                  uu____9313 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____9328 =
                    let uu____9339 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____9339]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9328
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____9366)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9399 =
                  let uu____9406 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.env_tcenv m
                     in
                  FStar_Util.must uu____9406  in
                (match uu____9399 with
                 | (ed,qualifiers) ->
                     let uu____9433 =
                       let uu____9435 =
                         FStar_TypeChecker_Env.is_reifiable_effect
                           g.FStar_Extraction_ML_UEnv.env_tcenv
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____9435  in
                     if uu____9433
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9453 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9455) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9461) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9467 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.env_tcenv t
              in
           (match uu____9467 with
            | (uu____9480,ty,uu____9482) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____9484 =
                  let uu____9485 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9485  in
                (uu____9484, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9486 ->
           let uu____9487 = is_type g t  in
           if uu____9487
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9498 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____9498 with
              | (FStar_Util.Inl uu____9511,uu____9512) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9517;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                   FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9520;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____9538 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____9538, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9539 -> instantiate_maybe_partial x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9541 = is_type g t  in
           if uu____9541
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9552 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____9552 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9561;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;
                    FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____9564;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9572  ->
                        let uu____9573 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____9575 =
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            g.FStar_Extraction_ML_UEnv.currentModule x
                           in
                        let uu____9577 =
                          FStar_Extraction_ML_Code.string_of_mlty
                            g.FStar_Extraction_ML_UEnv.currentModule
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9573 uu____9575 uu____9577);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____9590 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____9590, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9591 -> instantiate_maybe_partial x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____9619 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____9619 with
            | (bs1,body1) ->
                let uu____9632 = binders_as_ml_binders g bs1  in
                (match uu____9632 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9668 =
                             FStar_TypeChecker_Env.is_reifiable_rc
                               env.FStar_Extraction_ML_UEnv.env_tcenv rc
                              in
                           if uu____9668
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.env_tcenv
                               [FStar_TypeChecker_Env.Inlining] body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9676  ->
                                 let uu____9677 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9677);
                            body1)
                        in
                     let uu____9680 = term_as_mlexpr env body2  in
                     (match uu____9680 with
                      | (ml_body,f,t1) ->
                          let uu____9696 =
                            FStar_List.fold_right
                              (fun uu____9716  ->
                                 fun uu____9717  ->
                                   match (uu____9716, uu____9717) with
                                   | ((uu____9740,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____9696 with
                           | (f1,tfun) ->
                               let uu____9763 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____9763, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____9771;
              FStar_Syntax_Syntax.vars = uu____9772;_},(a1,uu____9774)::[])
           ->
           let ty =
             let uu____9814 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____9814  in
           let uu____9815 =
             let uu____9816 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____9816
              in
           (uu____9815, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____9817;
              FStar_Syntax_Syntax.vars = uu____9818;_},(t1,uu____9820)::
            (r,uu____9822)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____9877);
              FStar_Syntax_Syntax.pos = uu____9878;
              FStar_Syntax_Syntax.vars = uu____9879;_},uu____9880)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (is_match head1) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____9939 =
             FStar_All.pipe_right args (apply_to_match_branches head1)  in
           FStar_All.pipe_right uu____9939 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_9993  ->
                        match uu___1_9993 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____9996 -> false)))
              in
           let uu____9998 =
             let uu____10003 =
               let uu____10004 =
                 let uu____10007 =
                   FStar_All.pipe_right head1 FStar_Syntax_Subst.compress  in
                 FStar_All.pipe_right uu____10007 FStar_Syntax_Util.unascribe
                  in
               uu____10004.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____10003)  in
           (match uu____9998 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____10016,uu____10017) ->
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
            | (uu____10031,FStar_Syntax_Syntax.Tm_abs (bs,uu____10033,_rc))
                ->
                let uu____10059 =
                  FStar_All.pipe_right t
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Beta;
                       FStar_TypeChecker_Env.Iota;
                       FStar_TypeChecker_Env.Zeta;
                       FStar_TypeChecker_Env.EraseUniverses;
                       FStar_TypeChecker_Env.AllowUnboundUniverses]
                       g.FStar_Extraction_ML_UEnv.env_tcenv)
                   in
                FStar_All.pipe_right uu____10059 (term_as_mlexpr g)
            | (uu____10066,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____10068 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.env_tcenv
                    [FStar_TypeChecker_Env.Inlining] head1 uu____10068
                   in
                let tm =
                  let uu____10080 =
                    let uu____10085 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____10086 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____10085 uu____10086  in
                  uu____10080 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____10095 ->
                let rec extract_app is_data uu____10148 uu____10149 restArgs
                  =
                  match (uu____10148, uu____10149) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____10230 =
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
                         (fun uu____10257  ->
                            let uu____10258 =
                              let uu____10260 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                uu____10260
                               in
                            let uu____10261 =
                              FStar_Extraction_ML_Code.string_of_mlty
                                g.FStar_Extraction_ML_UEnv.currentModule t1
                               in
                            let uu____10263 =
                              match restArgs with
                              | [] -> "none"
                              | (hd1,uu____10274)::uu____10275 ->
                                  FStar_Syntax_Print.term_to_string hd1
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10258 uu____10261 uu____10263);
                       (match (restArgs, t1) with
                        | ([],uu____10309) ->
                            let app =
                              let uu____10325 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10325
                               in
                            (app, f, t1)
                        | ((arg,uu____10327)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10358 =
                              let uu____10363 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____10363, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10358 rest
                        | ((e0,uu____10375)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____10408 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head1)
                                 in
                              if uu____10408
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____10413 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____10413 with
                             | (e01,tInferred) ->
                                 let uu____10426 =
                                   let uu____10431 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____10431, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10426 rest)
                        | uu____10442 ->
                            let uu____10455 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____10455 with
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
                                  | uu____10527 ->
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
                let extract_app_maybe_projector is_data mlhead uu____10598
                  args1 =
                  match uu____10598 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10628)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10712))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____10714,f',t3)) ->
                                 let uu____10752 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____10752 t3
                             | uu____10753 -> (args2, f1, t2)  in
                           let uu____10778 = remove_implicits args1 f t1  in
                           (match uu____10778 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____10834 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____10858 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____10866 ->
                      let uu____10867 =
                        let uu____10888 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____10888 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____10927  ->
                                  let uu____10928 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____10930 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____10932 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____10934 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____10928 uu____10930 uu____10932
                                    uu____10934);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____10961 -> failwith "FIXME Ty"  in
                      (match uu____10867 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11037)::uu____11038 -> is_type g a
                             | uu____11065 -> false  in
                           let uu____11077 =
                             match vars with
                             | uu____11106::uu____11107 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11121 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____11127 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____11165 =
                                       FStar_List.map
                                         (fun uu____11177  ->
                                            match uu____11177 with
                                            | (x,uu____11185) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____11165, [])
                                   else
                                     (let uu____11208 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____11208 with
                                      | (prefix1,rest) ->
                                          let uu____11297 =
                                            FStar_List.map
                                              (fun uu____11309  ->
                                                 match uu____11309 with
                                                 | (x,uu____11317) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____11297, rest))
                                    in
                                 (match uu____11127 with
                                  | (provided_type_args,rest) ->
                                      let uu____11368 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____11377 ->
                                            let uu____11378 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11378 with
                                             | (head3,uu____11390,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____11392 ->
                                            let uu____11394 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____11394 with
                                             | (head3,uu____11406,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____11409;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____11410;_}::[])
                                            ->
                                            let uu____11413 =
                                              instantiate_maybe_partial head3
                                                (vars, t1) provided_type_args
                                               in
                                            (match uu____11413 with
                                             | (head4,uu____11425,t2) ->
                                                 let uu____11427 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____11427, t2))
                                        | uu____11430 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____11368 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____11077 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11497 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____11497,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11498 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11507 ->
                      let uu____11508 =
                        let uu____11529 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____11529 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11568  ->
                                  let uu____11569 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____11571 =
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11573 =
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      g.FStar_Extraction_ML_UEnv.currentModule
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  let uu____11575 =
                                    FStar_Util.string_of_bool
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                     in
                                  FStar_Util.print4
                                    "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                    uu____11569 uu____11571 uu____11573
                                    uu____11575);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_inst_ok)),
                               q))
                        | uu____11602 -> failwith "FIXME Ty"  in
                      (match uu____11508 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11678)::uu____11679 -> is_type g a
                             | uu____11706 -> false  in
                           let uu____11718 =
                             match vars with
                             | uu____11747::uu____11748 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____11762 ->
                                 let n1 = FStar_List.length vars  in
                                 let uu____11768 =
                                   if (FStar_List.length args) <= n1
                                   then
                                     let uu____11806 =
                                       FStar_List.map
                                         (fun uu____11818  ->
                                            match uu____11818 with
                                            | (x,uu____11826) ->
                                                term_as_mlty g x) args
                                        in
                                     (uu____11806, [])
                                   else
                                     (let uu____11849 =
                                        FStar_Util.first_N n1 args  in
                                      match uu____11849 with
                                      | (prefix1,rest) ->
                                          let uu____11938 =
                                            FStar_List.map
                                              (fun uu____11950  ->
                                                 match uu____11950 with
                                                 | (x,uu____11958) ->
                                                     term_as_mlty g x)
                                              prefix1
                                             in
                                          (uu____11938, rest))
                                    in
                                 (match uu____11768 with
                                  | (provided_type_args,rest) ->
                                      let uu____12009 =
                                        match head_ml.FStar_Extraction_ML_Syntax.expr
                                        with
                                        | FStar_Extraction_ML_Syntax.MLE_Name
                                            uu____12018 ->
                                            let uu____12019 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12019 with
                                             | (head3,uu____12031,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_Var
                                            uu____12033 ->
                                            let uu____12035 =
                                              instantiate_maybe_partial
                                                head_ml (vars, t1)
                                                provided_type_args
                                               in
                                            (match uu____12035 with
                                             | (head3,uu____12047,t2) ->
                                                 (head3, t2))
                                        | FStar_Extraction_ML_Syntax.MLE_App
                                            (head3,{
                                                     FStar_Extraction_ML_Syntax.expr
                                                       =
                                                       FStar_Extraction_ML_Syntax.MLE_Const
                                                       (FStar_Extraction_ML_Syntax.MLC_Unit
                                                       );
                                                     FStar_Extraction_ML_Syntax.mlty
                                                       = uu____12050;
                                                     FStar_Extraction_ML_Syntax.loc
                                                       = uu____12051;_}::[])
                                            ->
                                            let uu____12054 =
                                              instantiate_maybe_partial head3
                                                (vars, t1) provided_type_args
                                               in
                                            (match uu____12054 with
                                             | (head4,uu____12066,t2) ->
                                                 let uu____12068 =
                                                   FStar_All.pipe_right
                                                     (FStar_Extraction_ML_Syntax.MLE_App
                                                        (head4,
                                                          [FStar_Extraction_ML_Syntax.ml_unit]))
                                                     (FStar_Extraction_ML_Syntax.with_ty
                                                        t2)
                                                    in
                                                 (uu____12068, t2))
                                        | uu____12071 ->
                                            failwith
                                              "Impossible: Unexpected head term"
                                         in
                                      (match uu____12009 with
                                       | (head3,t2) -> (head3, t2, rest)))
                              in
                           (match uu____11718 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12138 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____12138,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12139 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12148 ->
                      let uu____12149 = term_as_mlexpr g head2  in
                      (match uu____12149 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____12165 = is_type g t  in
                if uu____12165
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12176 =
                     let uu____12177 = FStar_Syntax_Util.un_uinst head1  in
                     uu____12177.FStar_Syntax_Syntax.n  in
                   match uu____12176 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12187 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____12187 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12196 -> extract_app_with_instantiations ())
                   | uu____12199 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____12202),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12267 =
                   maybe_reify_comp g g.FStar_Extraction_ML_UEnv.env_tcenv c
                    in
                 term_as_mlty g uu____12267
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____12271 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____12271 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____12306 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12322 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____12322
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____12337 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____12337  in
                   let lb1 =
                     let uu___1738_12339 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1738_12339.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1738_12339.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1738_12339.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1738_12339.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1738_12339.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1738_12339.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____12306 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____12373 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.env_tcenv
                                uu____12373
                               in
                            let lbdef =
                              let uu____12388 = FStar_Options.ml_ish ()  in
                              if uu____12388
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____12400 =
                                   FStar_TypeChecker_Normalize.normalize
                                     (FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                     :: extraction_norm_steps) tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____12401 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____12401
                                 then
                                   ((let uu____12411 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu____12413 =
                                       FStar_Syntax_Print.term_to_string
                                         lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     FStar_Util.print2
                                       "Starting to normalize top-level let %s)\n\tlbdef=%s"
                                       uu____12411 uu____12413);
                                    (let a =
                                       let uu____12419 =
                                         let uu____12421 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____12421
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____12419 norm_call
                                        in
                                     (let uu____12427 =
                                        FStar_Syntax_Print.term_to_string a
                                         in
                                      FStar_Util.print1 "Normalized to %s\n"
                                        uu____12427);
                                     a))
                                 else norm_call ())
                               in
                            let uu___1756_12432 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1756_12432.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1756_12432.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1756_12432.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1756_12432.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1756_12432.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1756_12432.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____12485 =
                  match uu____12485 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____12641  ->
                               match uu____12641 with
                               | (a,uu____12649) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____12655 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____12655 with
                       | (e1,ty) ->
                           let uu____12666 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____12666 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____12678 -> []  in
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
                let uu____12709 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____12806  ->
                         match uu____12806 with
                         | (env,lbs4) ->
                             let uu____12940 = lb  in
                             (match uu____12940 with
                              | (lbname,uu____12991,(t1,(uu____12993,polytype)),add_unit,uu____12996)
                                  ->
                                  let uu____13011 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____13011 with
                                   | (env1,nm,uu____13052) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____12709 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____13331 = term_as_mlexpr env_body e'1  in
                     (match uu____13331 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____13348 =
                              let uu____13351 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____13351  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13348
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____13364 =
                            let uu____13365 =
                              let uu____13366 =
                                let uu____13367 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____13367)  in
                              mk_MLE_Let top_level uu____13366 e'2  in
                            let uu____13376 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13365 uu____13376
                             in
                          (uu____13364, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____13415 = term_as_mlexpr g scrutinee  in
           (match uu____13415 with
            | (e,f_e,t_e) ->
                let uu____13431 = check_pats_for_ite pats  in
                (match uu____13431 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____13496 = term_as_mlexpr g then_e1  in
                            (match uu____13496 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____13512 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____13512 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____13528 =
                                        let uu____13539 =
                                          type_leq g t_then t_else  in
                                        if uu____13539
                                        then (t_else, no_lift)
                                        else
                                          (let uu____13560 =
                                             type_leq g t_else t_then  in
                                           if uu____13560
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____13528 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____13607 =
                                             let uu____13608 =
                                               let uu____13609 =
                                                 let uu____13618 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____13619 =
                                                   let uu____13622 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____13622
                                                    in
                                                 (e, uu____13618,
                                                   uu____13619)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____13609
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____13608
                                              in
                                           let uu____13625 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____13607, uu____13625,
                                             t_branch))))
                        | uu____13626 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____13644 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____13743 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____13743 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____13788 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____13788 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____13850 =
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
                                                   let uu____13873 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____13873 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____13850 with
                                              | (when_opt1,f_when) ->
                                                  let uu____13923 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____13923 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____13958 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14035 
                                                                 ->
                                                                 match uu____14035
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
                                                         uu____13958)))))
                               true)
                           in
                        match uu____13644 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14206  ->
                                      let uu____14207 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____14209 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14207 uu____14209);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14236 =
                                   let uu____14237 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14237
                                    in
                                 (match uu____14236 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14244;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14246;
                                      FStar_Extraction_ML_UEnv.exp_b_inst_ok
                                        = uu____14247;_}
                                      ->
                                      let uu____14250 =
                                        let uu____14251 =
                                          let uu____14252 =
                                            let uu____14259 =
                                              let uu____14262 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____14262]  in
                                            (fw, uu____14259)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14252
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14251
                                         in
                                      (uu____14250,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14266,uu____14267,(uu____14268,f_first,t_first))::rest
                                 ->
                                 let uu____14328 =
                                   FStar_List.fold_left
                                     (fun uu____14370  ->
                                        fun uu____14371  ->
                                          match (uu____14370, uu____14371)
                                          with
                                          | ((topt,f),(uu____14428,uu____14429,
                                                       (uu____14430,f_branch,t_branch)))
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
                                                    let uu____14486 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____14486
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____14493 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____14493
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
                                 (match uu____14328 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____14591  ->
                                                match uu____14591 with
                                                | (p,(wopt,uu____14620),
                                                   (b1,uu____14622,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____14641 -> b1
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
                                      let uu____14646 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____14646, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____14673 =
          let uu____14678 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.env_tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____14678  in
        match uu____14673 with
        | (uu____14703,fstar_disc_type) ->
            let wildcards =
              let uu____14713 =
                let uu____14714 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____14714.FStar_Syntax_Syntax.n  in
              match uu____14713 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14725) ->
                  let uu____14746 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_14780  ->
                            match uu___2_14780 with
                            | (uu____14788,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____14789)) ->
                                true
                            | uu____14794 -> false))
                     in
                  FStar_All.pipe_right uu____14746
                    (FStar_List.map
                       (fun uu____14830  ->
                          let uu____14837 = fresh "_"  in
                          (uu____14837, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____14841 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____14856 =
                let uu____14857 =
                  let uu____14869 =
                    let uu____14870 =
                      let uu____14871 =
                        let uu____14886 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____14892 =
                          let uu____14903 =
                            let uu____14912 =
                              let uu____14913 =
                                let uu____14920 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____14920,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____14913
                               in
                            let uu____14923 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____14912, FStar_Pervasives_Native.None,
                              uu____14923)
                             in
                          let uu____14927 =
                            let uu____14938 =
                              let uu____14947 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____14947)
                               in
                            [uu____14938]  in
                          uu____14903 :: uu____14927  in
                        (uu____14886, uu____14892)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____14871  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____14870
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____14869)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____14857  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____14856
               in
            let uu____15008 =
              let uu____15009 =
                let uu____15012 =
                  let uu____15013 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____15013;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____15012]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____15009)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____15008
  