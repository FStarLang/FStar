open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____6 -> false
  
let (type_leq :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        FStar_Extraction_ML_Util.type_leq
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
  
let (type_leq_c :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool,FStar_Extraction_ML_Syntax.mlexpr
                        FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        FStar_Extraction_ML_Util.type_leq_c
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
  
let (eraseTypeDeep :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      FStar_Extraction_ML_Util.eraseTypeDeep
        (FStar_Extraction_ML_Util.udelta_unfold g) t
  
let record_fields :
  'Auu____68 .
    FStar_Ident.ident Prims.list ->
      'Auu____68 Prims.list ->
        (Prims.string,'Auu____68) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
  
let fail :
  'Auu____107 .
    FStar_Range.range ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2 ->
        'Auu____107
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_uninst :
  'Auu____136 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (Prims.string Prims.list,FStar_Extraction_ML_Syntax.mlty)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.term -> 'Auu____136
  =
  fun env  ->
    fun t  ->
      fun uu____161  ->
        fun app  ->
          match uu____161 with
          | (vars,ty) ->
              let uu____175 =
                let uu____180 =
                  let uu____181 = FStar_Syntax_Print.term_to_string t  in
                  let uu____182 =
                    FStar_All.pipe_right vars (FStar_String.concat ", ")  in
                  let uu____185 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      env.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  let uu____186 = FStar_Syntax_Print.term_to_string app  in
                  FStar_Util.format4
                    "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                    uu____181 uu____182 uu____185 uu____186
                   in
                (FStar_Errors.Fatal_Uninstantiated, uu____180)  in
              fail t.FStar_Syntax_Syntax.pos uu____175
  
let err_ill_typed_application :
  'Auu____199 'Auu____200 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,'Auu____199) FStar_Pervasives_Native.tuple2
          Prims.list -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____200
  =
  fun env  ->
    fun t  ->
      fun args  ->
        fun ty  ->
          let uu____233 =
            let uu____238 =
              let uu____239 = FStar_Syntax_Print.term_to_string t  in
              let uu____240 =
                let uu____241 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____259  ->
                          match uu____259 with
                          | (x,uu____265) ->
                              FStar_Syntax_Print.term_to_string x))
                   in
                FStar_All.pipe_right uu____241 (FStar_String.concat " ")  in
              let uu____268 =
                FStar_Extraction_ML_Code.string_of_mlty
                  env.FStar_Extraction_ML_UEnv.currentModule ty
                 in
              FStar_Util.format3
                "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
                uu____239 uu____240 uu____268
               in
            (FStar_Errors.Fatal_IllTyped, uu____238)  in
          fail t.FStar_Syntax_Syntax.pos uu____233
  
let err_ill_typed_erasure :
  'Auu____277 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Range.range -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____277
  =
  fun env  ->
    fun pos  ->
      fun ty  ->
        let uu____293 =
          let uu____298 =
            let uu____299 =
              FStar_Extraction_ML_Code.string_of_mlty
                env.FStar_Extraction_ML_UEnv.currentModule ty
               in
            FStar_Util.format1
              "Erased value found where a value of type %s was expected"
              uu____299
             in
          (FStar_Errors.Fatal_IllTyped, uu____298)  in
        fail pos uu____293
  
let err_value_restriction :
  'Auu____304 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____304
  =
  fun t  ->
    let uu____314 =
      let uu____319 =
        let uu____320 = FStar_Syntax_Print.tag_of_term t  in
        let uu____321 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____320 uu____321
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____319)  in
    fail t.FStar_Syntax_Syntax.pos uu____314
  
let (err_unexpected_eff :
  FStar_Extraction_ML_UEnv.env ->
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
            let uu____351 =
              let uu____356 =
                let uu____357 = FStar_Syntax_Print.term_to_string t  in
                let uu____358 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____359 = FStar_Extraction_ML_Util.eff_to_string f0  in
                let uu____360 = FStar_Extraction_ML_Util.eff_to_string f1  in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____357 uu____358 uu____359 uu____360
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____356)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____351
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____383 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____383 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____388 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____388 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____409,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____449 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____449
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____451 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____451
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.tcenv l1
               in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____474 =
                  FStar_All.pipe_right qualifiers
                    (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                   in
                if uu____474
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____495 =
        let uu____496 = FStar_Syntax_Subst.compress t1  in
        uu____496.FStar_Syntax_Syntax.n  in
      match uu____495 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____499 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____522 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____549 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____557 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____557
      | FStar_Syntax_Syntax.Tm_uvar uu____558 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____571 -> false
      | FStar_Syntax_Syntax.Tm_name uu____572 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____573 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____580 -> false
      | FStar_Syntax_Syntax.Tm_type uu____581 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____582,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____604 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1
             in
          let uu____606 =
            let uu____607 = FStar_Syntax_Subst.compress t2  in
            uu____607.FStar_Syntax_Syntax.n  in
          (match uu____606 with
           | FStar_Syntax_Syntax.Tm_fvar uu____610 -> false
           | uu____611 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____612 ->
          let uu____629 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____629 with | (head1,uu____647) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____673) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____683) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____688,body,uu____690) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____715,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____733,branches) ->
          (match branches with
           | (uu____771,uu____772,e)::uu____774 -> is_arity env e
           | uu____821 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____849 ->
          let uu____872 =
            let uu____873 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____873  in
          failwith uu____872
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____874 =
            let uu____875 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____875  in
          failwith uu____874
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____877 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____877
      | FStar_Syntax_Syntax.Tm_constant uu____878 -> false
      | FStar_Syntax_Syntax.Tm_type uu____879 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____880 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____887 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____904;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____905;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____906;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____908;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____909;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____910;_},s)
          ->
          let uu____950 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____950
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____951;
            FStar_Syntax_Syntax.index = uu____952;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____956;
            FStar_Syntax_Syntax.index = uu____957;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____962,uu____963) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1005) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____1016) ->
          let uu____1041 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____1041 with
           | (uu____1046,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____1083 =
            let uu____1088 =
              let uu____1089 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1089]  in
            FStar_Syntax_Subst.open_term uu____1088 body  in
          (match uu____1083 with
           | (uu____1108,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1130,lbs),body) ->
          let uu____1147 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____1147 with
           | (uu____1154,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1164,branches) ->
          (match branches with
           | b::uu____1203 ->
               let uu____1248 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1248 with
                | (uu____1249,uu____1250,e) -> is_type_aux env e)
           | uu____1268 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1285 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1293) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1299) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1338  ->
           let uu____1339 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1340 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1339
             uu____1340);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1346  ->
            if b
            then
              let uu____1347 = FStar_Syntax_Print.term_to_string t  in
              let uu____1348 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1347 uu____1348
            else
              (let uu____1350 = FStar_Syntax_Print.term_to_string t  in
               let uu____1351 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1350 uu____1351));
       b)
  
let is_type_binder :
  'Auu____1358 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1358) FStar_Pervasives_Native.tuple2 ->
        Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1382 =
      let uu____1383 = FStar_Syntax_Subst.compress t  in
      uu____1383.FStar_Syntax_Syntax.n  in
    match uu____1382 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1386;
          FStar_Syntax_Syntax.fv_delta = uu____1387;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1388;
          FStar_Syntax_Syntax.fv_delta = uu____1389;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1390);_}
        -> true
    | uu____1397 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1403 =
      let uu____1404 = FStar_Syntax_Subst.compress t  in
      uu____1404.FStar_Syntax_Syntax.n  in
    match uu____1403 with
    | FStar_Syntax_Syntax.Tm_constant uu____1407 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1408 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1409 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1410 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1455 = is_constructor head1  in
        if uu____1455
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1473  ->
                  match uu____1473 with
                  | (te,uu____1481) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1488) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1494,uu____1495) ->
        is_fstar_value t1
    | uu____1536 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1542 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1543 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1544 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1545 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1556,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1577,fields) ->
        FStar_Util.for_all
          (fun uu____1602  ->
             match uu____1602 with | (uu____1607,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1610) -> is_ml_value h
    | uu____1615 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1658 =
       let uu____1659 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____1659  in
     Prims.strcat x uu____1658)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1780 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1782 = FStar_Syntax_Util.is_fun e'  in
          if uu____1782
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
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.term FStar_Pervasives_Native.option,
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3)
  =
  fun l  ->
    let def =
      (false, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)  in
    if (FStar_List.length l) <> (Prims.parse_int "2")
    then def
    else
      (let uu____1872 = FStar_List.hd l  in
       match uu____1872 with
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
                 | uu____2033 -> def)))
  
let (instantiate :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  = fun s  -> fun args  -> FStar_Extraction_ML_Util.subst s args 
let (eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun t  ->
    fun e  ->
      let uu____2074 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2074 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____2094  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____2105 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____2119  ->
                    match uu____2119 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____2105
                in
             let body =
               FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r)
                 (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es))
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
  
let (default_value_for_ty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g  ->
    fun t  ->
      let uu____2145 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2145 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____2165 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____2165 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2169 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____2177  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____2185 =
               let uu____2186 =
                 let uu____2197 = body r  in (vs_ts, uu____2197)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____2186  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____2185)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____2214 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____2216 = FStar_Options.codegen ()  in
           uu____2216 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____2214 then e else eta_expand expect e
  
let maybe_coerce :
  'Auu____2234 .
    'Auu____2234 ->
      FStar_Extraction_ML_UEnv.env ->
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
            let uu____2261 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____2261 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____2271 ->
                (FStar_Extraction_ML_UEnv.debug g
                   (fun uu____2283  ->
                      let uu____2284 =
                        FStar_Extraction_ML_Code.string_of_mlexpr
                          g.FStar_Extraction_ML_UEnv.currentModule e
                         in
                      let uu____2285 =
                        FStar_Extraction_ML_Code.string_of_mlty
                          g.FStar_Extraction_ML_UEnv.currentModule ty1
                         in
                      let uu____2286 =
                        FStar_Extraction_ML_Code.string_of_mlty
                          g.FStar_Extraction_ML_UEnv.currentModule expect
                         in
                      FStar_Util.print3
                        "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                        uu____2284 uu____2285 uu____2286);
                 (match ty1 with
                  | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                      default_value_for_ty g expect
                  | uu____2287 ->
                      let uu____2288 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty expect)
                          (FStar_Extraction_ML_Syntax.MLE_Coerce
                             (e, ty1, expect))
                         in
                      maybe_eta_expand expect uu____2288))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____2299 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____2299 with
      | FStar_Util.Inl (uu____2300,t) -> t
      | uu____2320 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let (basic_norm_steps : FStar_TypeChecker_Env.step Prims.list) =
  [FStar_TypeChecker_Env.Beta;
  FStar_TypeChecker_Env.Eager_unfolding;
  FStar_TypeChecker_Env.Iota;
  FStar_TypeChecker_Env.Zeta;
  FStar_TypeChecker_Env.Inlining;
  FStar_TypeChecker_Env.EraseUniverses;
  FStar_TypeChecker_Env.AllowUnboundUniverses] 
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2336 -> c
    | FStar_Syntax_Syntax.GTotal uu____2345 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____2381  ->
               match uu____2381 with
               | (uu____2396,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___348_2409 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___348_2409.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___348_2409.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___348_2409.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___348_2409.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___349_2413 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___349_2413.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___349_2413.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let arg_as_mlty g1 uu____2460 =
        match uu____2460 with
        | (a,uu____2468) ->
            let uu____2473 = is_type g1 a  in
            if uu____2473
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____2491 =
          let uu____2492 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____2492  in
        if uu____2491
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____2494 =
             let uu____2509 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____2509 with
             | ((uu____2532,fvty),uu____2534) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant]
                     g1.FStar_Extraction_ML_UEnv.tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____2494 with
           | (formals,uu____2553) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____2609 = FStar_Util.first_N n_args formals  in
                   match uu____2609 with
                   | (uu____2642,rest) ->
                       let uu____2676 =
                         FStar_List.map
                           (fun uu____2686  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____2676
                 else mlargs  in
               let nm =
                 let uu____2695 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____2695 with
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
        | FStar_Syntax_Syntax.Tm_type uu____2731 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____2732 ->
            let uu____2733 =
              let uu____2734 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2734
               in
            failwith uu____2733
        | FStar_Syntax_Syntax.Tm_delayed uu____2735 ->
            let uu____2758 =
              let uu____2759 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2759
               in
            failwith uu____2758
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____2760 =
              let uu____2761 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2761
               in
            failwith uu____2760
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____2763 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____2763
        | FStar_Syntax_Syntax.Tm_constant uu____2764 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____2765 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____2772 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2786) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____2791;
               FStar_Syntax_Syntax.index = uu____2792;
               FStar_Syntax_Syntax.sort = t2;_},uu____2794)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2802) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2812,uu____2813) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____2886 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____2886 with
             | (bs1,c1) ->
                 let uu____2913 = binders_as_ml_binders env bs1  in
                 (match uu____2913 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let c2 = comp_no_args c1  in
                        let uu____2943 =
                          let uu____2950 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.tcenv eff
                             in
                          FStar_Util.must uu____2950  in
                        match uu____2943 with
                        | (ed,qualifiers) ->
                            let uu____2971 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____2971
                            then
                              let t2 =
                                FStar_TypeChecker_Env.reify_comp
                                  env1.FStar_Extraction_ML_UEnv.tcenv c2
                                  FStar_Syntax_Syntax.U_unknown
                                 in
                              (FStar_Extraction_ML_UEnv.debug env1
                                 (fun uu____2979  ->
                                    let uu____2980 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    let uu____2981 =
                                      FStar_Syntax_Print.term_to_string t2
                                       in
                                    FStar_Util.print2
                                      "Translating comp type %s as %s\n"
                                      uu____2980 uu____2981);
                               (let res = translate_term_to_mlty env1 t2  in
                                FStar_Extraction_ML_UEnv.debug env1
                                  (fun uu____2988  ->
                                     let uu____2989 =
                                       FStar_Syntax_Print.comp_to_string c2
                                        in
                                     let uu____2990 =
                                       FStar_Syntax_Print.term_to_string t2
                                        in
                                     let uu____2991 =
                                       FStar_Extraction_ML_Code.string_of_mlty
                                         env1.FStar_Extraction_ML_UEnv.currentModule
                                         res
                                        in
                                     FStar_Util.print3
                                       "Translated comp type %s as %s ... to %s\n"
                                       uu____2989 uu____2990 uu____2991);
                                res))
                            else
                              translate_term_to_mlty env1
                                (FStar_Syntax_Util.comp_result c2)
                         in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____2994 =
                        FStar_List.fold_right
                          (fun uu____3013  ->
                             fun uu____3014  ->
                               match (uu____3013, uu____3014) with
                               | ((uu____3035,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____2994 with | (uu____3047,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____3076 =
                let uu____3077 = FStar_Syntax_Util.un_uinst head1  in
                uu____3077.FStar_Syntax_Syntax.n  in
              match uu____3076 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____3108 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____3108
              | uu____3129 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____3132) ->
            let uu____3157 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____3157 with
             | (bs1,ty1) ->
                 let uu____3184 = binders_as_ml_binders env bs1  in
                 (match uu____3184 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____3209 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____3222 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____3251 ->
            let uu____3258 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____3258 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____3262 -> false  in
      let uu____3263 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.tcenv t0
         in
      if uu____3263
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____3266 = is_top_ty mlt  in
         if uu____3266
         then
           let t =
             FStar_TypeChecker_Normalize.normalize
               ((FStar_TypeChecker_Env.UnfoldUntil
                   FStar_Syntax_Syntax.delta_constant) :: basic_norm_steps)
               g.FStar_Extraction_ML_UEnv.tcenv t0
              in
           aux g t
         else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Extraction_ML_UEnv.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun bs  ->
      let uu____3281 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____3334  ->
                fun b  ->
                  match uu____3334 with
                  | (ml_bs,env) ->
                      let uu____3376 = is_type_binder g b  in
                      if uu____3376
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____3398 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____3398, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____3414 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____3414 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____3436 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____3436, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____3281 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize basic_norm_steps
          g.FStar_Extraction_ML_UEnv.tcenv t0
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____3519) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____3522,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____3526 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____3560 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____3561 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____3562 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____3571 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____3610 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____3610 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____3614 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____3641 -> p))
      | uu____3644 -> p
  
let rec (extract_one_pat :
  Prims.bool ->
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.pat ->
        FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option ->
          (FStar_Extraction_ML_UEnv.env ->
             FStar_Syntax_Syntax.term ->
               (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
                 FStar_Extraction_ML_Syntax.mlty)
                 FStar_Pervasives_Native.tuple3)
            ->
            (FStar_Extraction_ML_UEnv.env,(FStar_Extraction_ML_Syntax.mlpattern,
                                            FStar_Extraction_ML_Syntax.mlexpr
                                              Prims.list)
                                            FStar_Pervasives_Native.tuple2
                                            FStar_Pervasives_Native.option,
              Prims.bool) FStar_Pervasives_Native.tuple3)
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
                       (fun uu____3736  ->
                          let uu____3737 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____3738 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____3737 uu____3738)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____3768 = FStar_Options.codegen ()  in
                uu____3768 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____3773 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3786 =
                        let uu____3787 =
                          let uu____3788 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____3788  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____3787
                         in
                      (uu____3786, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____3809 = term_as_mlexpr g source_term  in
                      (match uu____3809 with
                       | (mlterm,uu____3821,mlty) -> (mlterm, mlty))
                   in
                (match uu____3773 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____3841 =
                         let uu____3842 =
                           let uu____3849 =
                             let uu____3852 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____3852; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____3849)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____3842  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3841
                        in
                     let uu____3855 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____3855))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____3875 =
                  let uu____3884 =
                    let uu____3891 =
                      let uu____3892 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____3892  in
                    (uu____3891, [])  in
                  FStar_Pervasives_Native.Some uu____3884  in
                let uu____3901 = ok mlty  in (g, uu____3875, uu____3901)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3912 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3912 with
                 | (g1,x1) ->
                     let uu____3933 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3933))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3967 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3967 with
                 | (g1,x1) ->
                     let uu____3988 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3988))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4020 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____4059 =
                  let uu____4068 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____4068 with
                  | FStar_Util.Inr
                      (uu____4077,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____4079;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____4080;_},ttys,uu____4082)
                      -> (n1, ttys)
                  | uu____4117 -> failwith "Expected a constructor"  in
                (match uu____4059 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____4151 = FStar_Util.first_N nTyVars pats  in
                     (match uu____4151 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___351_4251  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____4280  ->
                                               match uu____4280 with
                                               | (p1,uu____4286) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____4287,t) ->
                                                        term_as_mlty g t
                                                    | uu____4293 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____4297 
                                                              ->
                                                              let uu____4298
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____4298);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____4300 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____4300)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____4329 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____4365  ->
                                   match uu____4365 with
                                   | (p1,imp1) ->
                                       let uu____4384 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____4384 with
                                        | (g2,p2,uu____4413) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____4329 with
                           | (g1,tyMLPats) ->
                               let uu____4474 =
                                 FStar_Util.fold_map
                                   (fun uu____4538  ->
                                      fun uu____4539  ->
                                        match (uu____4538, uu____4539) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____4632 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____4692 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____4632 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____4763 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____4763 with
                                                  | (g3,p2,uu____4804) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____4474 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____4922 =
                                      let uu____4933 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___345_4984  ->
                                                match uu___345_4984 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____5026 -> []))
                                         in
                                      FStar_All.pipe_right uu____4933
                                        FStar_List.split
                                       in
                                    (match uu____4922 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____5099 -> false  in
                                         let uu____5108 =
                                           let uu____5117 =
                                             let uu____5124 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____5127 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____5124, uu____5127)  in
                                           FStar_Pervasives_Native.Some
                                             uu____5117
                                            in
                                         (g2, uu____5108, pat_ty_compat))))))
  
let (extract_pat :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_UEnv.env ->
           FStar_Syntax_Syntax.term ->
             (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
               FStar_Extraction_ML_Syntax.mlty)
               FStar_Pervasives_Native.tuple3)
          ->
          (FStar_Extraction_ML_UEnv.env,(FStar_Extraction_ML_Syntax.mlpattern,
                                          FStar_Extraction_ML_Syntax.mlexpr
                                            FStar_Pervasives_Native.option)
                                          FStar_Pervasives_Native.tuple2
                                          Prims.list,Prims.bool)
            FStar_Pervasives_Native.tuple3)
  =
  fun g  ->
    fun p  ->
      fun expected_t  ->
        fun term_as_mlexpr  ->
          let extract_one_pat1 g1 p1 expected_t1 =
            let uu____5254 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____5254 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____5311 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____5356 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____5356
             in
          let uu____5357 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____5357 with
          | (g1,(p1,whens),b) ->
              let when_clause = mk_when_clause whens  in
              (g1, [(p1, when_clause)], b)
  
let (maybe_eta_data_and_project_record :
  FStar_Extraction_ML_UEnv.env ->
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____5507,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____5510 =
                  let uu____5521 =
                    let uu____5530 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____5530)  in
                  uu____5521 :: more_args  in
                eta_args uu____5510 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____5543,uu____5544)
                -> ((FStar_List.rev more_args), t)
            | uu____5579 ->
                let uu____5580 =
                  let uu____5581 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____5582 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____5581 uu____5582
                   in
                failwith uu____5580
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____5614,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____5658 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____5680 = eta_args [] residualType  in
            match uu____5680 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____5733 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____5733
                 | uu____5734 ->
                     let uu____5745 = FStar_List.unzip eargs  in
                     (match uu____5745 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____5799 =
                                   let uu____5800 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____5800
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____5799
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____5809 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____5812,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5816;
                FStar_Extraction_ML_Syntax.loc = uu____5817;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5838 ->
                    let uu____5841 =
                      let uu____5848 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5848, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5841
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
                     FStar_Extraction_ML_Syntax.mlty = uu____5852;
                     FStar_Extraction_ML_Syntax.loc = uu____5853;_},uu____5854);
                FStar_Extraction_ML_Syntax.mlty = uu____5855;
                FStar_Extraction_ML_Syntax.loc = uu____5856;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5881 ->
                    let uu____5884 =
                      let uu____5891 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5891, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5884
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5895;
                FStar_Extraction_ML_Syntax.loc = uu____5896;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5904 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5904
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5908;
                FStar_Extraction_ML_Syntax.loc = uu____5909;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5911)) ->
              let uu____5924 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5924
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5928;
                     FStar_Extraction_ML_Syntax.loc = uu____5929;_},uu____5930);
                FStar_Extraction_ML_Syntax.mlty = uu____5931;
                FStar_Extraction_ML_Syntax.loc = uu____5932;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5944 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5944
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5948;
                     FStar_Extraction_ML_Syntax.loc = uu____5949;_},uu____5950);
                FStar_Extraction_ML_Syntax.mlty = uu____5951;
                FStar_Extraction_ML_Syntax.loc = uu____5952;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5954)) ->
              let uu____5971 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5971
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5977 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5977
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5981)) ->
              let uu____5990 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5990
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5994;
                FStar_Extraction_ML_Syntax.loc = uu____5995;_},uu____5996),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6003 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6003
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6007;
                FStar_Extraction_ML_Syntax.loc = uu____6008;_},uu____6009),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6010)) ->
              let uu____6023 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6023
          | uu____6026 -> mlAppExpr
  
let (maybe_promote_effect :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag)
          FStar_Pervasives_Native.tuple2)
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
        | uu____6056 -> (ml_e, tag)
  
let rec (check_term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlty)
            FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun e  ->
      fun f  ->
        fun ty  ->
          FStar_Extraction_ML_UEnv.debug g
            (fun uu____6121  ->
               let uu____6122 = FStar_Syntax_Print.term_to_string e  in
               let uu____6123 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____6122
                 uu____6123);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____6128) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____6129 ->
               let uu____6134 = term_as_mlexpr g e  in
               (match uu____6134 with
                | (ml_e,tag,t) ->
                    let uu____6148 = maybe_promote_effect ml_e tag t  in
                    (match uu____6148 with
                     | (ml_e1,tag1) ->
                         let uu____6159 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____6159
                         then
                           let uu____6164 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____6164, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____6170 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____6170, ty)
                            | uu____6171 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____6179 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____6179, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g  ->
    fun e  ->
      let uu____6182 = term_as_mlexpr' g e  in
      match uu____6182 with
      | (e1,f,t) ->
          let uu____6198 = maybe_promote_effect e1 f t  in
          (match uu____6198 with | (e2,f1) -> (e2, f1, t))

and (term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g  ->
    fun top  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____6223 =
             let uu____6224 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____6225 = FStar_Syntax_Print.tag_of_term top  in
             let uu____6226 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____6224 uu____6225 uu____6226
              in
           FStar_Util.print_string uu____6223);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6234 =
             let uu____6235 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____6235
              in
           failwith uu____6234
       | FStar_Syntax_Syntax.Tm_delayed uu____6242 ->
           let uu____6265 =
             let uu____6266 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____6266
              in
           failwith uu____6265
       | FStar_Syntax_Syntax.Tm_uvar uu____6273 ->
           let uu____6286 =
             let uu____6287 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____6287
              in
           failwith uu____6286
       | FStar_Syntax_Syntax.Tm_bvar uu____6294 ->
           let uu____6295 =
             let uu____6296 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____6296
              in
           failwith uu____6295
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____6304 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____6304
       | FStar_Syntax_Syntax.Tm_type uu____6305 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____6306 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____6313 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____6329;_})
           ->
           let uu____6342 =
             let uu____6351 =
               let uu____6368 =
                 FStar_Syntax_Syntax.lid_as_fv
                   FStar_Parser_Const.failwith_lid
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.lookup_fv g uu____6368  in
             FStar_All.pipe_left FStar_Util.right uu____6351  in
           (match uu____6342 with
            | (uu____6411,fw,uu____6413,uu____6414) ->
                let uu____6415 =
                  let uu____6416 =
                    let uu____6417 =
                      let uu____6424 =
                        let uu____6427 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____6427]  in
                      (fw, uu____6424)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6417  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____6416
                   in
                (uu____6415, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____6444 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____6444 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____6452 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____6452 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____6469 =
                         FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                       FStar_Syntax_Embeddings.embed uu____6469
                         t.FStar_Syntax_Syntax.pos
                         (FStar_Reflection_Data.Tv_Var bv)
                        in
                     let t1 =
                       let uu____6475 =
                         let uu____6486 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____6486]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____6475
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____6513 =
                    FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                  FStar_Syntax_Embeddings.embed uu____6513
                    t.FStar_Syntax_Syntax.pos tv
                   in
                let t1 =
                  let uu____6519 =
                    let uu____6530 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____6530]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____6519
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           FStar_Errors.raise_err
             (FStar_Errors.Error_NoLetMutable,
               "let-mutable no longer supported")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____6568)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____6598 =
                  let uu____6605 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m
                     in
                  FStar_Util.must uu____6605  in
                (match uu____6598 with
                 | (ed,qualifiers) ->
                     let uu____6632 =
                       let uu____6633 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                          in
                       FStar_All.pipe_right uu____6633 Prims.op_Negation  in
                     if uu____6632
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____6649 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6651) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6657) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6667 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____6667 with
            | (uu____6680,ty,uu____6682) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____6692 =
                  let uu____6693 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____6693  in
                (uu____6692, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____6694 ->
           let uu____6695 = is_type g t  in
           if uu____6695
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6703 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____6703 with
              | (FStar_Util.Inl uu____6716,uu____6717) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____6766,x,mltys,uu____6769),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____6839 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____6839, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6840 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____6854 = is_type g t  in
           if uu____6854
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6862 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____6862 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____6893) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | FStar_Pervasives_Native.Some (FStar_Util.Inr
                  (uu____6938,x,mltys,uu____6941)) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____7006 =
                         maybe_eta_data_and_project_record g
                           fv.FStar_Syntax_Syntax.fv_qual t1 x
                          in
                       (uu____7006, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____7007 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____7047 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____7047 with
            | (bs1,body1) ->
                let uu____7080 = binders_as_ml_binders g bs1  in
                (match uu____7080 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____7113 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c
                              in
                           if uu____7113
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____7118  ->
                                 let uu____7119 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____7119);
                            body1)
                        in
                     let uu____7120 = term_as_mlexpr env body2  in
                     (match uu____7120 with
                      | (ml_body,f,t1) ->
                          let uu____7136 =
                            FStar_List.fold_right
                              (fun uu____7155  ->
                                 fun uu____7156  ->
                                   match (uu____7155, uu____7156) with
                                   | ((uu____7177,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____7136 with
                           | (f1,tfun) ->
                               let uu____7197 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____7197, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____7204;
              FStar_Syntax_Syntax.vars = uu____7205;_},(a1,uu____7207)::[])
           ->
           let ty =
             let uu____7247 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____7247  in
           let uu____7248 =
             let uu____7249 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____7249
              in
           (uu____7248, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____7250;
              FStar_Syntax_Syntax.vars = uu____7251;_},(t1,uu____7253)::
            (r,uu____7255)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____7310);
              FStar_Syntax_Syntax.pos = uu____7311;
              FStar_Syntax_Syntax.vars = uu____7312;_},uu____7313)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___346_7379  ->
                        match uu___346_7379 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____7380 -> false)))
              in
           let uu____7381 =
             let uu____7386 =
               let uu____7387 = FStar_Syntax_Subst.compress head1  in
               uu____7387.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____7386)  in
           (match uu____7381 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____7396,uu____7397) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Iota;
                    FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                term_as_mlexpr g t1
            | (uu____7411,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____7413,FStar_Pervasives_Native.Some rc)) when
                is_total rc ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.Iota;
                    FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                term_as_mlexpr g t1
            | (uu____7438,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____7440 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____7440
                   in
                let tm =
                  let uu____7452 =
                    let uu____7457 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____7458 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____7457 uu____7458  in
                  uu____7452 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____7469 ->
                let rec extract_app is_data uu____7522 uu____7523 restArgs =
                  match (uu____7522, uu____7523) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____7613) ->
                           let mlargs =
                             FStar_All.pipe_right (FStar_List.rev mlargs_f)
                               (FStar_List.map FStar_Pervasives_Native.fst)
                              in
                           let app =
                             let uu____7648 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t1)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (mlhead, mlargs))
                                in
                             FStar_All.pipe_left
                               (maybe_eta_data_and_project_record g is_data
                                  t1) uu____7648
                              in
                           (app, f, t1)
                       | ((arg,uu____7652)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____7683 =
                             let uu____7688 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f'
                                in
                             (uu____7688, t2)  in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____7683 rest
                       | ((e0,uu____7700)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let expected_effect =
                             let uu____7733 =
                               (FStar_Options.lax ()) &&
                                 (FStar_TypeChecker_Util.short_circuit_head
                                    head1)
                                in
                             if uu____7733
                             then FStar_Extraction_ML_Syntax.E_IMPURE
                             else FStar_Extraction_ML_Syntax.E_PURE  in
                           let uu____7735 =
                             check_term_as_mlexpr g e0 expected_effect
                               tExpected
                              in
                           (match uu____7735 with
                            | (e01,tInferred) ->
                                let uu____7748 =
                                  let uu____7753 =
                                    FStar_Extraction_ML_Util.join_l r [f; f']
                                     in
                                  (uu____7753, t2)  in
                                extract_app is_data
                                  (mlhead, ((e01, expected_effect) ::
                                    mlargs_f)) uu____7748 rest)
                       | uu____7764 ->
                           let uu____7777 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1  in
                           (match uu____7777 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                (match t1 with
                                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                                     (FStar_Extraction_ML_Syntax.ml_unit,
                                       FStar_Extraction_ML_Syntax.E_PURE, t1)
                                 | uu____7799 ->
                                     err_ill_typed_application g top restArgs
                                       t1)))
                   in
                let extract_app_maybe_projector is_data mlhead uu____7847
                  args1 =
                  match uu____7847 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____7877)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____7961))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____7963,f',t3)) ->
                                 let uu____8000 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____8000 t3
                             | uu____8001 -> (args2, f1, t2)  in
                           let uu____8026 = remove_implicits args1 f t1  in
                           (match uu____8026 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____8082 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____8106 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____8114 ->
                      let uu____8115 =
                        let uu____8134 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____8134 with
                        | (FStar_Util.Inr (uu____8159,x1,x2,x3),q) ->
                            ((x1, x2, x3), q)
                        | uu____8240 -> failwith "FIXME Ty"  in
                      (match uu____8115 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____8304)::uu____8305 -> is_type g a
                             | uu____8332 -> false  in
                           let uu____8343 =
                             match vars with
                             | uu____8372::uu____8373 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____8384 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____8416 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____8416 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____8521  ->
                                               match uu____8521 with
                                               | (x,uu____8529) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____8550 ->
                                              let uu___352_8553 = e  in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___352_8553.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___352_8553.FStar_Extraction_ML_Syntax.loc)
                                              }
                                           in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____8557 ->
                                              let uu___353_8558 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___353_8558.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___353_8558.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____8559 ->
                                              let uu___353_8560 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___353_8560.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___353_8560.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____8562;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____8563;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___354_8569 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes
                                                        in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___354_8569.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___354_8569.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____8570 ->
                                              failwith
                                                "Impossible: Unexpected head term"
                                           in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____8343 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____8633 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____8633,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____8634 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____8643 ->
                      let uu____8644 =
                        let uu____8663 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____8663 with
                        | (FStar_Util.Inr (uu____8688,x1,x2,x3),q) ->
                            ((x1, x2, x3), q)
                        | uu____8769 -> failwith "FIXME Ty"  in
                      (match uu____8644 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____8833)::uu____8834 -> is_type g a
                             | uu____8861 -> false  in
                           let uu____8872 =
                             match vars with
                             | uu____8901::uu____8902 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____8913 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____8945 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____8945 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____9050  ->
                                               match uu____9050 with
                                               | (x,uu____9058) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____9079 ->
                                              let uu___352_9082 = e  in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___352_9082.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___352_9082.FStar_Extraction_ML_Syntax.loc)
                                              }
                                           in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____9086 ->
                                              let uu___353_9087 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___353_9087.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___353_9087.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____9088 ->
                                              let uu___353_9089 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___353_9089.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___353_9089.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____9091;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____9092;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___354_9098 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes
                                                        in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___354_9098.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___354_9098.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____9099 ->
                                              failwith
                                                "Impossible: Unexpected head term"
                                           in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____8872 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____9162 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____9162,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____9163 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____9172 ->
                      let uu____9173 = term_as_mlexpr g head2  in
                      (match uu____9173 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____9189 = is_type g t  in
                if uu____9189
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____9197 =
                     let uu____9198 = FStar_Syntax_Util.un_uinst head1  in
                     uu____9198.FStar_Syntax_Syntax.n  in
                   match uu____9197 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____9208 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____9208 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____9239 -> extract_app_with_instantiations ())
                   | uu____9242 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____9245),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 term_as_mlty g (FStar_Syntax_Util.comp_result c)
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____9312 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____9312 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____9343 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____9357 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____9357
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____9369 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____9369  in
                   let lb1 =
                     let uu___355_9371 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___355_9371.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___355_9371.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___355_9371.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___355_9371.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___355_9371.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___355_9371.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____9343 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____9402 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____9402
                               in
                            let lbdef =
                              let uu____9410 = FStar_Options.ml_ish ()  in
                              if uu____9410
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                  FStar_TypeChecker_Env.EraseUniverses;
                                  FStar_TypeChecker_Env.Inlining;
                                  FStar_TypeChecker_Env.Eager_unfolding;
                                  FStar_TypeChecker_Env.Exclude
                                    FStar_TypeChecker_Env.Zeta;
                                  FStar_TypeChecker_Env.PureSubtermsWithinComputations;
                                  FStar_TypeChecker_Env.Primops] tcenv
                                  lb.FStar_Syntax_Syntax.lbdef
                               in
                            let uu___356_9414 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___356_9414.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___356_9414.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___356_9414.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___356_9414.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___356_9414.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___356_9414.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let maybe_generalize uu____9439 =
                  match uu____9439 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____9459;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;
                      FStar_Syntax_Syntax.lbattrs = uu____9463;
                      FStar_Syntax_Syntax.lbpos = uu____9464;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t2 = FStar_Syntax_Subst.compress t1  in
                      let no_gen uu____9542 =
                        let expected_t = term_as_mlty g t2  in
                        (lbname_, f_e, (t2, ([], ([], expected_t))), false,
                          e)
                         in
                      let uu____9612 =
                        FStar_TypeChecker_Util.must_erase_for_extraction
                          g.FStar_Extraction_ML_UEnv.tcenv t2
                         in
                      if uu____9612
                      then
                        (lbname_, f_e,
                          (t2,
                            ([],
                              ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                          false, e)
                      else
                        (match t2.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                             let uu____9690 = FStar_List.hd bs  in
                             FStar_All.pipe_right uu____9690
                               (is_type_binder g)
                             ->
                             let uu____9711 =
                               FStar_Syntax_Subst.open_comp bs c  in
                             (match uu____9711 with
                              | (bs1,c1) ->
                                  let uu____9756 =
                                    let uu____9769 =
                                      FStar_Util.prefix_until
                                        (fun x  ->
                                           let uu____9815 =
                                             is_type_binder g x  in
                                           Prims.op_Negation uu____9815) bs1
                                       in
                                    match uu____9769 with
                                    | FStar_Pervasives_Native.None  ->
                                        (bs1,
                                          (FStar_Syntax_Util.comp_result c1))
                                    | FStar_Pervasives_Native.Some
                                        (bs2,b,rest) ->
                                        let uu____9941 =
                                          FStar_Syntax_Util.arrow (b :: rest)
                                            c1
                                           in
                                        (bs2, uu____9941)
                                     in
                                  (match uu____9756 with
                                   | (tbinders,tbody) ->
                                       let n_tbinders =
                                         FStar_List.length tbinders  in
                                       let e1 =
                                         let uu____10002 = normalize_abs e
                                            in
                                         FStar_All.pipe_right uu____10002
                                           FStar_Syntax_Util.unmeta
                                          in
                                       (match e1.FStar_Syntax_Syntax.n with
                                        | FStar_Syntax_Syntax.Tm_abs
                                            (bs2,body,copt) ->
                                            let uu____10050 =
                                              FStar_Syntax_Subst.open_term
                                                bs2 body
                                               in
                                            (match uu____10050 with
                                             | (bs3,body1) ->
                                                 if
                                                   n_tbinders <=
                                                     (FStar_List.length bs3)
                                                 then
                                                   let uu____10125 =
                                                     FStar_Util.first_N
                                                       n_tbinders bs3
                                                      in
                                                   (match uu____10125 with
                                                    | (targs,rest_args) ->
                                                        let expected_source_ty
                                                          =
                                                          let s =
                                                            FStar_List.map2
                                                              (fun
                                                                 uu____10231 
                                                                 ->
                                                                 fun
                                                                   uu____10232
                                                                    ->
                                                                   match 
                                                                    (uu____10231,
                                                                    uu____10232)
                                                                   with
                                                                   | 
                                                                   ((x,uu____10258),
                                                                    (y,uu____10260))
                                                                    ->
                                                                    let uu____10281
                                                                    =
                                                                    let uu____10288
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____10288)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____10281)
                                                              tbinders targs
                                                             in
                                                          FStar_Syntax_Subst.subst
                                                            s tbody
                                                           in
                                                        let env =
                                                          FStar_List.fold_left
                                                            (fun env  ->
                                                               fun
                                                                 uu____10305 
                                                                 ->
                                                                 match uu____10305
                                                                 with
                                                                 | (a,uu____10313)
                                                                    ->
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
                                                          let uu____10324 =
                                                            FStar_All.pipe_right
                                                              targs
                                                              (FStar_List.map
                                                                 (fun
                                                                    uu____10342
                                                                     ->
                                                                    match uu____10342
                                                                    with
                                                                    | 
                                                                    (x,uu____10350)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                             in
                                                          (uu____10324,
                                                            expected_t)
                                                           in
                                                        let add_unit =
                                                          match rest_args
                                                          with
                                                          | [] ->
                                                              (let uu____10364
                                                                 =
                                                                 is_fstar_value
                                                                   body1
                                                                  in
                                                               Prims.op_Negation
                                                                 uu____10364)
                                                                ||
                                                                (let uu____10366
                                                                   =
                                                                   FStar_Syntax_Util.is_pure_comp
                                                                    c1
                                                                    in
                                                                 Prims.op_Negation
                                                                   uu____10366)
                                                          | uu____10367 ->
                                                              false
                                                           in
                                                        let rest_args1 =
                                                          if add_unit
                                                          then unit_binder ::
                                                            rest_args
                                                          else rest_args  in
                                                        let polytype1 =
                                                          if add_unit
                                                          then
                                                            FStar_Extraction_ML_Syntax.push_unit
                                                              polytype
                                                          else polytype  in
                                                        let body2 =
                                                          FStar_Syntax_Util.abs
                                                            rest_args1 body1
                                                            copt
                                                           in
                                                        (lbname_, f_e,
                                                          (t2,
                                                            (targs,
                                                              polytype1)),
                                                          add_unit, body2))
                                                 else
                                                   failwith
                                                     "Not enough type binders")
                                        | FStar_Syntax_Syntax.Tm_uinst
                                            uu____10420 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____10439  ->
                                                     match uu____10439 with
                                                     | (a,uu____10447) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____10458 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____10476  ->
                                                        match uu____10476
                                                        with
                                                        | (x,uu____10484) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____10458, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____10528  ->
                                                      match uu____10528 with
                                                      | (bv,uu____10536) ->
                                                          let uu____10541 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____10541
                                                            FStar_Syntax_Syntax.as_arg))
                                               in
                                            let e2 =
                                              FStar_Syntax_Syntax.mk
                                                (FStar_Syntax_Syntax.Tm_app
                                                   (e1, args))
                                                FStar_Pervasives_Native.None
                                                e1.FStar_Syntax_Syntax.pos
                                               in
                                            (lbname_, f_e,
                                              (t2, (tbinders, polytype)),
                                              false, e2)
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            uu____10569 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____10582  ->
                                                     match uu____10582 with
                                                     | (a,uu____10590) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____10601 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____10619  ->
                                                        match uu____10619
                                                        with
                                                        | (x,uu____10627) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____10601, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____10671  ->
                                                      match uu____10671 with
                                                      | (bv,uu____10679) ->
                                                          let uu____10684 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____10684
                                                            FStar_Syntax_Syntax.as_arg))
                                               in
                                            let e2 =
                                              FStar_Syntax_Syntax.mk
                                                (FStar_Syntax_Syntax.Tm_app
                                                   (e1, args))
                                                FStar_Pervasives_Native.None
                                                e1.FStar_Syntax_Syntax.pos
                                               in
                                            (lbname_, f_e,
                                              (t2, (tbinders, polytype)),
                                              false, e2)
                                        | FStar_Syntax_Syntax.Tm_name
                                            uu____10712 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____10725  ->
                                                     match uu____10725 with
                                                     | (a,uu____10733) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____10744 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____10762  ->
                                                        match uu____10762
                                                        with
                                                        | (x,uu____10770) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____10744, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____10814  ->
                                                      match uu____10814 with
                                                      | (bv,uu____10822) ->
                                                          let uu____10827 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____10827
                                                            FStar_Syntax_Syntax.as_arg))
                                               in
                                            let e2 =
                                              FStar_Syntax_Syntax.mk
                                                (FStar_Syntax_Syntax.Tm_app
                                                   (e1, args))
                                                FStar_Pervasives_Native.None
                                                e1.FStar_Syntax_Syntax.pos
                                               in
                                            (lbname_, f_e,
                                              (t2, (tbinders, polytype)),
                                              false, e2)
                                        | uu____10855 ->
                                            err_value_restriction e1)))
                         | uu____10874 -> no_gen ())
                   in
                let check_lb env uu____10929 =
                  match uu____10929 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____11104  ->
                               match uu____11104 with
                               | (a,uu____11112) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____11118 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____11118 with
                       | (e1,ty) ->
                           let uu____11129 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____11129 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____11141 -> []  in
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
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize)
                   in
                let uu____11223 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____11338  ->
                         match uu____11338 with
                         | (env,lbs4) ->
                             let uu____11503 = lb  in
                             (match uu____11503 with
                              | (lbname,uu____11567,(t1,(uu____11569,polytype)),add_unit,uu____11572)
                                  ->
                                  let uu____11617 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____11617 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, [])
                   in
                (match uu____11223 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____12008 = term_as_mlexpr env_body e'1  in
                     (match uu____12008 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____12025 =
                              let uu____12028 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____12028  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____12025
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____12037 =
                            let uu____12038 =
                              let uu____12039 =
                                let uu____12040 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____12040)  in
                              mk_MLE_Let top_level uu____12039 e'2  in
                            let uu____12049 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____12038 uu____12049
                             in
                          (uu____12037, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____12088 = term_as_mlexpr g scrutinee  in
           (match uu____12088 with
            | (e,f_e,t_e) ->
                let uu____12104 = check_pats_for_ite pats  in
                (match uu____12104 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____12189 = term_as_mlexpr g then_e1  in
                            (match uu____12189 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____12205 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____12205 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____12221 =
                                        let uu____12232 =
                                          type_leq g t_then t_else  in
                                        if uu____12232
                                        then (t_else, no_lift)
                                        else
                                          (let uu____12250 =
                                             type_leq g t_else t_then  in
                                           if uu____12250
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____12221 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____12294 =
                                             let uu____12295 =
                                               let uu____12296 =
                                                 let uu____12305 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____12306 =
                                                   let uu____12309 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____12309
                                                    in
                                                 (e, uu____12305,
                                                   uu____12306)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____12296
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____12295
                                              in
                                           let uu____12312 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____12294, uu____12312,
                                             t_branch))))
                        | uu____12313 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____12333 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____12428 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____12428 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____12472 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____12472 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____12530 =
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
                                                   let uu____12553 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____12553 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____12530 with
                                              | (when_opt1,f_when) ->
                                                  let uu____12602 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____12602 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____12636 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____12713 
                                                                 ->
                                                                 match uu____12713
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
                                                         uu____12636)))))
                               true)
                           in
                        match uu____12333 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____12878  ->
                                      let uu____12879 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____12880 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____12879 uu____12880);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____12905 =
                                   let uu____12914 =
                                     let uu____12931 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.delta_constant
                                         FStar_Pervasives_Native.None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____12931
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____12914
                                    in
                                 (match uu____12905 with
                                  | (uu____12974,fw,uu____12976,uu____12977)
                                      ->
                                      let uu____12978 =
                                        let uu____12979 =
                                          let uu____12980 =
                                            let uu____12987 =
                                              let uu____12990 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____12990]  in
                                            (fw, uu____12987)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____12980
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____12979
                                         in
                                      (uu____12978,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____12993,uu____12994,(uu____12995,f_first,t_first))::rest
                                 ->
                                 let uu____13055 =
                                   FStar_List.fold_left
                                     (fun uu____13097  ->
                                        fun uu____13098  ->
                                          match (uu____13097, uu____13098)
                                          with
                                          | ((topt,f),(uu____13155,uu____13156,
                                                       (uu____13157,f_branch,t_branch)))
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
                                                    let uu____13213 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____13213
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____13217 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____13217
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
                                 (match uu____13055 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____13312  ->
                                                match uu____13312 with
                                                | (p,(wopt,uu____13341),
                                                   (b1,uu____13343,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____13362 -> b1
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
                                      let uu____13367 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____13367, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____13393 =
          let uu____13398 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____13398  in
        match uu____13393 with
        | (uu____13423,fstar_disc_type) ->
            let wildcards =
              let uu____13432 =
                let uu____13433 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____13433.FStar_Syntax_Syntax.n  in
              match uu____13432 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____13443) ->
                  let uu____13464 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___347_13498  ->
                            match uu___347_13498 with
                            | (uu____13505,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____13506)) ->
                                true
                            | uu____13509 -> false))
                     in
                  FStar_All.pipe_right uu____13464
                    (FStar_List.map
                       (fun uu____13542  ->
                          let uu____13549 = fresh "_"  in
                          (uu____13549, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____13550 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____13561 =
                let uu____13562 =
                  let uu____13573 =
                    let uu____13574 =
                      let uu____13575 =
                        let uu____13590 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____13593 =
                          let uu____13604 =
                            let uu____13613 =
                              let uu____13614 =
                                let uu____13621 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____13621,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____13614
                               in
                            let uu____13624 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____13613, FStar_Pervasives_Native.None,
                              uu____13624)
                             in
                          let uu____13627 =
                            let uu____13638 =
                              let uu____13647 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____13647)
                               in
                            [uu____13638]  in
                          uu____13604 :: uu____13627  in
                        (uu____13590, uu____13593)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____13575  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____13574
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____13573)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____13562  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____13561
               in
            let uu____13702 =
              let uu____13703 =
                let uu____13706 =
                  let uu____13707 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____13707;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____13706]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____13703)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____13702
  