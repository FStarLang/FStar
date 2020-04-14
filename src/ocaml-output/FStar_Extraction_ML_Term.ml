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
          let uu____928 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____928
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____929;
            FStar_Syntax_Syntax.index = uu____930;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____935;
            FStar_Syntax_Syntax.index = uu____936;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____942,uu____943) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____985) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____992) ->
          let uu____1017 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____1017 with
           | (uu____1023,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____1043 =
            let uu____1048 =
              let uu____1049 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1049]  in
            FStar_Syntax_Subst.open_term uu____1048 body  in
          (match uu____1043 with
           | (uu____1069,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1071,lbs),body) ->
          let uu____1091 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____1091 with
           | (uu____1099,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1105,branches) ->
          (match branches with
           | b::uu____1145 ->
               let uu____1190 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1190 with
                | (uu____1192,uu____1193,e) -> is_type_aux env e)
           | uu____1211 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1229 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1238) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head,uu____1244) -> is_type_aux env head
  
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1285  ->
           let uu____1286 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1288 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1286
             uu____1288);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1297  ->
            if b
            then
              let uu____1299 = FStar_Syntax_Print.term_to_string t  in
              let uu____1301 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "yes, is_type %s (%s)\n" uu____1299
                uu____1301
            else
              (let uu____1306 = FStar_Syntax_Print.term_to_string t  in
               let uu____1308 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1306 uu____1308));
       b)
  
let is_type_binder :
  'uuuuuu1318 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu1318) -> Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1345 =
      let uu____1346 = FStar_Syntax_Subst.compress t  in
      uu____1346.FStar_Syntax_Syntax.n  in
    match uu____1345 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1350;
          FStar_Syntax_Syntax.fv_delta = uu____1351;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1353;
          FStar_Syntax_Syntax.fv_delta = uu____1354;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1355);_}
        -> true
    | uu____1363 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1372 =
      let uu____1373 = FStar_Syntax_Subst.compress t  in
      uu____1373.FStar_Syntax_Syntax.n  in
    match uu____1372 with
    | FStar_Syntax_Syntax.Tm_constant uu____1377 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1379 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1381 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1383 -> true
    | FStar_Syntax_Syntax.Tm_app (head,args) ->
        let uu____1429 = is_constructor head  in
        if uu____1429
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1451  ->
                  match uu____1451 with
                  | (te,uu____1460) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1469) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1475,uu____1476) ->
        is_fstar_value t1
    | uu____1517 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1527 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1529 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1532 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1534 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1547,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1556,fields) ->
        FStar_Util.for_all
          (fun uu____1586  ->
             match uu____1586 with | (uu____1593,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1598) -> is_ml_value h
    | uu____1603 -> false
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1685 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1687 = FStar_Syntax_Util.is_fun e'  in
          if uu____1687
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : unit -> FStar_Syntax_Syntax.binder) =
  fun uu____1705  ->
    let uu____1706 =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.t_unit
       in
    FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1706
  
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
      (let uu____1797 = FStar_List.hd l  in
       match uu____1797 with
       | (p1,w1,e1) ->
           let uu____1832 =
             let uu____1841 = FStar_List.tl l  in FStar_List.hd uu____1841
              in
           (match uu____1832 with
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
                 | uu____1925 -> def)))
  
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
      let uu____1990 =
        FStar_List.fold_right
          (fun t  ->
             fun uu____2021  ->
               match uu____2021 with
               | (uenv,vs) ->
                   let uu____2060 = FStar_Extraction_ML_UEnv.new_mlident uenv
                      in
                   (match uu____2060 with
                    | (uenv1,v) -> (uenv1, ((v, t) :: vs)))) ts (g, [])
         in
      match uu____1990 with | (g1,vs_ts) -> (vs_ts, g1)
  
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
          let uu____2177 = s  in
          match uu____2177 with
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
                      let uu___372_2209 = e  in
                      {
                        FStar_Extraction_ML_Syntax.expr =
                          (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                        FStar_Extraction_ML_Syntax.mlty = ts;
                        FStar_Extraction_ML_Syntax.loc =
                          (uu___372_2209.FStar_Extraction_ML_Syntax.loc)
                      }  in
                    (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
              else
                if n_args < n_vars
                then
                  (let extra_tyargs =
                     let uu____2224 = FStar_Util.first_N n_args vars  in
                     match uu____2224 with
                     | (uu____2238,rest_vars) ->
                         FStar_All.pipe_right rest_vars
                           (FStar_List.map
                              (fun uu____2259  ->
                                 FStar_Extraction_ML_Syntax.MLTY_Erased))
                      in
                   let tyargs1 = FStar_List.append tyargs extra_tyargs  in
                   let ts = instantiate_tyscheme (vars, t) tyargs1  in
                   let tapp =
                     let uu___383_2266 = e  in
                     {
                       FStar_Extraction_ML_Syntax.expr =
                         (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                       FStar_Extraction_ML_Syntax.mlty = ts;
                       FStar_Extraction_ML_Syntax.loc =
                         (uu___383_2266.FStar_Extraction_ML_Syntax.loc)
                     }  in
                   let t1 =
                     FStar_List.fold_left
                       (fun out  ->
                          fun t1  ->
                            FStar_Extraction_ML_Syntax.MLTY_Fun
                              (t1, FStar_Extraction_ML_Syntax.E_PURE, out))
                       ts extra_tyargs
                      in
                   let uu____2274 = fresh_mlidents extra_tyargs g  in
                   match uu____2274 with
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
        let uu____2341 = FStar_Extraction_ML_Util.doms_and_cod t  in
        match uu____2341 with
        | (ts,r) ->
            if ts = []
            then e
            else
              (let uu____2359 = fresh_mlidents ts g  in
               match uu____2359 with
               | (vs_ts,g1) ->
                   let vs_es =
                     FStar_List.map
                       (fun uu____2398  ->
                          match uu____2398 with
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
      let uu____2429 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____2429 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____2449 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____2449 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____2453 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let uu____2459 = fresh_mlidents ts g  in
             match uu____2459 with
             | (vs_ts,g1) ->
                 let uu____2487 =
                   let uu____2488 =
                     let uu____2500 = body r  in (vs_ts, uu____2500)  in
                   FStar_Extraction_ML_Syntax.MLE_Fun uu____2488  in
                 FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
                   uu____2487)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g  ->
    fun expect  ->
      fun e  ->
        let uu____2524 =
          (FStar_Options.ml_no_eta_expand_coertions ()) ||
            (let uu____2527 = FStar_Options.codegen ()  in
             uu____2527 =
               (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
           in
        if uu____2524 then e else eta_expand g expect e
  
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
            | uu____2605 ->
                FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body)
             in
          let rec aux e1 ty1 expect1 =
            let coerce_branch uu____2660 =
              match uu____2660 with
              | (pat,w,b) ->
                  let uu____2684 = aux b ty1 expect1  in (pat, w, uu____2684)
               in
            match ((e1.FStar_Extraction_ML_Syntax.expr), ty1, expect1) with
            | (FStar_Extraction_ML_Syntax.MLE_Fun
               (arg::rest,body),FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0,uu____2691,t1),FStar_Extraction_ML_Syntax.MLTY_Fun
               (s0,uu____2694,s1)) ->
                let body1 =
                  match rest with
                  | [] -> body
                  | uu____2726 ->
                      FStar_Extraction_ML_Syntax.with_ty t1
                        (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body))
                   in
                let body2 = aux body1 t1 s1  in
                let uu____2742 = type_leq g s0 t0  in
                if uu____2742
                then
                  FStar_Extraction_ML_Syntax.with_ty expect1
                    (mk_fun arg body2)
                else
                  (let lb =
                     let uu____2748 =
                       let uu____2749 =
                         let uu____2750 =
                           let uu____2757 =
                             FStar_All.pipe_left
                               (FStar_Extraction_ML_Syntax.with_ty s0)
                               (FStar_Extraction_ML_Syntax.MLE_Var
                                  (FStar_Pervasives_Native.fst arg))
                              in
                           (uu____2757, s0, t0)  in
                         FStar_Extraction_ML_Syntax.MLE_Coerce uu____2750  in
                       FStar_Extraction_ML_Syntax.with_ty t0 uu____2749  in
                     {
                       FStar_Extraction_ML_Syntax.mllb_name =
                         (FStar_Pervasives_Native.fst arg);
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         (FStar_Pervasives_Native.Some ([], t0));
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = uu____2748;
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
               (lbs,body),uu____2776,uu____2777) ->
                let uu____2790 =
                  let uu____2791 =
                    let uu____2802 = aux body ty1 expect1  in
                    (lbs, uu____2802)  in
                  FStar_Extraction_ML_Syntax.MLE_Let uu____2791  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2790
            | (FStar_Extraction_ML_Syntax.MLE_Match
               (s,branches),uu____2811,uu____2812) ->
                let uu____2833 =
                  let uu____2834 =
                    let uu____2849 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2849)  in
                  FStar_Extraction_ML_Syntax.MLE_Match uu____2834  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2833
            | (FStar_Extraction_ML_Syntax.MLE_If
               (s,b1,b2_opt),uu____2889,uu____2890) ->
                let uu____2895 =
                  let uu____2896 =
                    let uu____2905 = aux b1 ty1 expect1  in
                    let uu____2906 =
                      FStar_Util.map_opt b2_opt
                        (fun b2  -> aux b2 ty1 expect1)
                       in
                    (s, uu____2905, uu____2906)  in
                  FStar_Extraction_ML_Syntax.MLE_If uu____2896  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2895
            | (FStar_Extraction_ML_Syntax.MLE_Seq es,uu____2914,uu____2915)
                ->
                let uu____2918 = FStar_Util.prefix es  in
                (match uu____2918 with
                 | (prefix,last) ->
                     let uu____2931 =
                       let uu____2932 =
                         let uu____2935 =
                           let uu____2938 = aux last ty1 expect1  in
                           [uu____2938]  in
                         FStar_List.append prefix uu____2935  in
                       FStar_Extraction_ML_Syntax.MLE_Seq uu____2932  in
                     FStar_All.pipe_left
                       (FStar_Extraction_ML_Syntax.with_ty expect1)
                       uu____2931)
            | (FStar_Extraction_ML_Syntax.MLE_Try
               (s,branches),uu____2941,uu____2942) ->
                let uu____2963 =
                  let uu____2964 =
                    let uu____2979 = FStar_List.map coerce_branch branches
                       in
                    (s, uu____2979)  in
                  FStar_Extraction_ML_Syntax.MLE_Try uu____2964  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty expect1) uu____2963
            | uu____3016 ->
                FStar_Extraction_ML_Syntax.with_ty expect1
                  (FStar_Extraction_ML_Syntax.MLE_Coerce (e1, ty1, expect1))
             in
          aux e ty expect
  
let maybe_coerce :
  'uuuuuu3036 .
    'uuuuuu3036 ->
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
            let uu____3063 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____3063 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____3076 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                     default_value_for_ty g expect
                 | uu____3084 ->
                     let uu____3085 =
                       let uu____3087 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1
                          in
                       let uu____3088 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect
                          in
                       type_leq g uu____3087 uu____3088  in
                     if uu____3085
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3094  ->
                             let uu____3095 =
                               let uu____3097 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3097 e
                                in
                             let uu____3098 =
                               let uu____3100 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3100 ty1
                                in
                             FStar_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu____3095 uu____3098);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu____3109  ->
                             let uu____3110 =
                               let uu____3112 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu____3112 e
                                in
                             let uu____3113 =
                               let uu____3115 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3115 ty1
                                in
                             let uu____3116 =
                               let uu____3118 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g
                                  in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu____3118 expect
                                in
                             FStar_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu____3110 uu____3113 uu____3116);
                        (let uu____3120 = apply_coercion g e ty1 expect  in
                         maybe_eta_expand g expect uu____3120)))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____3132 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____3132 with
      | FStar_Util.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu____3134 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
  fun uu____3148  ->
    let uu____3149 = FStar_Options.use_nbe_for_extraction ()  in
    if uu____3149
    then extraction_norm_steps_nbe
    else extraction_norm_steps_core
  
let (comp_no_args :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____3170 -> c
    | FStar_Syntax_Syntax.GTotal uu____3179 -> c
    | FStar_Syntax_Syntax.Comp ct ->
        let effect_args =
          FStar_List.map
            (fun uu____3215  ->
               match uu____3215 with
               | (uu____3230,aq) -> (FStar_Syntax_Syntax.t_unit, aq))
            ct.FStar_Syntax_Syntax.effect_args
           in
        let ct1 =
          let uu___550_3243 = ct  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___550_3243.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___550_3243.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___550_3243.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args = effect_args;
            FStar_Syntax_Syntax.flags =
              (uu___550_3243.FStar_Syntax_Syntax.flags)
          }  in
        let c1 =
          let uu___553_3247 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
            FStar_Syntax_Syntax.pos = (uu___553_3247.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___553_3247.FStar_Syntax_Syntax.vars)
          }  in
        c1
  
let maybe_reify_comp :
  'uuuuuu3259 .
    'uuuuuu3259 ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun g  ->
    fun env  ->
      fun c  ->
        let c1 = comp_no_args c  in
        let uu____3278 =
          let uu____3280 =
            let uu____3281 =
              FStar_All.pipe_right c1 FStar_Syntax_Util.comp_effect_name  in
            FStar_All.pipe_right uu____3281
              (FStar_TypeChecker_Env.norm_eff_name env)
             in
          FStar_All.pipe_right uu____3280
            (FStar_TypeChecker_Env.is_reifiable_effect env)
           in
        if uu____3278
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
      let arg_as_mlty g1 uu____3334 =
        match uu____3334 with
        | (a,uu____3342) ->
            let uu____3347 = is_type g1 a  in
            if uu____3347
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_Syntax.MLTY_Erased
         in
      let fv_app_as_mlty g1 fv args =
        let uu____3368 =
          let uu____3370 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____3370  in
        if uu____3368
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____3375 =
             let uu____3382 =
               let uu____3391 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1  in
               FStar_TypeChecker_Env.lookup_lid uu____3391
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____3382 with
             | ((uu____3398,fvty),uu____3400) ->
                 let fvty1 =
                   let uu____3406 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1
                      in
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Env.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant] uu____3406 fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____3375 with
           | (formals,uu____3408) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____3445 = FStar_Util.first_N n_args formals  in
                   match uu____3445 with
                   | (uu____3474,rest) ->
                       let uu____3508 =
                         FStar_List.map
                           (fun uu____3518  ->
                              FStar_Extraction_ML_Syntax.MLTY_Erased) rest
                          in
                       FStar_List.append mlargs uu____3508
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
        | FStar_Syntax_Syntax.Tm_type uu____3542 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____3543 ->
            let uu____3544 =
              let uu____3546 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3546
               in
            failwith uu____3544
        | FStar_Syntax_Syntax.Tm_delayed uu____3549 ->
            let uu____3564 =
              let uu____3566 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3566
               in
            failwith uu____3564
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3569 =
              let uu____3571 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____3571
               in
            failwith uu____3569
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____3575 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____3575
        | FStar_Syntax_Syntax.Tm_constant uu____3576 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_quoted uu____3577 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_uvar uu____3584 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____3598) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____3603;
               FStar_Syntax_Syntax.index = uu____3604;
               FStar_Syntax_Syntax.sort = t2;_},uu____3606)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3615) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3621,uu____3622) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____3695 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____3695 with
             | (bs1,c1) ->
                 let uu____3702 = binders_as_ml_binders env bs1  in
                 (match uu____3702 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let uu____3731 =
                          let uu____3732 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv env1  in
                          maybe_reify_comp env1 uu____3732 c1  in
                        translate_term_to_mlty env1 uu____3731  in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____3734 =
                        FStar_List.fold_right
                          (fun uu____3754  ->
                             fun uu____3755  ->
                               match (uu____3754, uu____3755) with
                               | ((uu____3778,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____3734 with | (uu____3793,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let res =
              let uu____3822 =
                let uu____3823 = FStar_Syntax_Util.un_uinst head  in
                uu____3823.FStar_Syntax_Syntax.n  in
              match uu____3822 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head1,args') ->
                  let uu____3854 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head1, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____3854
              | uu____3875 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____3878) ->
            let uu____3903 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____3903 with
             | (bs1,ty1) ->
                 let uu____3910 = binders_as_ml_binders env bs1  in
                 (match uu____3910 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____3938 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_match uu____3952 ->
            FStar_Extraction_ML_Syntax.MLTY_Top
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____3984 ->
            let uu____3991 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____3991 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____3997 -> false  in
      let uu____3999 =
        let uu____4001 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Util.must_erase_for_extraction uu____4001 t0  in
      if uu____3999
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____4006 = is_top_ty mlt  in
         if uu____4006 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)

and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g  ->
    fun bs  ->
      let uu____4024 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____4081  ->
                fun b  ->
                  match uu____4081 with
                  | (ml_bs,env) ->
                      let uu____4127 = is_type_binder g b  in
                      if uu____4127
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1 true  in
                        let ml_b =
                          let uu____4150 =
                            FStar_Extraction_ML_UEnv.lookup_ty env1 b1  in
                          uu____4150.FStar_Extraction_ML_UEnv.ty_b_name  in
                        let ml_b1 =
                          (ml_b, FStar_Extraction_ML_Syntax.ml_unit_ty)  in
                        ((ml_b1 :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____4176 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false
                            in
                         match uu____4176 with
                         | (env1,b2,uu____4200) ->
                             let ml_b = (b2, t)  in ((ml_b :: ml_bs), env1)))
             ([], g))
         in
      match uu____4024 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let t =
        let uu____4285 = extraction_norm_steps ()  in
        let uu____4286 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
        FStar_TypeChecker_Normalize.normalize uu____4285 uu____4286 t0  in
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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____4305) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____4308,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____4312 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____4346 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____4347 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____4348 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____4357 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
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
            (fun uu____4433  ->
               fun x  -> match uu____4433 with | (p,s) -> (s, x)) fns1 xs
  
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
            let uu____4485 = FStar_Extraction_ML_Util.is_xtuple d  in
            (match uu____4485 with
             | FStar_Pervasives_Native.Some n ->
                 FStar_Extraction_ML_Syntax.MLP_Tuple pats
             | uu____4492 ->
                 (match q with
                  | FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                      let path =
                        let uu____4506 = FStar_Ident.ns_of_lid ty  in
                        FStar_List.map FStar_Ident.text_of_id uu____4506  in
                      let fs = record_fields g ty fns pats  in
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
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false imp
                   in
                (match uu____4851 with
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
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false imp
                   in
                (match uu____4919 with
                 | (g1,x1,uu____4946) ->
                     let uu____4949 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____4949))
            | FStar_Syntax_Syntax.Pat_dot_term uu____4985 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____5028 =
                  let uu____5037 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____5037 with
                  | { FStar_Extraction_ML_UEnv.exp_b_name = uu____5046;
                      FStar_Extraction_ML_UEnv.exp_b_expr =
                        {
                          FStar_Extraction_ML_Syntax.expr =
                            FStar_Extraction_ML_Syntax.MLE_Name n;
                          FStar_Extraction_ML_Syntax.mlty = uu____5048;
                          FStar_Extraction_ML_Syntax.loc = uu____5049;_};
                      FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;_} ->
                      (n, ttys)
                  | uu____5056 -> failwith "Expected a constructor"  in
                (match uu____5028 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____5093 = FStar_Util.first_N nTyVars pats  in
                     (match uu____5093 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              (fun uu___852_5197  ->
                                 match () with
                                 | () ->
                                     let mlty_args =
                                       FStar_All.pipe_right tysVarPats
                                         (FStar_List.map
                                            (fun uu____5228  ->
                                               match uu____5228 with
                                               | (p1,uu____5235) ->
                                                   (match p1.FStar_Syntax_Syntax.v
                                                    with
                                                    | FStar_Syntax_Syntax.Pat_dot_term
                                                        (uu____5238,t) ->
                                                        term_as_mlty g t
                                                    | uu____5244 ->
                                                        (FStar_Extraction_ML_UEnv.debug
                                                           g
                                                           (fun uu____5248 
                                                              ->
                                                              let uu____5249
                                                                =
                                                                FStar_Syntax_Print.pat_to_string
                                                                  p1
                                                                 in
                                                              FStar_Util.print1
                                                                "Pattern %s is not extractable"
                                                                uu____5249);
                                                         FStar_Exn.raise
                                                           Un_extractable))))
                                        in
                                     let f_ty =
                                       FStar_Extraction_ML_Util.subst tys
                                         mlty_args
                                        in
                                     let uu____5253 =
                                       FStar_Extraction_ML_Util.uncurry_mlty_fun
                                         f_ty
                                        in
                                     FStar_Pervasives_Native.Some uu____5253)
                                ()
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____5282 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____5319  ->
                                   match uu____5319 with
                                   | (p1,imp1) ->
                                       let uu____5341 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____5341 with
                                        | (g2,p2,uu____5372) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____5282 with
                           | (g1,tyMLPats) ->
                               let uu____5436 =
                                 FStar_Util.fold_map
                                   (fun uu____5501  ->
                                      fun uu____5502  ->
                                        match (uu____5501, uu____5502) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____5600 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd))
                                              | uu____5660 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____5600 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____5731 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____5731 with
                                                  | (g3,p2,uu____5774) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____5436 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____5895 =
                                      let uu____5906 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___0_5957  ->
                                                match uu___0_5957 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____5999 -> []))
                                         in
                                      FStar_All.pipe_right uu____5906
                                        FStar_List.split
                                       in
                                    (match uu____5895 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____6075 -> false  in
                                         let uu____6085 =
                                           let uu____6094 =
                                             let uu____6101 =
                                               resugar_pat g2
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____6104 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____6101, uu____6104)  in
                                           FStar_Pervasives_Native.Some
                                             uu____6094
                                            in
                                         (g2, uu____6085, pat_ty_compat))))))
  
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
            let uu____6236 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____6236 with
            | (g2,FStar_Pervasives_Native.Some (x,v),b) -> (g2, (x, v), b)
            | uu____6299 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd::tl ->
                let uu____6347 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl
                   in
                FStar_Pervasives_Native.Some uu____6347
             in
          let uu____6348 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____6348 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____6513,t1) ->
                let uu____6515 = FStar_Extraction_ML_UEnv.new_mlident g1  in
                (match uu____6515 with
                 | (g2,x) ->
                     let uu____6540 =
                       let uu____6552 =
                         let uu____6562 =
                           FStar_All.pipe_left
                             (FStar_Extraction_ML_Syntax.with_ty t0)
                             (FStar_Extraction_ML_Syntax.MLE_Var x)
                            in
                         ((x, t0), uu____6562)  in
                       uu____6552 :: more_args  in
                     eta_args g2 uu____6540 t1)
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____6578,uu____6579)
                -> ((FStar_List.rev more_args), t)
            | uu____6604 ->
                let uu____6605 =
                  let uu____6607 =
                    let uu____6609 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu____6609
                      mlAppExpr
                     in
                  let uu____6610 =
                    let uu____6612 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1  in
                    FStar_Extraction_ML_Code.string_of_mlty uu____6612 t  in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____6607 uu____6610
                   in
                failwith uu____6605
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____6646,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  let uu____6664 = FStar_Ident.ns_of_lid tyname  in
                  FStar_List.map FStar_Ident.text_of_id uu____6664  in
                let fields1 = record_fields g tyname fields args  in
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
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head,args)
                               ->
                               let body =
                                 let uu____6825 =
                                   let uu____6826 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
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
              let fn =
                let uu____6857 =
                  let uu____6862 =
                    let uu____6863 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6863
                      constrname
                     in
                  (uu____6862, f)  in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6857
                 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____6866 ->
                    let uu____6869 =
                      let uu____6876 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6876, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6869
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
                     FStar_Extraction_ML_Syntax.mlty = uu____6880;
                     FStar_Extraction_ML_Syntax.loc = uu____6881;_},uu____6882);
                FStar_Extraction_ML_Syntax.mlty = uu____6883;
                FStar_Extraction_ML_Syntax.loc = uu____6884;_},mle::args),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname,f))) ->
              let fn =
                let uu____6900 =
                  let uu____6905 =
                    let uu____6906 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.typ_of_datacon uu____6906
                      constrname
                     in
                  (uu____6905, f)  in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g
                  uu____6900
                 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn)  in
              let e =
                match args with
                | [] -> proj
                | uu____6909 ->
                    let uu____6912 =
                      let uu____6919 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____6919, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____6912
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6923;
                FStar_Extraction_ML_Syntax.loc = uu____6924;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6932 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6932
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____6936;
                FStar_Extraction_ML_Syntax.loc = uu____6937;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6939)) ->
              let uu____6952 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6952
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6956;
                     FStar_Extraction_ML_Syntax.loc = uu____6957;_},uu____6958);
                FStar_Extraction_ML_Syntax.mlty = uu____6959;
                FStar_Extraction_ML_Syntax.loc = uu____6960;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____6972 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6972
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____6976;
                     FStar_Extraction_ML_Syntax.loc = uu____6977;_},uu____6978);
                FStar_Extraction_ML_Syntax.mlty = uu____6979;
                FStar_Extraction_ML_Syntax.loc = uu____6980;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____6982)) ->
              let uu____6999 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____6999
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____7005 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7005
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7009)) ->
              let uu____7018 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7018
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7022;
                FStar_Extraction_ML_Syntax.loc = uu____7023;_},uu____7024),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____7031 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7031
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____7035;
                FStar_Extraction_ML_Syntax.loc = uu____7036;_},uu____7037),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____7038)) ->
              let uu____7051 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____7051
          | uu____7054 -> mlAppExpr
  
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
        | uu____7085 -> (ml_e, tag)
  
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
      let maybe_generalize uu____7146 =
        match uu____7146 with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu____7167;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu____7172;_} ->
            let f_e = effect_as_etag g lbeff  in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp  in
            let no_gen uu____7253 =
              let expected_t = term_as_mlty g lbtyp1  in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef)
               in
            let uu____7330 =
              let uu____7332 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
              FStar_TypeChecker_Util.must_erase_for_extraction uu____7332
                lbtyp1
               in
            if uu____7330
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                   let uu____7417 = FStar_List.hd bs  in
                   FStar_All.pipe_right uu____7417 (is_type_binder g) ->
                   let uu____7439 = FStar_Syntax_Subst.open_comp bs c  in
                   (match uu____7439 with
                    | (bs1,c1) ->
                        let uu____7465 =
                          let uu____7478 =
                            FStar_Util.prefix_until
                              (fun x  ->
                                 let uu____7524 = is_type_binder g x  in
                                 Prims.op_Negation uu____7524) bs1
                             in
                          match uu____7478 with
                          | FStar_Pervasives_Native.None  ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2,b,rest) ->
                              let uu____7651 =
                                FStar_Syntax_Util.arrow (b :: rest) c1  in
                              (bs2, uu____7651)
                           in
                        (match uu____7465 with
                         | (tbinders,tbody) ->
                             let n_tbinders = FStar_List.length tbinders  in
                             let lbdef1 =
                               let uu____7713 = normalize_abs lbdef  in
                               FStar_All.pipe_right uu____7713
                                 FStar_Syntax_Util.unmeta
                                in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs (bs2,body,copt) ->
                                  let uu____7762 =
                                    FStar_Syntax_Subst.open_term bs2 body  in
                                  (match uu____7762 with
                                   | (bs3,body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_List.length bs3)
                                       then
                                         let uu____7814 =
                                           FStar_Util.first_N n_tbinders bs3
                                            in
                                         (match uu____7814 with
                                          | (targs,rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_List.map2
                                                    (fun uu____7917  ->
                                                       fun uu____7918  ->
                                                         match (uu____7917,
                                                                 uu____7918)
                                                         with
                                                         | ((x,uu____7944),
                                                            (y,uu____7946))
                                                             ->
                                                             let uu____7967 =
                                                               let uu____7974
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y
                                                                  in
                                                               (x,
                                                                 uu____7974)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____7967)
                                                    tbinders targs
                                                   in
                                                FStar_Syntax_Subst.subst s
                                                  tbody
                                                 in
                                              let env =
                                                FStar_List.fold_left
                                                  (fun env  ->
                                                     fun uu____7991  ->
                                                       match uu____7991 with
                                                       | (a,uu____7999) ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env a false) g
                                                  targs
                                                 in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty
                                                 in
                                              let polytype =
                                                let uu____8011 =
                                                  FStar_All.pipe_right targs
                                                    (FStar_List.map
                                                       (fun uu____8031  ->
                                                          match uu____8031
                                                          with
                                                          | (x,uu____8040) ->
                                                              let uu____8045
                                                                =
                                                                FStar_Extraction_ML_UEnv.lookup_ty
                                                                  env x
                                                                 in
                                                              uu____8045.FStar_Extraction_ML_UEnv.ty_b_name))
                                                   in
                                                (uu____8011, expected_t)  in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu____8057 =
                                                       is_fstar_value body1
                                                        in
                                                     Prims.op_Negation
                                                       uu____8057)
                                                      ||
                                                      (let uu____8060 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1
                                                          in
                                                       Prims.op_Negation
                                                         uu____8060)
                                                | uu____8062 -> false  in
                                              let rest_args1 =
                                                if add_unit
                                                then
                                                  let uu____8074 =
                                                    unit_binder ()  in
                                                  uu____8074 :: rest_args
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
                              | FStar_Syntax_Syntax.Tm_uinst uu____8131 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8150  ->
                                           match uu____8150 with
                                           | (a,uu____8158) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8170 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8190  ->
                                              match uu____8190 with
                                              | (x,uu____8199) ->
                                                  let uu____8204 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8204.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8170, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8244  ->
                                            match uu____8244 with
                                            | (bv,uu____8252) ->
                                                let uu____8257 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8257
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
                              | FStar_Syntax_Syntax.Tm_fvar uu____8287 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8300  ->
                                           match uu____8300 with
                                           | (a,uu____8308) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8320 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8340  ->
                                              match uu____8340 with
                                              | (x,uu____8349) ->
                                                  let uu____8354 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8354.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8320, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8394  ->
                                            match uu____8394 with
                                            | (bv,uu____8402) ->
                                                let uu____8407 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8407
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
                              | FStar_Syntax_Syntax.Tm_name uu____8437 ->
                                  let env =
                                    FStar_List.fold_left
                                      (fun env  ->
                                         fun uu____8450  ->
                                           match uu____8450 with
                                           | (a,uu____8458) ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env a false) g tbinders
                                     in
                                  let expected_t = term_as_mlty env tbody  in
                                  let polytype =
                                    let uu____8470 =
                                      FStar_All.pipe_right tbinders
                                        (FStar_List.map
                                           (fun uu____8490  ->
                                              match uu____8490 with
                                              | (x,uu____8499) ->
                                                  let uu____8504 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x
                                                     in
                                                  uu____8504.FStar_Extraction_ML_UEnv.ty_b_name))
                                       in
                                    (uu____8470, expected_t)  in
                                  let args =
                                    FStar_All.pipe_right tbinders
                                      (FStar_List.map
                                         (fun uu____8544  ->
                                            match uu____8544 with
                                            | (bv,uu____8552) ->
                                                let uu____8557 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8557
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
                              | uu____8587 -> err_value_restriction lbdef1)))
               | uu____8607 -> no_gen ())
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
           fun uu____8758  ->
             match uu____8758 with
             | (lbname,e_tag,(typ,(binders,mltyscheme)),add_unit,_body) ->
                 let uu____8819 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit
                    in
                 (match uu____8819 with
                  | (env1,uu____8836,exp_binding) ->
                      let uu____8840 =
                        let uu____8845 = FStar_Util.right lbname  in
                        (uu____8845, exp_binding)  in
                      (env1, uu____8840))) g lbs1
  
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
            (fun uu____8912  ->
               let uu____8913 = FStar_Syntax_Print.term_to_string e  in
               let uu____8915 =
                 let uu____8917 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g  in
                 FStar_Extraction_ML_Code.string_of_mlty uu____8917 ty  in
               let uu____8918 = FStar_Extraction_ML_Util.eff_to_string f  in
               FStar_Util.print3 "Checking %s at type %s and eff %s\n"
                 uu____8913 uu____8915 uu____8918);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____8925) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____8926 ->
               let uu____8931 = term_as_mlexpr g e  in
               (match uu____8931 with
                | (ml_e,tag,t) ->
                    let uu____8945 = FStar_Extraction_ML_Util.eff_leq tag f
                       in
                    if uu____8945
                    then
                      let uu____8952 =
                        maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t ty
                         in
                      (uu____8952, ty)
                    else
                      (match (tag, f, ty) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST
                          ,FStar_Extraction_ML_Syntax.E_PURE
                          ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                           let uu____8959 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t
                               ty
                              in
                           (uu____8959, ty)
                       | uu____8960 ->
                           (err_unexpected_eff g e ty f tag;
                            (let uu____8968 =
                               maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e
                                 t ty
                                in
                             (uu____8968, ty))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g  ->
    fun e  ->
      let uu____8977 = term_as_mlexpr' g e  in
      match uu____8977 with
      | (e1,f,t) ->
          let uu____8993 = maybe_promote_effect e1 f t  in
          (match uu____8993 with | (e2,f1) -> (e2, f1, t))

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
           let uu____9019 =
             let uu____9021 =
               FStar_Range.string_of_range top1.FStar_Syntax_Syntax.pos  in
             let uu____9023 = FStar_Syntax_Print.tag_of_term top1  in
             let uu____9025 = FStar_Syntax_Print.term_to_string top1  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____9021 uu____9023 uu____9025
              in
           FStar_Util.print_string uu____9019);
      (let is_match t =
         let uu____9035 =
           let uu____9036 =
             let uu____9039 =
               FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9039 FStar_Syntax_Util.unascribe  in
           uu____9036.FStar_Syntax_Syntax.n  in
         match uu____9035 with
         | FStar_Syntax_Syntax.Tm_match uu____9043 -> true
         | uu____9067 -> false  in
       let should_apply_to_match_branches =
         FStar_List.for_all
           (fun uu____9086  ->
              match uu____9086 with
              | (t,uu____9095) ->
                  let uu____9100 =
                    let uu____9101 =
                      FStar_All.pipe_right t FStar_Syntax_Subst.compress  in
                    uu____9101.FStar_Syntax_Syntax.n  in
                  (match uu____9100 with
                   | FStar_Syntax_Syntax.Tm_name uu____9107 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu____9109 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu____9111 -> true
                   | uu____9113 -> false))
          in
       let apply_to_match_branches head args =
         let uu____9152 =
           let uu____9153 =
             let uu____9156 =
               FStar_All.pipe_right head FStar_Syntax_Subst.compress  in
             FStar_All.pipe_right uu____9156 FStar_Syntax_Util.unascribe  in
           uu____9153.FStar_Syntax_Syntax.n  in
         match uu____9152 with
         | FStar_Syntax_Syntax.Tm_match (scrutinee,branches) ->
             let branches1 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____9280  ->
                       match uu____9280 with
                       | (pat,when_opt,body) ->
                           (pat, when_opt,
                             (let uu___1319_9337 = body  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_app (body, args));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1319_9337.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1319_9337.FStar_Syntax_Syntax.vars)
                              }))))
                in
             let uu___1322_9352 = head  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1));
               FStar_Syntax_Syntax.pos =
                 (uu___1322_9352.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___1322_9352.FStar_Syntax_Syntax.vars)
             }
         | uu____9373 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match"
          in
       let t = FStar_Syntax_Subst.compress top1  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____9384 =
             let uu____9386 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9386
              in
           failwith uu____9384
       | FStar_Syntax_Syntax.Tm_delayed uu____9395 ->
           let uu____9410 =
             let uu____9412 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9412
              in
           failwith uu____9410
       | FStar_Syntax_Syntax.Tm_uvar uu____9421 ->
           let uu____9434 =
             let uu____9436 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9436
              in
           failwith uu____9434
       | FStar_Syntax_Syntax.Tm_bvar uu____9445 ->
           let uu____9446 =
             let uu____9448 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____9448
              in
           failwith uu____9446
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____9458 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____9458
       | FStar_Syntax_Syntax.Tm_type uu____9459 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____9460 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____9467 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____9483;_})
           ->
           let uu____9496 =
             let uu____9497 =
               FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             FStar_Extraction_ML_UEnv.lookup_fv g uu____9497  in
           (match uu____9496 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu____9504;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu____9506;_} ->
                let uu____9508 =
                  let uu____9509 =
                    let uu____9510 =
                      let uu____9517 =
                        let uu____9520 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime"))
                           in
                        [uu____9520]  in
                      (fw, uu____9517)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____9510  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____9509
                   in
                (uu____9508, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____9538 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____9538 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____9546 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____9546 with
                 | FStar_Pervasives_Native.Some tm -> term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____9557 =
                         let uu____9564 =
                           FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                         FStar_Syntax_Embeddings.embed uu____9564
                           (FStar_Reflection_Data.Tv_Var bv)
                          in
                       uu____9557 t.FStar_Syntax_Syntax.pos
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Embeddings.id_norm_cb
                        in
                     let t1 =
                       let uu____9572 =
                         let uu____9583 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____9583]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____9572
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____9610 =
                    let uu____9617 =
                      FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                    FStar_Syntax_Embeddings.embed uu____9617 tv  in
                  uu____9610 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings.id_norm_cb
                   in
                let t1 =
                  let uu____9625 =
                    let uu____9636 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____9636]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____9625
                   in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____9663)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____9696 =
                  let uu____9703 =
                    let uu____9712 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                       in
                    FStar_TypeChecker_Env.effect_decl_opt uu____9712 m  in
                  FStar_Util.must uu____9703  in
                (match uu____9696 with
                 | (ed,qualifiers) ->
                     let uu____9731 =
                       let uu____9733 =
                         let uu____9735 =
                           FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                         FStar_TypeChecker_Env.is_reifiable_effect uu____9735
                           ed.FStar_Syntax_Syntax.mname
                          in
                       Prims.op_Negation uu____9733  in
                     if uu____9731
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____9752 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____9754) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____9760) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____9766 =
             let uu____9773 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
             FStar_TypeChecker_TcTerm.type_of_tot_term uu____9773 t  in
           (match uu____9766 with
            | (uu____9780,ty,uu____9782) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____9784 =
                  let uu____9785 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____9785  in
                (uu____9784, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____9786 ->
           let uu____9787 = is_type g t  in
           if uu____9787
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9798 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____9798 with
              | (FStar_Util.Inl uu____9811,uu____9812) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu____9817;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_},qual)
                  ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____9836 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____9836, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____9837 -> instantiate_maybe_partial g x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____9839 = is_type g t  in
           if uu____9839
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____9850 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____9850 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu____9859;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu____9868  ->
                        let uu____9869 = FStar_Syntax_Print.fv_to_string fv
                           in
                        let uu____9871 =
                          let uu____9873 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlexpr
                            uu____9873 x
                           in
                        let uu____9874 =
                          let uu____9876 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g
                             in
                          FStar_Extraction_ML_Code.string_of_mlty uu____9876
                            (FStar_Pervasives_Native.snd mltys)
                           in
                        FStar_Util.print3 "looked up %s: got %s at %s \n"
                          uu____9869 uu____9871 uu____9874);
                   (match mltys with
                    | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                        ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([],t1) ->
                        let uu____9888 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x
                           in
                        (uu____9888, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu____9889 -> instantiate_maybe_partial g x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,rcopt) ->
           let uu____9917 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____9917 with
            | (bs1,body1) ->
                let uu____9930 = binders_as_ml_binders g bs1  in
                (match uu____9930 with
                 | (ml_bs,env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu____9966 =
                             let uu____9968 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Env.is_reifiable_rc uu____9968
                               rc
                              in
                           if uu____9966
                           then
                             let uu____9970 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
                             FStar_TypeChecker_Util.reify_body uu____9970
                               [FStar_TypeChecker_Env.Inlining;
                               FStar_TypeChecker_Env.Unascribe] body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____9976  ->
                                 let uu____9977 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____9977);
                            body1)
                        in
                     let uu____9980 = term_as_mlexpr env body2  in
                     (match uu____9980 with
                      | (ml_body,f,t1) ->
                          let uu____9996 =
                            FStar_List.fold_right
                              (fun uu____10016  ->
                                 fun uu____10017  ->
                                   match (uu____10016, uu____10017) with
                                   | ((uu____10040,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____9996 with
                           | (f1,tfun) ->
                               let uu____10063 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____10063, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____10071;
              FStar_Syntax_Syntax.vars = uu____10072;_},(a1,uu____10074)::[])
           ->
           let ty =
             let uu____10114 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____10114  in
           let uu____10115 =
             let uu____10116 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____10116
              in
           (uu____10115, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____10117;
              FStar_Syntax_Syntax.vars = uu____10118;_},(t1,uu____10120)::
            (r,uu____10122)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____10177);
              FStar_Syntax_Syntax.pos = uu____10178;
              FStar_Syntax_Syntax.vars = uu____10179;_},uu____10180)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head,args) when
           (is_match head) &&
             (FStar_All.pipe_right args should_apply_to_match_branches)
           ->
           let uu____10239 =
             FStar_All.pipe_right args (apply_to_match_branches head)  in
           FStar_All.pipe_right uu____10239 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app (head,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___1_10293  ->
                        match uu___1_10293 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____10296 -> false)))
              in
           let uu____10298 =
             let uu____10299 =
               let uu____10302 =
                 FStar_All.pipe_right head FStar_Syntax_Subst.compress  in
               FStar_All.pipe_right uu____10302 FStar_Syntax_Util.unascribe
                in
             uu____10299.FStar_Syntax_Syntax.n  in
           (match uu____10298 with
            | FStar_Syntax_Syntax.Tm_abs (bs,uu____10312,_rc) ->
                let uu____10338 =
                  let uu____10339 =
                    let uu____10344 =
                      FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses]
                      uu____10344
                     in
                  FStar_All.pipe_right t uu____10339  in
                FStar_All.pipe_right uu____10338 (term_as_mlexpr g)
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                let e =
                  let uu____10352 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                     in
                  let uu____10353 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg uu____10352
                    [FStar_TypeChecker_Env.Inlining;
                    FStar_TypeChecker_Env.Unascribe] head uu____10353
                   in
                let tm =
                  let uu____10365 =
                    let uu____10370 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____10371 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____10370 uu____10371  in
                  uu____10365 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____10380 ->
                let rec extract_app is_data uu____10429 uu____10430 restArgs
                  =
                  match (uu____10429, uu____10430) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      let mk_head uu____10511 =
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
                         (fun uu____10538  ->
                            let uu____10539 =
                              let uu____10541 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              let uu____10542 = mk_head ()  in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____10541 uu____10542
                               in
                            let uu____10543 =
                              let uu____10545 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Extraction_ML_Code.string_of_mlty
                                uu____10545 t1
                               in
                            let uu____10546 =
                              match restArgs with
                              | [] -> "none"
                              | (hd,uu____10557)::uu____10558 ->
                                  FStar_Syntax_Print.term_to_string hd
                               in
                            FStar_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu____10539 uu____10543 uu____10546);
                       (match (restArgs, t1) with
                        | ([],uu____10592) ->
                            let app =
                              let uu____10608 = mk_head ()  in
                              maybe_eta_data_and_project_record g is_data t1
                                uu____10608
                               in
                            (app, f, t1)
                        | ((arg,uu____10610)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t,f',t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu____10641 =
                              let uu____10646 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f'
                                 in
                              (uu____10646, t2)  in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu____10641 rest
                        | ((e0,uu____10658)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected,f',t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos  in
                            let expected_effect =
                              let uu____10691 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head)
                                 in
                              if uu____10691
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE  in
                            let uu____10696 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected
                               in
                            (match uu____10696 with
                             | (e01,tInferred) ->
                                 let uu____10709 =
                                   let uu____10714 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f']
                                      in
                                   (uu____10714, t2)  in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu____10709 rest)
                        | uu____10725 ->
                            let uu____10738 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1  in
                            (match uu____10738 with
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
                                  | uu____10810 ->
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
                let extract_app_maybe_projector is_data mlhead uu____10881
                  args1 =
                  match uu____10881 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____10911)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____10995))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____10997,f',t3)) ->
                                 let uu____11035 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____11035 t3
                             | uu____11036 -> (args2, f1, t2)  in
                           let uu____11061 = remove_implicits args1 f t1  in
                           (match uu____11061 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____11117 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____11141 =
                  let head1 = FStar_Syntax_Util.un_uinst head  in
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____11149 ->
                      let uu____11150 =
                        let uu____11165 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1  in
                        match uu____11165 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11197  ->
                                  let uu____11198 =
                                    FStar_Syntax_Print.term_to_string head1
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
                                  FStar_Util.print3
                                    "@@@looked up %s: got %s at %s\n"
                                    uu____11198 uu____11200 uu____11203);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu____11221 -> failwith "FIXME Ty"  in
                      (match uu____11150 with
                       | ((head_ml,(vars,t1)),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11273)::uu____11274 -> is_type g a
                             | uu____11301 -> false  in
                           let uu____11313 =
                             let n = FStar_List.length vars  in
                             let uu____11330 =
                               if (FStar_List.length args) <= n
                               then
                                 let uu____11368 =
                                   FStar_List.map
                                     (fun uu____11380  ->
                                        match uu____11380 with
                                        | (x,uu____11388) -> term_as_mlty g x)
                                     args
                                    in
                                 (uu____11368, [])
                               else
                                 (let uu____11411 = FStar_Util.first_N n args
                                     in
                                  match uu____11411 with
                                  | (prefix,rest) ->
                                      let uu____11500 =
                                        FStar_List.map
                                          (fun uu____11512  ->
                                             match uu____11512 with
                                             | (x,uu____11520) ->
                                                 term_as_mlty g x) prefix
                                         in
                                      (uu____11500, rest))
                                in
                             match uu____11330 with
                             | (provided_type_args,rest) ->
                                 let uu____11571 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu____11580 ->
                                       let uu____11581 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____11581 with
                                        | (head2,uu____11593,t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu____11595 ->
                                       let uu____11597 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____11597 with
                                        | (head2,uu____11609,t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head2,{
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  FStar_Extraction_ML_Syntax.MLE_Const
                                                  (FStar_Extraction_ML_Syntax.MLC_Unit
                                                  );
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = uu____11612;
                                                FStar_Extraction_ML_Syntax.loc
                                                  = uu____11613;_}::[])
                                       ->
                                       let uu____11616 =
                                         instantiate_maybe_partial g head2
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____11616 with
                                        | (head3,uu____11628,t2) ->
                                            let uu____11630 =
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head3,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                               in
                                            (uu____11630, t2))
                                   | uu____11633 ->
                                       failwith
                                         "Impossible: Unexpected head term"
                                    in
                                 (match uu____11571 with
                                  | (head2,t2) -> (head2, t2, rest))
                              in
                           (match uu____11313 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____11700 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____11700,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____11701 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____11710 ->
                      let uu____11711 =
                        let uu____11726 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1  in
                        match uu____11726 with
                        | (FStar_Util.Inr exp_b,q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu____11758  ->
                                  let uu____11759 =
                                    FStar_Syntax_Print.term_to_string head1
                                     in
                                  let uu____11761 =
                                    let uu____11763 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu____11763
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr
                                     in
                                  let uu____11764 =
                                    let uu____11766 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g
                                       in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu____11766
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)
                                     in
                                  FStar_Util.print3
                                    "@@@looked up %s: got %s at %s\n"
                                    uu____11759 uu____11761 uu____11764);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu____11782 -> failwith "FIXME Ty"  in
                      (match uu____11711 with
                       | ((head_ml,(vars,t1)),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____11834)::uu____11835 -> is_type g a
                             | uu____11862 -> false  in
                           let uu____11874 =
                             let n = FStar_List.length vars  in
                             let uu____11891 =
                               if (FStar_List.length args) <= n
                               then
                                 let uu____11929 =
                                   FStar_List.map
                                     (fun uu____11941  ->
                                        match uu____11941 with
                                        | (x,uu____11949) -> term_as_mlty g x)
                                     args
                                    in
                                 (uu____11929, [])
                               else
                                 (let uu____11972 = FStar_Util.first_N n args
                                     in
                                  match uu____11972 with
                                  | (prefix,rest) ->
                                      let uu____12061 =
                                        FStar_List.map
                                          (fun uu____12073  ->
                                             match uu____12073 with
                                             | (x,uu____12081) ->
                                                 term_as_mlty g x) prefix
                                         in
                                      (uu____12061, rest))
                                in
                             match uu____11891 with
                             | (provided_type_args,rest) ->
                                 let uu____12132 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu____12141 ->
                                       let uu____12142 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____12142 with
                                        | (head2,uu____12154,t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu____12156 ->
                                       let uu____12158 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____12158 with
                                        | (head2,uu____12170,t2) ->
                                            (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head2,{
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  FStar_Extraction_ML_Syntax.MLE_Const
                                                  (FStar_Extraction_ML_Syntax.MLC_Unit
                                                  );
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = uu____12173;
                                                FStar_Extraction_ML_Syntax.loc
                                                  = uu____12174;_}::[])
                                       ->
                                       let uu____12177 =
                                         instantiate_maybe_partial g head2
                                           (vars, t1) provided_type_args
                                          in
                                       (match uu____12177 with
                                        | (head3,uu____12189,t2) ->
                                            let uu____12191 =
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head3,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                               in
                                            (uu____12191, t2))
                                   | uu____12194 ->
                                       failwith
                                         "Impossible: Unexpected head term"
                                    in
                                 (match uu____12132 with
                                  | (head2,t2) -> (head2, t2, rest))
                              in
                           (match uu____11874 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____12261 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____12261,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____12262 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____12271 ->
                      let uu____12272 = term_as_mlexpr g head1  in
                      (match uu____12272 with
                       | (head2,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head2 (f, t1) args)
                   in
                let uu____12288 = is_type g t  in
                if uu____12288
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____12299 =
                     let uu____12300 = FStar_Syntax_Util.un_uinst head  in
                     uu____12300.FStar_Syntax_Syntax.n  in
                   match uu____12299 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____12310 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____12310 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____12319 -> extract_app_with_instantiations ())
                   | uu____12322 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____12325),f) ->
           let t1 =
             match tc with
             | FStar_Util.Inl t1 -> term_as_mlty g t1
             | FStar_Util.Inr c ->
                 let uu____12390 =
                   let uu____12391 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g
                      in
                   maybe_reify_comp g uu____12391 c  in
                 term_as_mlty g uu____12390
              in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None  ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l  in
           let uu____12395 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____12395 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e') when
           (let uu____12427 = FStar_Syntax_Syntax.is_top_level [lb]  in
            Prims.op_Negation uu____12427) &&
             (let uu____12430 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs
                 in
              FStar_Util.is_some uu____12430)
           ->
           let b =
             let uu____12440 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                in
             (uu____12440, FStar_Pervasives_Native.None)  in
           let uu____12443 = FStar_Syntax_Subst.open_term_1 b e'  in
           (match uu____12443 with
            | ((x,uu____12455),body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str,uu____12470)::[]) ->
                      let uu____12495 =
                        let uu____12496 = FStar_Syntax_Subst.compress str  in
                        uu____12496.FStar_Syntax_Syntax.n  in
                      (match uu____12495 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s,uu____12502)) ->
                           let id =
                             let uu____12506 =
                               let uu____12512 =
                                 FStar_Syntax_Syntax.range_of_bv x  in
                               (s, uu____12512)  in
                             FStar_Ident.mk_ident uu____12506  in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             }  in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv  in
                           FStar_Pervasives_Native.Some bv1
                       | uu____12517 -> FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____12518 ->
                      (FStar_Errors.log_issue top1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `rename_let`");
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pervasives_Native.None
                   in
                let remove_attr attrs =
                  let uu____12538 =
                    FStar_List.partition
                      (fun attr  ->
                         let uu____12550 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr]
                            in
                         FStar_Util.is_some uu____12550)
                      lb.FStar_Syntax_Syntax.lbattrs
                     in
                  match uu____12538 with
                  | (uu____12555,other_attrs) -> other_attrs  in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None  ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs  in
                      FStar_Syntax_Syntax.Tm_let
                        ((false,
                           [(let uu___1774_12583 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1774_12583.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1774_12583.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1774_12583.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1774_12583.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef =
                                 (uu___1774_12583.FStar_Syntax_Syntax.lbdef);
                               FStar_Syntax_Syntax.lbattrs = other_attrs;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1774_12583.FStar_Syntax_Syntax.lbpos)
                             })]), e')
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs  in
                      let rename =
                        let uu____12591 =
                          let uu____12592 =
                            let uu____12599 =
                              FStar_Syntax_Syntax.bv_to_name y  in
                            (x, uu____12599)  in
                          FStar_Syntax_Syntax.NT uu____12592  in
                        [uu____12591]  in
                      let body1 =
                        let uu____12605 =
                          FStar_Syntax_Subst.subst rename body  in
                        FStar_Syntax_Subst.close
                          [(y, FStar_Pervasives_Native.None)] uu____12605
                         in
                      let lb1 =
                        let uu___1781_12621 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname = (FStar_Util.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (uu___1781_12621.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (uu___1781_12621.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1781_12621.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (uu___1781_12621.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1781_12621.FStar_Syntax_Syntax.lbpos)
                        }  in
                      FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1)
                   in
                let top2 =
                  let uu___1785_12638 = top1  in
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos =
                      (uu___1785_12638.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (uu___1785_12638.FStar_Syntax_Syntax.vars)
                  }  in
                term_as_mlexpr' g top2)
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____12661 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____12677 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____12677
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____12692 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____12692  in
                   let lb1 =
                     let uu___1799_12694 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___1799_12694.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___1799_12694.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___1799_12694.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___1799_12694.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___1799_12694.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___1799_12694.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____12661 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu____12719 =
                        FStar_Extraction_ML_UEnv.tcenv_of_uenv g  in
                      let uu____12720 =
                        let uu____12721 =
                          let uu____12722 =
                            let uu____12726 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g
                               in
                            FStar_Pervasives_Native.fst uu____12726  in
                          let uu____12739 =
                            let uu____12743 =
                              let uu____12745 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g
                                 in
                              FStar_Pervasives_Native.snd uu____12745  in
                            [uu____12743]  in
                          FStar_List.append uu____12722 uu____12739  in
                        FStar_Ident.lid_of_path uu____12721
                          FStar_Range.dummyRange
                         in
                      FStar_TypeChecker_Env.set_current_module uu____12719
                        uu____12720
                       in
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let lbdef =
                              let uu____12772 = FStar_Options.ml_ish ()  in
                              if uu____12772
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu____12784 =
                                   let uu____12785 =
                                     let uu____12786 =
                                       extraction_norm_steps ()  in
                                     FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                       :: uu____12786
                                      in
                                   FStar_TypeChecker_Normalize.normalize
                                     uu____12785 tcenv
                                     lb.FStar_Syntax_Syntax.lbdef
                                    in
                                 let uu____12789 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm"))
                                    in
                                 if uu____12789
                                 then
                                   ((let uu____12799 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Util.print1
                                       "Starting to normalize top-level let %s\n"
                                       uu____12799);
                                    (let a =
                                       let uu____12805 =
                                         let uu____12807 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lb.FStar_Syntax_Syntax.lbname
                                            in
                                         FStar_Util.format1
                                           "###(Time to normalize top-level let %s)"
                                           uu____12807
                                          in
                                       FStar_Util.measure_execution_time
                                         uu____12805 norm_call
                                        in
                                     a))
                                 else norm_call ())
                               in
                            let uu___1816_12814 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1816_12814.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1816_12814.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___1816_12814.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1816_12814.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1816_12814.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1816_12814.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let check_lb env uu____12867 =
                  match uu____12867 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____13023  ->
                               match uu____13023 with
                               | (a,uu____13031) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     false) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____13038 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____13038 with
                       | (e1,ty) ->
                           let uu____13049 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____13049 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____13061 -> []  in
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
                let uu____13092 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____13189  ->
                         match uu____13189 with
                         | (env,lbs4) ->
                             let uu____13323 = lb  in
                             (match uu____13323 with
                              | (lbname,uu____13374,(t1,(uu____13376,polytype)),add_unit,uu____13379)
                                  ->
                                  let uu____13394 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit
                                     in
                                  (match uu____13394 with
                                   | (env1,nm,uu____13434) ->
                                       (env1, ((nm, lb) :: lbs4))))) lbs3
                    (g, [])
                   in
                (match uu____13092 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____13713 = term_as_mlexpr env_body e'1  in
                     (match uu____13713 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____13730 =
                              let uu____13733 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____13733  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____13730
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____13746 =
                            let uu____13747 =
                              let uu____13748 =
                                let uu____13749 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____13749)  in
                              mk_MLE_Let top_level uu____13748 e'2  in
                            let uu____13758 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____13747 uu____13758
                             in
                          (uu____13746, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____13797 = term_as_mlexpr g scrutinee  in
           (match uu____13797 with
            | (e,f_e,t_e) ->
                let uu____13813 = check_pats_for_ite pats  in
                (match uu____13813 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____13878 = term_as_mlexpr g then_e1  in
                            (match uu____13878 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____13894 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____13894 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____13910 =
                                        let uu____13921 =
                                          type_leq g t_then t_else  in
                                        if uu____13921
                                        then (t_else, no_lift)
                                        else
                                          (let uu____13942 =
                                             type_leq g t_else t_then  in
                                           if uu____13942
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____13910 with
                                       | (t_branch,maybe_lift) ->
                                           let uu____13989 =
                                             let uu____13990 =
                                               let uu____13991 =
                                                 let uu____14000 =
                                                   maybe_lift then_mle t_then
                                                    in
                                                 let uu____14001 =
                                                   let uu____14004 =
                                                     maybe_lift else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____14004
                                                    in
                                                 (e, uu____14000,
                                                   uu____14001)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____13991
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____13990
                                              in
                                           let uu____14007 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____13989, uu____14007,
                                             t_branch))))
                        | uu____14008 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____14026 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____14125 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____14125 with
                                    | (pat,when_opt,branch) ->
                                        let uu____14170 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____14170 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____14232 =
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
                                                   let uu____14255 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____14255 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____14232 with
                                              | (when_opt1,f_when) ->
                                                  let uu____14305 =
                                                    term_as_mlexpr env branch
                                                     in
                                                  (match uu____14305 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____14340 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____14417 
                                                                 ->
                                                                 match uu____14417
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
                                                         uu____14340)))))
                               true)
                           in
                        match uu____14026 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____14588  ->
                                      let uu____14589 =
                                        let uu____14591 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu____14591 e
                                         in
                                      let uu____14592 =
                                        let uu____14594 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g
                                           in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu____14594 t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____14589 uu____14592);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____14620 =
                                   let uu____14621 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.failwith_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Extraction_ML_UEnv.lookup_fv g
                                     uu____14621
                                    in
                                 (match uu____14620 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu____14628;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu____14630;_}
                                      ->
                                      let uu____14632 =
                                        let uu____14633 =
                                          let uu____14634 =
                                            let uu____14641 =
                                              let uu____14644 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____14644]  in
                                            (fw, uu____14641)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____14634
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____14633
                                         in
                                      (uu____14632,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____14648,uu____14649,(uu____14650,f_first,t_first))::rest
                                 ->
                                 let uu____14710 =
                                   FStar_List.fold_left
                                     (fun uu____14752  ->
                                        fun uu____14753  ->
                                          match (uu____14752, uu____14753)
                                          with
                                          | ((topt,f),(uu____14810,uu____14811,
                                                       (uu____14812,f_branch,t_branch)))
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
                                                    let uu____14868 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____14868
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____14875 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____14875
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
                                 (match uu____14710 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____14973  ->
                                                match uu____14973 with
                                                | (p,(wopt,uu____15002),
                                                   (b1,uu____15004,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____15023 -> b1
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
                                      let uu____15028 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____15028, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____15055 =
          let uu____15060 =
            let uu____15069 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
            FStar_TypeChecker_Env.lookup_lid uu____15069 discName  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____15060  in
        match uu____15055 with
        | (uu____15086,fstar_disc_type) ->
            let uu____15088 =
              let uu____15100 =
                let uu____15101 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____15101.FStar_Syntax_Syntax.n  in
              match uu____15100 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____15116) ->
                  let binders1 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___2_15171  ->
                            match uu___2_15171 with
                            | (uu____15179,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____15180)) ->
                                true
                            | uu____15185 -> false))
                     in
                  FStar_List.fold_right
                    (fun uu____15217  ->
                       fun uu____15218  ->
                         match uu____15218 with
                         | (g,vs) ->
                             let uu____15263 =
                               FStar_Extraction_ML_UEnv.new_mlident g  in
                             (match uu____15263 with
                              | (g1,v) ->
                                  (g1,
                                    ((v, FStar_Extraction_ML_Syntax.MLTY_Top)
                                    :: vs)))) binders1 (env, [])
              | uu____15309 -> failwith "Discriminator must be a function"
               in
            (match uu____15088 with
             | (g,wildcards) ->
                 let uu____15338 = FStar_Extraction_ML_UEnv.new_mlident g  in
                 (match uu____15338 with
                  | (g1,mlid) ->
                      let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
                      let discrBody =
                        let uu____15351 =
                          let uu____15352 =
                            let uu____15364 =
                              let uu____15365 =
                                let uu____15366 =
                                  let uu____15381 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         targ)
                                      (FStar_Extraction_ML_Syntax.MLE_Name
                                         ([], mlid))
                                     in
                                  let uu____15387 =
                                    let uu____15398 =
                                      let uu____15407 =
                                        let uu____15408 =
                                          let uu____15415 =
                                            FStar_Extraction_ML_UEnv.mlpath_of_lident
                                              g1 constrName
                                             in
                                          (uu____15415,
                                            [FStar_Extraction_ML_Syntax.MLP_Wild])
                                           in
                                        FStar_Extraction_ML_Syntax.MLP_CTor
                                          uu____15408
                                         in
                                      let uu____15418 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_bool_ty)
                                          (FStar_Extraction_ML_Syntax.MLE_Const
                                             (FStar_Extraction_ML_Syntax.MLC_Bool
                                                true))
                                         in
                                      (uu____15407,
                                        FStar_Pervasives_Native.None,
                                        uu____15418)
                                       in
                                    let uu____15422 =
                                      let uu____15433 =
                                        let uu____15442 =
                                          FStar_All.pipe_left
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.ml_bool_ty)
                                            (FStar_Extraction_ML_Syntax.MLE_Const
                                               (FStar_Extraction_ML_Syntax.MLC_Bool
                                                  false))
                                           in
                                        (FStar_Extraction_ML_Syntax.MLP_Wild,
                                          FStar_Pervasives_Native.None,
                                          uu____15442)
                                         in
                                      [uu____15433]  in
                                    uu____15398 :: uu____15422  in
                                  (uu____15381, uu____15387)  in
                                FStar_Extraction_ML_Syntax.MLE_Match
                                  uu____15366
                                 in
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                uu____15365
                               in
                            ((FStar_List.append wildcards [(mlid, targ)]),
                              uu____15364)
                             in
                          FStar_Extraction_ML_Syntax.MLE_Fun uu____15352  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty disc_ty)
                          uu____15351
                         in
                      let uu____15503 =
                        FStar_Extraction_ML_UEnv.mlpath_of_lident env
                          discName
                         in
                      (match uu____15503 with
                       | (uu____15504,name) ->
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
  