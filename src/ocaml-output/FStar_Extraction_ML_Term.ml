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
          | FStar_Pervasives_Native.Some (uu____399,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____409 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____409
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____411 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____411
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.tcenv l1
               in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____434 =
                  FStar_All.pipe_right qualifiers
                    (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                   in
                if uu____434
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____455 =
        let uu____456 = FStar_Syntax_Subst.compress t1  in
        uu____456.FStar_Syntax_Syntax.n  in
      match uu____455 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____459 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____484 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____511 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____519 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____519
      | FStar_Syntax_Syntax.Tm_uvar uu____520 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____535 -> false
      | FStar_Syntax_Syntax.Tm_name uu____536 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____537 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____544 -> false
      | FStar_Syntax_Syntax.Tm_type uu____545 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____546,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____564 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1
             in
          let uu____566 =
            let uu____567 = FStar_Syntax_Subst.compress t2  in
            uu____567.FStar_Syntax_Syntax.n  in
          (match uu____566 with
           | FStar_Syntax_Syntax.Tm_fvar uu____570 -> false
           | uu____571 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____572 ->
          let uu____587 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____587 with | (head1,uu____603) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____625) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____631) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____636,body,uu____638) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____659,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____677,branches) ->
          (match branches with
           | (uu____715,uu____716,e)::uu____718 -> is_arity env e
           | uu____765 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____793 ->
          let uu____818 =
            let uu____819 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____819  in
          failwith uu____818
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____820 =
            let uu____821 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____821  in
          failwith uu____820
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____823 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____823
      | FStar_Syntax_Syntax.Tm_constant uu____824 -> false
      | FStar_Syntax_Syntax.Tm_type uu____825 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____826 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____833 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          ({ FStar_Syntax_Syntax.ctx_uvar_head = uu____848;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____849;
             FStar_Syntax_Syntax.ctx_uvar_binders = uu____850;
             FStar_Syntax_Syntax.ctx_uvar_typ = t2;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____852;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____853;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____854;_},s)
          ->
          let uu____896 = FStar_Syntax_Subst.subst' s t2  in
          is_arity env uu____896
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____897;
            FStar_Syntax_Syntax.index = uu____898;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____902;
            FStar_Syntax_Syntax.index = uu____903;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____908,uu____909) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____951) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____958) ->
          let uu____979 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____979 with | (uu____984,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____1001 =
            let uu____1006 =
              let uu____1007 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____1007]  in
            FStar_Syntax_Subst.open_term uu____1006 body  in
          (match uu____1001 with
           | (uu____1020,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____1022,lbs),body) ->
          let uu____1039 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____1039 with
           | (uu____1046,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1052,branches) ->
          (match branches with
           | b::uu____1091 ->
               let uu____1136 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1136 with
                | (uu____1137,uu____1138,e) -> is_type_aux env e)
           | uu____1156 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1173 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1181) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1187) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1222  ->
           let uu____1223 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1224 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1223
             uu____1224);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1230  ->
            if b
            then
              let uu____1231 = FStar_Syntax_Print.term_to_string t  in
              let uu____1232 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1231 uu____1232
            else
              (let uu____1234 = FStar_Syntax_Print.term_to_string t  in
               let uu____1235 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1234 uu____1235));
       b)
  
let is_type_binder :
  'Auu____1242 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1242) FStar_Pervasives_Native.tuple2 ->
        Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1266 =
      let uu____1267 = FStar_Syntax_Subst.compress t  in
      uu____1267.FStar_Syntax_Syntax.n  in
    match uu____1266 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1270;
          FStar_Syntax_Syntax.fv_delta = uu____1271;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1272;
          FStar_Syntax_Syntax.fv_delta = uu____1273;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1274);_}
        -> true
    | uu____1281 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1287 =
      let uu____1288 = FStar_Syntax_Subst.compress t  in
      uu____1288.FStar_Syntax_Syntax.n  in
    match uu____1287 with
    | FStar_Syntax_Syntax.Tm_constant uu____1291 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1292 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1293 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1294 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1333 = is_constructor head1  in
        if uu____1333
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1347  ->
                  match uu____1347 with
                  | (te,uu____1353) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1356) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1362,uu____1363) ->
        is_fstar_value t1
    | uu____1404 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1410 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1411 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1412 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1413 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1424,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1433,fields) ->
        FStar_Util.for_all
          (fun uu____1458  ->
             match uu____1458 with | (uu____1463,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1466) -> is_ml_value h
    | uu____1471 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1514 =
       let uu____1515 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____1515  in
     Prims.strcat x uu____1514)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1630 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1632 = FStar_Syntax_Util.is_fun e'  in
          if uu____1632
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1640 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1640 
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
      (let uu____1720 = FStar_List.hd l  in
       match uu____1720 with
       | (p1,w1,e1) ->
           let uu____1754 =
             let uu____1763 = FStar_List.tl l  in FStar_List.hd uu____1763
              in
           (match uu____1754 with
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
                 | uu____1837 -> def)))
  
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
      let uu____1874 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1874 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1894  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____1905 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____1919  ->
                    match uu____1919 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1905
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
      let uu____1945 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1945 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____1965 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____1965 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____1969 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____1977  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____1985 =
               let uu____1986 =
                 let uu____1997 = body r  in (vs_ts, uu____1997)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____1986  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____1985)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____2014 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____2016 = FStar_Options.codegen ()  in
           uu____2016 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____2014 then e else eta_expand expect e
  
let maybe_coerce :
  'Auu____2034 .
    'Auu____2034 ->
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
            let uu____2061 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____2061 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____2071 ->
                (FStar_Extraction_ML_UEnv.debug g
                   (fun uu____2083  ->
                      let uu____2084 =
                        FStar_Extraction_ML_Code.string_of_mlexpr
                          g.FStar_Extraction_ML_UEnv.currentModule e
                         in
                      let uu____2085 =
                        FStar_Extraction_ML_Code.string_of_mlty
                          g.FStar_Extraction_ML_UEnv.currentModule ty1
                         in
                      let uu____2086 =
                        FStar_Extraction_ML_Code.string_of_mlty
                          g.FStar_Extraction_ML_UEnv.currentModule expect
                         in
                      FStar_Util.print3
                        "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                        uu____2084 uu____2085 uu____2086);
                 (match ty1 with
                  | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                      default_value_for_ty g expect
                  | uu____2087 ->
                      let uu____2088 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty expect)
                          (FStar_Extraction_ML_Syntax.MLE_Coerce
                             (e, ty1, expect))
                         in
                      maybe_eta_expand expect uu____2088))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____2099 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____2099 with
      | FStar_Util.Inl (uu____2100,t) -> t
      | uu____2114 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let (basic_norm_steps : FStar_TypeChecker_Normalize.step Prims.list) =
  [FStar_TypeChecker_Normalize.Beta;
  FStar_TypeChecker_Normalize.Eager_unfolding;
  FStar_TypeChecker_Normalize.Iota;
  FStar_TypeChecker_Normalize.Zeta;
  FStar_TypeChecker_Normalize.Inlining;
  FStar_TypeChecker_Normalize.EraseUniverses;
  FStar_TypeChecker_Normalize.AllowUnboundUniverses] 
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t0  ->
      let arg_as_mlty g1 uu____2159 =
        match uu____2159 with
        | (a,uu____2165) ->
            let uu____2166 = is_type g1 a  in
            if uu____2166
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____2184 =
          let uu____2185 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____2185  in
        if uu____2184
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____2187 =
             let uu____2200 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____2200 with
             | ((uu____2221,fvty),uu____2223) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.UnfoldUntil
                        FStar_Syntax_Syntax.delta_constant]
                     g1.FStar_Extraction_ML_UEnv.tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____2187 with
           | (formals,uu____2230) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____2276 = FStar_Util.first_N n_args formals  in
                   match uu____2276 with
                   | (uu____2303,rest) ->
                       let uu____2329 =
                         FStar_List.map
                           (fun uu____2337  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____2329
                 else mlargs  in
               let nm =
                 let uu____2344 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____2344 with
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
        | FStar_Syntax_Syntax.Tm_type uu____2362 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____2363 ->
            let uu____2364 =
              let uu____2365 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2365
               in
            failwith uu____2364
        | FStar_Syntax_Syntax.Tm_delayed uu____2366 ->
            let uu____2391 =
              let uu____2392 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2392
               in
            failwith uu____2391
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____2393 =
              let uu____2394 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2394
               in
            failwith uu____2393
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____2396 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____2396
        | FStar_Syntax_Syntax.Tm_constant uu____2397 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____2398 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____2405 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2421) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____2426;
               FStar_Syntax_Syntax.index = uu____2427;
               FStar_Syntax_Syntax.sort = t2;_},uu____2429)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2437) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2443,uu____2444) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____2511 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____2511 with
             | (bs1,c1) ->
                 let uu____2518 = binders_as_ml_binders env bs1  in
                 (match uu____2518 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let uu____2545 =
                          let uu____2552 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.tcenv eff
                             in
                          FStar_Util.must uu____2552  in
                        match uu____2545 with
                        | (ed,qualifiers) ->
                            let uu____2573 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____2573
                            then
                              let t2 =
                                FStar_TypeChecker_Env.reify_comp
                                  env1.FStar_Extraction_ML_UEnv.tcenv c1
                                  FStar_Syntax_Syntax.U_unknown
                                 in
                              let res = translate_term_to_mlty env1 t2  in
                              res
                            else
                              translate_term_to_mlty env1
                                (FStar_Syntax_Util.comp_result c1)
                         in
                      let erase =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1)
                         in
                      let uu____2580 =
                        FStar_List.fold_right
                          (fun uu____2599  ->
                             fun uu____2600  ->
                               match (uu____2599, uu____2600) with
                               | ((uu____2621,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____2580 with | (uu____2633,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____2658 =
                let uu____2659 = FStar_Syntax_Util.un_uinst head1  in
                uu____2659.FStar_Syntax_Syntax.n  in
              match uu____2658 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____2686 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____2686
              | uu____2703 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2706) ->
            let uu____2727 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____2727 with
             | (bs1,ty1) ->
                 let uu____2734 = binders_as_ml_binders env bs1  in
                 (match uu____2734 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____2759 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____2772 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____2801 ->
            let uu____2808 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____2808 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____2812 -> false  in
      let uu____2813 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.tcenv t0
         in
      if uu____2813
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____2816 = is_top_ty mlt  in
         if uu____2816
         then
           let t =
             FStar_TypeChecker_Normalize.normalize
               ((FStar_TypeChecker_Normalize.UnfoldUntil
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
      let uu____2831 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2880  ->
                fun b  ->
                  match uu____2880 with
                  | (ml_bs,env) ->
                      let uu____2920 = is_type_binder g b  in
                      if uu____2920
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____2938 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____2938, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____2952 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____2952 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2974 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____2974, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____2831 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____3057) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____3060,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____3064 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____3090 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____3091 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____3092 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____3101 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____3128 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____3128 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____3132 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____3159 -> p))
      | uu____3162 -> p
  
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
                       (fun uu____3254  ->
                          let uu____3255 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____3256 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____3255 uu____3256)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____3286 = FStar_Options.codegen ()  in
                uu____3286 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____3291 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3304 =
                        let uu____3305 =
                          let uu____3306 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____3306  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____3305
                         in
                      (uu____3304, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____3327 = term_as_mlexpr g source_term  in
                      (match uu____3327 with
                       | (mlterm,uu____3339,mlty) -> (mlterm, mlty))
                   in
                (match uu____3291 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____3359 =
                         let uu____3360 =
                           let uu____3367 =
                             let uu____3370 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____3370; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____3367)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____3360  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3359
                        in
                     let uu____3373 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____3373))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____3393 =
                  let uu____3402 =
                    let uu____3409 =
                      let uu____3410 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____3410  in
                    (uu____3409, [])  in
                  FStar_Pervasives_Native.Some uu____3402  in
                let uu____3419 = ok mlty  in (g, uu____3393, uu____3419)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3430 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3430 with
                 | (g1,x1) ->
                     let uu____3451 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3451))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3485 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3485 with
                 | (g1,x1) ->
                     let uu____3506 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3506))
            | FStar_Syntax_Syntax.Pat_dot_term uu____3538 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____3577 =
                  let uu____3586 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____3586 with
                  | FStar_Util.Inr
                      (uu____3595,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____3597;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____3598;_},ttys,uu____3600)
                      -> (n1, ttys)
                  | uu____3617 -> failwith "Expected a constructor"  in
                (match uu____3577 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____3651 = FStar_Util.first_N nTyVars pats  in
                     (match uu____3651 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____3780  ->
                                        match uu____3780 with
                                        | (p1,uu____3786) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____3787,t) ->
                                                 term_as_mlty g t
                                             | uu____3793 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____3797  ->
                                                       let uu____3798 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1
                                                          in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____3798);
                                                  FStar_Exn.raise
                                                    Un_extractable))))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              let uu____3800 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty
                                 in
                              FStar_Pervasives_Native.Some uu____3800
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____3829 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____3865  ->
                                   match uu____3865 with
                                   | (p1,imp1) ->
                                       let uu____3884 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____3884 with
                                        | (g2,p2,uu____3913) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____3829 with
                           | (g1,tyMLPats) ->
                               let uu____3974 =
                                 FStar_Util.fold_map
                                   (fun uu____4038  ->
                                      fun uu____4039  ->
                                        match (uu____4038, uu____4039) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____4132 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____4192 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____4132 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____4263 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____4263 with
                                                  | (g3,p2,uu____4304) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____3974 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____4422 =
                                      let uu____4433 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___84_4484  ->
                                                match uu___84_4484 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____4526 -> []))
                                         in
                                      FStar_All.pipe_right uu____4433
                                        FStar_List.split
                                       in
                                    (match uu____4422 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____4599 -> false  in
                                         let uu____4608 =
                                           let uu____4617 =
                                             let uu____4624 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____4627 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____4624, uu____4627)  in
                                           FStar_Pervasives_Native.Some
                                             uu____4617
                                            in
                                         (g2, uu____4608, pat_ty_compat))))))
  
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
            let uu____4754 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____4754 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____4811 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____4856 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____4856
             in
          let uu____4857 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____4857 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____5007,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____5010 =
                  let uu____5021 =
                    let uu____5030 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____5030)  in
                  uu____5021 :: more_args  in
                eta_args uu____5010 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____5043,uu____5044)
                -> ((FStar_List.rev more_args), t)
            | uu____5067 ->
                let uu____5068 =
                  let uu____5069 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____5070 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____5069 uu____5070
                   in
                failwith uu____5068
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____5102,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____5134 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____5156 = eta_args [] residualType  in
            match uu____5156 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____5209 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____5209
                 | uu____5210 ->
                     let uu____5221 = FStar_List.unzip eargs  in
                     (match uu____5221 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____5263 =
                                   let uu____5264 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____5264
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____5263
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____5273 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____5276,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5280;
                FStar_Extraction_ML_Syntax.loc = uu____5281;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5302 ->
                    let uu____5305 =
                      let uu____5312 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5312, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5305
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
                     FStar_Extraction_ML_Syntax.mlty = uu____5316;
                     FStar_Extraction_ML_Syntax.loc = uu____5317;_},uu____5318);
                FStar_Extraction_ML_Syntax.mlty = uu____5319;
                FStar_Extraction_ML_Syntax.loc = uu____5320;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5345 ->
                    let uu____5348 =
                      let uu____5355 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5355, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5348
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5359;
                FStar_Extraction_ML_Syntax.loc = uu____5360;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5368 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5368
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5372;
                FStar_Extraction_ML_Syntax.loc = uu____5373;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5375)) ->
              let uu____5388 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5388
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5392;
                     FStar_Extraction_ML_Syntax.loc = uu____5393;_},uu____5394);
                FStar_Extraction_ML_Syntax.mlty = uu____5395;
                FStar_Extraction_ML_Syntax.loc = uu____5396;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5408 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5408
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5412;
                     FStar_Extraction_ML_Syntax.loc = uu____5413;_},uu____5414);
                FStar_Extraction_ML_Syntax.mlty = uu____5415;
                FStar_Extraction_ML_Syntax.loc = uu____5416;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5418)) ->
              let uu____5435 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5435
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5441 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5441
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5445)) ->
              let uu____5454 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5454
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5458;
                FStar_Extraction_ML_Syntax.loc = uu____5459;_},uu____5460),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5467 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5467
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5471;
                FStar_Extraction_ML_Syntax.loc = uu____5472;_},uu____5473),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5474)) ->
              let uu____5487 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5487
          | uu____5490 -> mlAppExpr
  
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
        | uu____5520 -> (ml_e, tag)
  
type generalized_lb =
  (FStar_Syntax_Syntax.lbname,FStar_Extraction_ML_Syntax.e_tag,(FStar_Syntax_Syntax.typ,
                                                                 (FStar_Syntax_Syntax.binders,
                                                                   FStar_Extraction_ML_Syntax.mltyscheme)
                                                                   FStar_Pervasives_Native.tuple2)
                                                                 FStar_Pervasives_Native.tuple2,
    Prims.bool,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple5
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
            (fun uu____5603  ->
               let uu____5604 = FStar_Syntax_Print.term_to_string e  in
               let uu____5605 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____5604
                 uu____5605);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5610) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____5611 ->
               let uu____5616 = term_as_mlexpr g e  in
               (match uu____5616 with
                | (ml_e,tag,t) ->
                    let uu____5630 = maybe_promote_effect ml_e tag t  in
                    (match uu____5630 with
                     | (ml_e1,tag1) ->
                         let uu____5641 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____5641
                         then
                           let uu____5646 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____5646, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____5652 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____5652, ty)
                            | uu____5653 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____5661 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____5661, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g  ->
    fun e  ->
      let uu____5664 = term_as_mlexpr' g e  in
      match uu____5664 with
      | (e1,f,t) ->
          let uu____5680 = maybe_promote_effect e1 f t  in
          (match uu____5680 with | (e2,f1) -> (e2, f1, t))

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
           let uu____5705 =
             let uu____5706 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____5707 = FStar_Syntax_Print.tag_of_term top  in
             let uu____5708 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5706 uu____5707 uu____5708
              in
           FStar_Util.print_string uu____5705);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5716 =
             let uu____5717 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5717
              in
           failwith uu____5716
       | FStar_Syntax_Syntax.Tm_delayed uu____5724 ->
           let uu____5749 =
             let uu____5750 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5750
              in
           failwith uu____5749
       | FStar_Syntax_Syntax.Tm_uvar uu____5757 ->
           let uu____5772 =
             let uu____5773 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5773
              in
           failwith uu____5772
       | FStar_Syntax_Syntax.Tm_bvar uu____5780 ->
           let uu____5781 =
             let uu____5782 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5782
              in
           failwith uu____5781
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____5790 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____5790
       | FStar_Syntax_Syntax.Tm_type uu____5791 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5792 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5799 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____5813;_})
           ->
           let uu____5828 =
             let uu____5837 =
               let uu____5854 =
                 FStar_Syntax_Syntax.lid_as_fv
                   FStar_Parser_Const.failwith_lid
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.lookup_fv g uu____5854  in
             FStar_All.pipe_left FStar_Util.right uu____5837  in
           (match uu____5828 with
            | (uu____5897,fw,uu____5899,uu____5900) ->
                let uu____5901 =
                  let uu____5902 =
                    let uu____5903 =
                      let uu____5910 =
                        let uu____5913 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Open quotation at runtime"))
                           in
                        [uu____5913]  in
                      (fw, uu____5910)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5903  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____5902
                   in
                (uu____5901, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____5932 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____5932 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____5940 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____5940 with
                 | FStar_Pervasives_Native.Some (false ,tm) ->
                     term_as_mlexpr g tm
                 | FStar_Pervasives_Native.Some (true ,tm) ->
                     let uu____5963 =
                       let uu____5972 =
                         let uu____5989 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.failwith_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         FStar_Extraction_ML_UEnv.lookup_fv g uu____5989  in
                       FStar_All.pipe_left FStar_Util.right uu____5972  in
                     (match uu____5963 with
                      | (uu____6032,fw,uu____6034,uu____6035) ->
                          let uu____6036 =
                            let uu____6037 =
                              let uu____6038 =
                                let uu____6045 =
                                  let uu____6048 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         FStar_Extraction_ML_Syntax.ml_string_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_String
                                            "Open quotation at runtime"))
                                     in
                                  [uu____6048]  in
                                (fw, uu____6045)  in
                              FStar_Extraction_ML_Syntax.MLE_App uu____6038
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____6037
                             in
                          (uu____6036, FStar_Extraction_ML_Syntax.E_PURE,
                            FStar_Extraction_ML_Syntax.ml_int_ty))
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____6056 =
                         FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                       FStar_Syntax_Embeddings.embed uu____6056
                         t.FStar_Syntax_Syntax.pos
                         (FStar_Reflection_Data.Tv_Var bv)
                        in
                     let t1 =
                       let uu____6062 =
                         let uu____6071 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____6071]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____6062
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____6092 =
                    FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                  FStar_Syntax_Embeddings.embed uu____6092
                    t.FStar_Syntax_Syntax.pos tv
                   in
                let t1 =
                  let uu____6098 =
                    let uu____6107 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____6107]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____6098
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
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____6139)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____6169 =
                  let uu____6176 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m
                     in
                  FStar_Util.must uu____6176  in
                (match uu____6169 with
                 | (ed,qualifiers) ->
                     let uu____6203 =
                       let uu____6204 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                          in
                       FStar_All.pipe_right uu____6204 Prims.op_Negation  in
                     if uu____6203
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____6220 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6222) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6228) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6234 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____6234 with
            | (uu____6247,ty,uu____6249) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____6251 =
                  let uu____6252 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____6252  in
                (uu____6251, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____6253 ->
           let uu____6254 = is_type g t  in
           if uu____6254
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6262 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____6262 with
              | (FStar_Util.Inl uu____6275,uu____6276) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____6297,x,mltys,uu____6300),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____6326 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____6326, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6327 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____6335 = is_type g t  in
           if uu____6335
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6343 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____6343 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____6352) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | FStar_Pervasives_Native.Some (FStar_Util.Inr
                  (uu____6369,x,mltys,uu____6372)) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____6393 =
                         maybe_eta_data_and_project_record g
                           fv.FStar_Syntax_Syntax.fv_qual t1 x
                          in
                       (uu____6393, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6394 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____6424 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____6424 with
            | (bs1,body1) ->
                let uu____6437 = binders_as_ml_binders g bs1  in
                (match uu____6437 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____6470 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c
                              in
                           if uu____6470
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____6475  ->
                                 let uu____6476 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____6476);
                            body1)
                        in
                     let uu____6477 = term_as_mlexpr env body2  in
                     (match uu____6477 with
                      | (ml_body,f,t1) ->
                          let uu____6493 =
                            FStar_List.fold_right
                              (fun uu____6512  ->
                                 fun uu____6513  ->
                                   match (uu____6512, uu____6513) with
                                   | ((uu____6534,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____6493 with
                           | (f1,tfun) ->
                               let uu____6554 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____6554, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6561;
              FStar_Syntax_Syntax.vars = uu____6562;_},(a1,uu____6564)::[])
           ->
           let ty =
             let uu____6594 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____6594  in
           let uu____6595 =
             let uu____6596 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____6596
              in
           (uu____6595, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6597;
              FStar_Syntax_Syntax.vars = uu____6598;_},(t1,uu____6600)::
            (r,uu____6602)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6641);
              FStar_Syntax_Syntax.pos = uu____6642;
              FStar_Syntax_Syntax.vars = uu____6643;_},uu____6644)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___85_6702  ->
                        match uu___85_6702 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____6703 -> false)))
              in
           let uu____6704 =
             let uu____6709 =
               let uu____6710 = FStar_Syntax_Subst.compress head1  in
               uu____6710.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____6709)  in
           (match uu____6704 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6719,uu____6720) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                term_as_mlexpr g t1
            | (uu____6736,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6738,FStar_Pervasives_Native.Some rc)) when
                is_total rc ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                term_as_mlexpr g t1
            | (uu____6759,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6761 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6761
                   in
                let tm =
                  let uu____6771 =
                    let uu____6776 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____6777 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6776 uu____6777  in
                  uu____6771 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____6786 ->
                let rec extract_app is_data uu____6839 uu____6840 restArgs =
                  match (uu____6839, uu____6840) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6930) ->
                           let mlargs =
                             FStar_All.pipe_right (FStar_List.rev mlargs_f)
                               (FStar_List.map FStar_Pervasives_Native.fst)
                              in
                           let app =
                             let uu____6965 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t1)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (mlhead, mlargs))
                                in
                             FStar_All.pipe_left
                               (maybe_eta_data_and_project_record g is_data
                                  t1) uu____6965
                              in
                           (app, f, t1)
                       | ((arg,uu____6969)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____7000 =
                             let uu____7005 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f'
                                in
                             (uu____7005, t2)  in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____7000 rest
                       | ((e0,uu____7017)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let expected_effect =
                             let uu____7050 =
                               (FStar_Options.lax ()) &&
                                 (FStar_TypeChecker_Util.short_circuit_head
                                    head1)
                                in
                             if uu____7050
                             then FStar_Extraction_ML_Syntax.E_IMPURE
                             else FStar_Extraction_ML_Syntax.E_PURE  in
                           let uu____7052 =
                             check_term_as_mlexpr g e0 expected_effect
                               tExpected
                              in
                           (match uu____7052 with
                            | (e01,tInferred) ->
                                let uu____7065 =
                                  let uu____7070 =
                                    FStar_Extraction_ML_Util.join_l r [f; f']
                                     in
                                  (uu____7070, t2)  in
                                extract_app is_data
                                  (mlhead, ((e01, expected_effect) ::
                                    mlargs_f)) uu____7065 rest)
                       | uu____7081 ->
                           let uu____7094 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1  in
                           (match uu____7094 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                (match t1 with
                                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                                     (FStar_Extraction_ML_Syntax.ml_unit,
                                       FStar_Extraction_ML_Syntax.E_PURE, t1)
                                 | uu____7116 ->
                                     err_ill_typed_application g top restArgs
                                       t1)))
                   in
                let extract_app_maybe_projector is_data mlhead uu____7164
                  args1 =
                  match uu____7164 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____7194)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____7278))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____7280,f',t3)) ->
                                 let uu____7317 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____7317 t3
                             | uu____7318 -> (args2, f1, t2)  in
                           let uu____7343 = remove_implicits args1 f t1  in
                           (match uu____7343 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____7399 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____7423 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____7431 ->
                      let uu____7432 =
                        let uu____7451 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____7451 with
                        | (FStar_Util.Inr (uu____7476,x1,x2,x3),q) ->
                            ((x1, x2, x3), q)
                        | uu____7517 -> failwith "FIXME Ty"  in
                      (match uu____7432 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____7581)::uu____7582 -> is_type g a
                             | uu____7601 -> false  in
                           let uu____7610 =
                             match vars with
                             | uu____7639::uu____7640 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____7651 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____7681 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____7681 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____7770  ->
                                               match uu____7770 with
                                               | (x,uu____7776) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____7793 ->
                                              let uu___89_7796 = e  in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___89_7796.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___89_7796.FStar_Extraction_ML_Syntax.loc)
                                              }
                                           in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____7800 ->
                                              let uu___90_7801 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___90_7801.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___90_7801.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____7802 ->
                                              let uu___90_7803 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___90_7803.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___90_7803.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____7805;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____7806;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___91_7812 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes
                                                        in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___91_7812.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___91_7812.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____7813 ->
                                              failwith
                                                "Impossible: Unexpected head term"
                                           in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____7610 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____7876 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____7876,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____7877 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____7886 ->
                      let uu____7887 =
                        let uu____7906 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____7906 with
                        | (FStar_Util.Inr (uu____7931,x1,x2,x3),q) ->
                            ((x1, x2, x3), q)
                        | uu____7972 -> failwith "FIXME Ty"  in
                      (match uu____7887 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____8036)::uu____8037 -> is_type g a
                             | uu____8056 -> false  in
                           let uu____8065 =
                             match vars with
                             | uu____8094::uu____8095 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____8106 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____8136 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____8136 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____8225  ->
                                               match uu____8225 with
                                               | (x,uu____8231) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____8248 ->
                                              let uu___89_8251 = e  in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___89_8251.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___89_8251.FStar_Extraction_ML_Syntax.loc)
                                              }
                                           in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____8255 ->
                                              let uu___90_8256 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___90_8256.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___90_8256.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____8257 ->
                                              let uu___90_8258 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___90_8258.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___90_8258.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____8260;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____8261;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___91_8267 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes
                                                        in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___91_8267.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___91_8267.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____8268 ->
                                              failwith
                                                "Impossible: Unexpected head term"
                                           in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____8065 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____8331 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____8331,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____8332 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____8341 ->
                      let uu____8342 = term_as_mlexpr g head2  in
                      (match uu____8342 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____8358 = is_type g t  in
                if uu____8358
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____8366 =
                     let uu____8367 = FStar_Syntax_Util.un_uinst head1  in
                     uu____8367.FStar_Syntax_Syntax.n  in
                   match uu____8366 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____8377 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____8377 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____8386 -> extract_app_with_instantiations ())
                   | uu____8389 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____8392),f) ->
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
           let uu____8459 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____8459 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____8490 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8504 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____8504
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____8516 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____8516  in
                   let lb1 =
                     let uu___92_8518 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___92_8518.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___92_8518.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___92_8518.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___92_8518.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___92_8518.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___92_8518.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____8490 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8549 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8549
                               in
                            let lbdef =
                              let uu____8557 = FStar_Options.ml_ish ()  in
                              if uu____8557
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.EraseUniverses;
                                  FStar_TypeChecker_Normalize.Inlining;
                                  FStar_TypeChecker_Normalize.Eager_unfolding;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.PureSubtermsWithinComputations;
                                  FStar_TypeChecker_Normalize.Primops] tcenv
                                  lb.FStar_Syntax_Syntax.lbdef
                               in
                            let uu___93_8561 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___93_8561.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___93_8561.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___93_8561.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___93_8561.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___93_8561.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___93_8561.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let maybe_generalize uu____8568 =
                  match uu____8568 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8570;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;
                      FStar_Syntax_Syntax.lbattrs = uu____8574;
                      FStar_Syntax_Syntax.lbpos = uu____8575;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t2 = FStar_Syntax_Subst.compress t1  in
                      let no_gen uu____8633 =
                        let expected_t = term_as_mlty g t2  in
                        (lbname_, f_e, (t2, ([], ([], expected_t))), false,
                          e)
                         in
                      let uu____8695 =
                        FStar_TypeChecker_Util.must_erase_for_extraction
                          g.FStar_Extraction_ML_UEnv.tcenv t2
                         in
                      if uu____8695
                      then
                        (lbname_, f_e,
                          (t2,
                            ([],
                              ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                          false, e)
                      else
                        (match t2.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                             let uu____8731 = FStar_List.hd bs  in
                             FStar_All.pipe_right uu____8731
                               (is_type_binder g)
                             ->
                             let uu____8744 =
                               FStar_Syntax_Subst.open_comp bs c  in
                             (match uu____8744 with
                              | (bs1,c1) ->
                                  let uu____8751 =
                                    let uu____8762 =
                                      FStar_Util.prefix_until
                                        (fun x  ->
                                           let uu____8798 =
                                             is_type_binder g x  in
                                           Prims.op_Negation uu____8798) bs1
                                       in
                                    match uu____8762 with
                                    | FStar_Pervasives_Native.None  ->
                                        (bs1,
                                          (FStar_Syntax_Util.comp_result c1))
                                    | FStar_Pervasives_Native.Some
                                        (bs2,b,rest) ->
                                        let uu____8894 =
                                          FStar_Syntax_Util.arrow (b :: rest)
                                            c1
                                           in
                                        (bs2, uu____8894)
                                     in
                                  (match uu____8751 with
                                   | (tbinders,tbody) ->
                                       let n_tbinders =
                                         FStar_List.length tbinders  in
                                       let e1 =
                                         let uu____8927 = normalize_abs e  in
                                         FStar_All.pipe_right uu____8927
                                           FStar_Syntax_Util.unmeta
                                          in
                                       (match e1.FStar_Syntax_Syntax.n with
                                        | FStar_Syntax_Syntax.Tm_abs
                                            (bs2,body,copt) ->
                                            let uu____8953 =
                                              FStar_Syntax_Subst.open_term
                                                bs2 body
                                               in
                                            (match uu____8953 with
                                             | (bs3,body1) ->
                                                 if
                                                   n_tbinders <=
                                                     (FStar_List.length bs3)
                                                 then
                                                   let uu____8970 =
                                                     FStar_Util.first_N
                                                       n_tbinders bs3
                                                      in
                                                   (match uu____8970 with
                                                    | (targs,rest_args) ->
                                                        let expected_source_ty
                                                          =
                                                          let s =
                                                            FStar_List.map2
                                                              (fun uu____9040
                                                                  ->
                                                                 fun
                                                                   uu____9041
                                                                    ->
                                                                   match 
                                                                    (uu____9040,
                                                                    uu____9041)
                                                                   with
                                                                   | 
                                                                   ((x,uu____9059),
                                                                    (y,uu____9061))
                                                                    ->
                                                                    let uu____9070
                                                                    =
                                                                    let uu____9077
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____9077)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9070)
                                                              tbinders targs
                                                             in
                                                          FStar_Syntax_Subst.subst
                                                            s tbody
                                                           in
                                                        let env =
                                                          FStar_List.fold_left
                                                            (fun env  ->
                                                               fun uu____9092
                                                                  ->
                                                                 match uu____9092
                                                                 with
                                                                 | (a,uu____9098)
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
                                                          let uu____9105 =
                                                            FStar_All.pipe_right
                                                              targs
                                                              (FStar_List.map
                                                                 (fun
                                                                    uu____9119
                                                                     ->
                                                                    match uu____9119
                                                                    with
                                                                    | 
                                                                    (x,uu____9125)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                             in
                                                          (uu____9105,
                                                            expected_t)
                                                           in
                                                        let add_unit =
                                                          match rest_args
                                                          with
                                                          | [] ->
                                                              (let uu____9133
                                                                 =
                                                                 is_fstar_value
                                                                   body1
                                                                  in
                                                               Prims.op_Negation
                                                                 uu____9133)
                                                                ||
                                                                (let uu____9135
                                                                   =
                                                                   FStar_Syntax_Util.is_pure_comp
                                                                    c1
                                                                    in
                                                                 Prims.op_Negation
                                                                   uu____9135)
                                                          | uu____9136 ->
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
                                            uu____9167 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9184  ->
                                                     match uu____9184 with
                                                     | (a,uu____9190) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9197 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9211  ->
                                                        match uu____9211 with
                                                        | (x,uu____9217) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9197, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9249  ->
                                                      match uu____9249 with
                                                      | (bv,uu____9255) ->
                                                          let uu____9256 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9256
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
                                            uu____9282 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9293  ->
                                                     match uu____9293 with
                                                     | (a,uu____9299) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9306 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9320  ->
                                                        match uu____9320 with
                                                        | (x,uu____9326) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9306, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9358  ->
                                                      match uu____9358 with
                                                      | (bv,uu____9364) ->
                                                          let uu____9365 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9365
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
                                            uu____9391 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9402  ->
                                                     match uu____9402 with
                                                     | (a,uu____9408) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9415 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9429  ->
                                                        match uu____9429 with
                                                        | (x,uu____9435) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9415, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9467  ->
                                                      match uu____9467 with
                                                      | (bv,uu____9473) ->
                                                          let uu____9474 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9474
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
                                        | uu____9500 ->
                                            err_value_restriction e1)))
                         | uu____9501 -> no_gen ())
                   in
                let check_lb env uu____9520 =
                  match uu____9520 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9559  ->
                               match uu____9559 with
                               | (a,uu____9565) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____9567 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____9567 with
                       | (e1,ty) ->
                           let uu____9578 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____9578 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____9590 -> []  in
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
                let uu____9638 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____9729  ->
                         match uu____9729 with
                         | (env,lbs4) ->
                             let uu____9854 = lb  in
                             (match uu____9854 with
                              | (lbname,uu____9902,(t1,(uu____9904,polytype)),add_unit,uu____9907)
                                  ->
                                  let uu____9920 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____9920 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, [])
                   in
                (match uu____9638 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____10151 = term_as_mlexpr env_body e'1  in
                     (match uu____10151 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____10168 =
                              let uu____10171 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____10171  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10168
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____10180 =
                            let uu____10181 =
                              let uu____10182 =
                                let uu____10183 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____10183)  in
                              mk_MLE_Let top_level uu____10182 e'2  in
                            let uu____10192 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10181 uu____10192
                             in
                          (uu____10180, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10231 = term_as_mlexpr g scrutinee  in
           (match uu____10231 with
            | (e,f_e,t_e) ->
                let uu____10247 = check_pats_for_ite pats  in
                (match uu____10247 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10308 = term_as_mlexpr g then_e1  in
                            (match uu____10308 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10324 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____10324 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10340 =
                                        let uu____10351 =
                                          type_leq g t_then t_else  in
                                        if uu____10351
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10369 =
                                             type_leq g t_else t_then  in
                                           if uu____10369
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____10340 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10413 =
                                             let uu____10414 =
                                               let uu____10415 =
                                                 let uu____10424 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____10425 =
                                                   let uu____10428 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10428
                                                    in
                                                 (e, uu____10424,
                                                   uu____10425)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10415
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10414
                                              in
                                           let uu____10431 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____10413, uu____10431,
                                             t_branch))))
                        | uu____10432 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10448 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____10543 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____10543 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____10587 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____10587 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____10645 =
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
                                                   let uu____10668 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____10668 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____10645 with
                                              | (when_opt1,f_when) ->
                                                  let uu____10717 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____10717 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____10751 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____10828 
                                                                 ->
                                                                 match uu____10828
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
                                                         uu____10751)))))
                               true)
                           in
                        match uu____10448 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____10993  ->
                                      let uu____10994 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____10995 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____10994 uu____10995);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____11020 =
                                   let uu____11029 =
                                     let uu____11046 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.delta_constant
                                         FStar_Pervasives_Native.None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____11046
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____11029
                                    in
                                 (match uu____11020 with
                                  | (uu____11089,fw,uu____11091,uu____11092)
                                      ->
                                      let uu____11093 =
                                        let uu____11094 =
                                          let uu____11095 =
                                            let uu____11102 =
                                              let uu____11105 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____11105]  in
                                            (fw, uu____11102)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11095
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____11094
                                         in
                                      (uu____11093,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____11108,uu____11109,(uu____11110,f_first,t_first))::rest
                                 ->
                                 let uu____11170 =
                                   FStar_List.fold_left
                                     (fun uu____11212  ->
                                        fun uu____11213  ->
                                          match (uu____11212, uu____11213)
                                          with
                                          | ((topt,f),(uu____11270,uu____11271,
                                                       (uu____11272,f_branch,t_branch)))
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
                                                    let uu____11328 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____11328
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11332 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____11332
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
                                 (match uu____11170 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11427  ->
                                                match uu____11427 with
                                                | (p,(wopt,uu____11456),
                                                   (b1,uu____11458,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11477 -> b1
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
                                      let uu____11482 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____11482, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11508 =
          let uu____11513 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11513  in
        match uu____11508 with
        | (uu____11538,fstar_disc_type) ->
            let wildcards =
              let uu____11547 =
                let uu____11548 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____11548.FStar_Syntax_Syntax.n  in
              match uu____11547 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11558) ->
                  let uu____11575 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___86_11609  ->
                            match uu___86_11609 with
                            | (uu____11616,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11617)) ->
                                true
                            | uu____11620 -> false))
                     in
                  FStar_All.pipe_right uu____11575
                    (FStar_List.map
                       (fun uu____11653  ->
                          let uu____11660 = fresh "_"  in
                          (uu____11660, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11661 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____11672 =
                let uu____11673 =
                  let uu____11684 =
                    let uu____11685 =
                      let uu____11686 =
                        let uu____11701 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____11704 =
                          let uu____11715 =
                            let uu____11724 =
                              let uu____11725 =
                                let uu____11732 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____11732,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____11725
                               in
                            let uu____11735 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____11724, FStar_Pervasives_Native.None,
                              uu____11735)
                             in
                          let uu____11738 =
                            let uu____11749 =
                              let uu____11758 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____11758)
                               in
                            [uu____11749]  in
                          uu____11715 :: uu____11738  in
                        (uu____11701, uu____11704)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11686  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11685
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11684)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11673  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11672
               in
            let uu____11813 =
              let uu____11814 =
                let uu____11817 =
                  let uu____11818 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____11818;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____11817]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____11814)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____11813
  