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
      | FStar_Syntax_Syntax.Tm_constant uu____521 -> false
      | FStar_Syntax_Syntax.Tm_name uu____522 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____523 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____530 -> false
      | FStar_Syntax_Syntax.Tm_type uu____531 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____532,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____550 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1
             in
          let uu____552 =
            let uu____553 = FStar_Syntax_Subst.compress t2  in
            uu____553.FStar_Syntax_Syntax.n  in
          (match uu____552 with
           | FStar_Syntax_Syntax.Tm_fvar uu____556 -> false
           | uu____557 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____558 ->
          let uu____573 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____573 with | (head1,uu____589) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____611) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____617) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____622,body,uu____624) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____645,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____663,branches) ->
          (match branches with
           | (uu____701,uu____702,e)::uu____704 -> is_arity env e
           | uu____751 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____779 ->
          let uu____804 =
            let uu____805 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____805  in
          failwith uu____804
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____806 =
            let uu____807 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____807  in
          failwith uu____806
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____809 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____809
      | FStar_Syntax_Syntax.Tm_constant uu____810 -> false
      | FStar_Syntax_Syntax.Tm_type uu____811 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____812 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____819 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar
          { FStar_Syntax_Syntax.ctx_uvar_head = uu____834;
            FStar_Syntax_Syntax.ctx_uvar_gamma = uu____835;
            FStar_Syntax_Syntax.ctx_uvar_binders = uu____836;
            FStar_Syntax_Syntax.ctx_uvar_typ = t2;
            FStar_Syntax_Syntax.ctx_uvar_reason = uu____838;
            FStar_Syntax_Syntax.ctx_uvar_should_check = uu____839;
            FStar_Syntax_Syntax.ctx_uvar_range = uu____840;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____861;
            FStar_Syntax_Syntax.index = uu____862;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____866;
            FStar_Syntax_Syntax.index = uu____867;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____872,uu____873) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____915) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____922) ->
          let uu____943 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____943 with | (uu____948,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____965 =
            let uu____970 =
              let uu____971 = FStar_Syntax_Syntax.mk_binder x  in [uu____971]
               in
            FStar_Syntax_Subst.open_term uu____970 body  in
          (match uu____965 with | (uu____984,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____986,lbs),body) ->
          let uu____1003 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____1003 with
           | (uu____1010,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____1016,branches) ->
          (match branches with
           | b::uu____1055 ->
               let uu____1100 = FStar_Syntax_Subst.open_branch b  in
               (match uu____1100 with
                | (uu____1101,uu____1102,e) -> is_type_aux env e)
           | uu____1120 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1137 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1145) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1151) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1186  ->
           let uu____1187 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1188 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1187
             uu____1188);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1194  ->
            if b
            then
              let uu____1195 = FStar_Syntax_Print.term_to_string t  in
              let uu____1196 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1195 uu____1196
            else
              (let uu____1198 = FStar_Syntax_Print.term_to_string t  in
               let uu____1199 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1198 uu____1199));
       b)
  
let is_type_binder :
  'Auu____1206 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1206) FStar_Pervasives_Native.tuple2 ->
        Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1230 =
      let uu____1231 = FStar_Syntax_Subst.compress t  in
      uu____1231.FStar_Syntax_Syntax.n  in
    match uu____1230 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1234;
          FStar_Syntax_Syntax.fv_delta = uu____1235;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1236;
          FStar_Syntax_Syntax.fv_delta = uu____1237;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1238);_}
        -> true
    | uu____1245 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1251 =
      let uu____1252 = FStar_Syntax_Subst.compress t  in
      uu____1252.FStar_Syntax_Syntax.n  in
    match uu____1251 with
    | FStar_Syntax_Syntax.Tm_constant uu____1255 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1256 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1257 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1258 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1297 = is_constructor head1  in
        if uu____1297
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1311  ->
                  match uu____1311 with
                  | (te,uu____1317) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1320) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1326,uu____1327) ->
        is_fstar_value t1
    | uu____1368 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1374 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1375 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1376 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1377 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1388,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1397,fields) ->
        FStar_Util.for_all
          (fun uu____1422  ->
             match uu____1422 with | (uu____1427,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1430) -> is_ml_value h
    | uu____1435 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1478 =
       let uu____1479 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____1479  in
     Prims.strcat x uu____1478)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1594 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1596 = FStar_Syntax_Util.is_fun e'  in
          if uu____1596
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1604 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1604 
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
      (let uu____1685 = FStar_List.hd l  in
       match uu____1685 with
       | (p1,w1,e1) ->
           let uu____1719 =
             let uu____1728 = FStar_List.tl l  in FStar_List.hd uu____1728
              in
           (match uu____1719 with
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
                 | uu____1802 -> def)))
  
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
      let uu____1839 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1839 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1859  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____1870 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____1884  ->
                    match uu____1884 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1870
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
      let uu____1910 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1910 with
      | (ts,r) ->
          let body r1 =
            let r2 =
              let uu____1930 = FStar_Extraction_ML_Util.udelta_unfold g r1
                 in
              match uu____1930 with
              | FStar_Pervasives_Native.None  -> r1
              | FStar_Pervasives_Native.Some r2 -> r2  in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top  ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu____1934 ->
                FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2))
             in
          if ts = []
          then body r
          else
            (let vs = FStar_List.map (fun uu____1942  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let uu____1950 =
               let uu____1951 =
                 let uu____1962 = body r  in (vs_ts, uu____1962)  in
               FStar_Extraction_ML_Syntax.MLE_Fun uu____1951  in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               uu____1950)
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____1979 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____1981 = FStar_Options.codegen ()  in
           uu____1981 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____1979 then e else eta_expand expect e
  
let maybe_coerce :
  'Auu____1999 .
    'Auu____1999 ->
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
            let uu____2026 =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
            match uu____2026 with
            | (true ,FStar_Pervasives_Native.Some e') -> e'
            | uu____2036 ->
                (FStar_Extraction_ML_UEnv.debug g
                   (fun uu____2048  ->
                      let uu____2049 =
                        FStar_Extraction_ML_Code.string_of_mlexpr
                          g.FStar_Extraction_ML_UEnv.currentModule e
                         in
                      let uu____2050 =
                        FStar_Extraction_ML_Code.string_of_mlty
                          g.FStar_Extraction_ML_UEnv.currentModule ty1
                         in
                      let uu____2051 =
                        FStar_Extraction_ML_Code.string_of_mlty
                          g.FStar_Extraction_ML_UEnv.currentModule expect
                         in
                      FStar_Util.print3
                        "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                        uu____2049 uu____2050 uu____2051);
                 (match ty1 with
                  | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                      default_value_for_ty g expect
                  | uu____2052 ->
                      let uu____2053 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty expect)
                          (FStar_Extraction_ML_Syntax.MLE_Coerce
                             (e, ty1, expect))
                         in
                      maybe_eta_expand expect uu____2053))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____2064 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____2064 with
      | FStar_Util.Inl (uu____2065,t) -> t
      | uu____2079 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
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
      let arg_as_mlty g1 uu____2124 =
        match uu____2124 with
        | (a,uu____2130) ->
            let uu____2131 = is_type g1 a  in
            if uu____2131
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____2149 =
          let uu____2150 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv  in
          Prims.op_Negation uu____2150  in
        if uu____2149
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu____2152 =
             let uu____2165 =
               FStar_TypeChecker_Env.lookup_lid
                 g1.FStar_Extraction_ML_UEnv.tcenv
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             match uu____2165 with
             | ((uu____2186,fvty),uu____2188) ->
                 let fvty1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.UnfoldUntil
                        FStar_Syntax_Syntax.Delta_constant]
                     g1.FStar_Extraction_ML_UEnv.tcenv fvty
                    in
                 FStar_Syntax_Util.arrow_formals fvty1
              in
           match uu____2152 with
           | (formals,uu____2195) ->
               let mlargs = FStar_List.map (arg_as_mlty g1) args  in
               let mlargs1 =
                 let n_args = FStar_List.length args  in
                 if (FStar_List.length formals) > n_args
                 then
                   let uu____2241 = FStar_Util.first_N n_args formals  in
                   match uu____2241 with
                   | (uu____2268,rest) ->
                       let uu____2294 =
                         FStar_List.map
                           (fun uu____2302  ->
                              FStar_Extraction_ML_UEnv.erasedContent) rest
                          in
                       FStar_List.append mlargs uu____2294
                 else mlargs  in
               let nm =
                 let uu____2309 =
                   FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                    in
                 match uu____2309 with
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
        | FStar_Syntax_Syntax.Tm_type uu____2327 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____2328 ->
            let uu____2329 =
              let uu____2330 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2330
               in
            failwith uu____2329
        | FStar_Syntax_Syntax.Tm_delayed uu____2331 ->
            let uu____2356 =
              let uu____2357 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2357
               in
            failwith uu____2356
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____2358 =
              let uu____2359 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2359
               in
            failwith uu____2358
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____2361 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____2361
        | FStar_Syntax_Syntax.Tm_constant uu____2362 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____2363 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____2370 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2372) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____2377;
               FStar_Syntax_Syntax.index = uu____2378;
               FStar_Syntax_Syntax.sort = t2;_},uu____2380)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2388) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2394,uu____2395) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____2462 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____2462 with
             | (bs1,c1) ->
                 let uu____2469 = binders_as_ml_binders env bs1  in
                 (match uu____2469 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let uu____2496 =
                          let uu____2503 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.tcenv eff
                             in
                          FStar_Util.must uu____2503  in
                        match uu____2496 with
                        | (ed,qualifiers) ->
                            let uu____2524 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____2524
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
                      let uu____2531 =
                        FStar_List.fold_right
                          (fun uu____2550  ->
                             fun uu____2551  ->
                               match (uu____2550, uu____2551) with
                               | ((uu____2572,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____2531 with | (uu____2584,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____2609 =
                let uu____2610 = FStar_Syntax_Util.un_uinst head1  in
                uu____2610.FStar_Syntax_Syntax.n  in
              match uu____2609 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____2637 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____2637
              | uu____2654 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2657) ->
            let uu____2678 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____2678 with
             | (bs1,ty1) ->
                 let uu____2685 = binders_as_ml_binders env bs1  in
                 (match uu____2685 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____2710 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____2723 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____2752 ->
            let uu____2759 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____2759 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____2763 -> false  in
      let uu____2764 =
        FStar_TypeChecker_Util.must_erase_for_extraction
          g.FStar_Extraction_ML_UEnv.tcenv t0
         in
      if uu____2764
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____2767 = is_top_ty mlt  in
         if uu____2767
         then
           let t =
             FStar_TypeChecker_Normalize.normalize
               ((FStar_TypeChecker_Normalize.UnfoldUntil
                   FStar_Syntax_Syntax.Delta_constant) :: basic_norm_steps)
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
      let uu____2782 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2831  ->
                fun b  ->
                  match uu____2831 with
                  | (ml_bs,env) ->
                      let uu____2871 = is_type_binder g b  in
                      if uu____2871
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____2889 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____2889, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____2903 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____2903 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2925 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____2925, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____2782 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____3008) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____3011,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____3015 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____3041 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____3042 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____3043 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____3052 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____3079 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____3079 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____3083 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____3110 -> p))
      | uu____3113 -> p
  
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
                       (fun uu____3205  ->
                          let uu____3206 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____3207 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____3206 uu____3207)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____3237 = FStar_Options.codegen ()  in
                uu____3237 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____3242 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3255 =
                        let uu____3256 =
                          let uu____3257 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____3257  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____3256
                         in
                      (uu____3255, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____3278 = term_as_mlexpr g source_term  in
                      (match uu____3278 with
                       | (mlterm,uu____3290,mlty) -> (mlterm, mlty))
                   in
                (match uu____3242 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____3310 =
                         let uu____3311 =
                           let uu____3318 =
                             let uu____3321 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____3321; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____3318)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____3311  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3310
                        in
                     let uu____3324 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____3324))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____3344 =
                  let uu____3353 =
                    let uu____3360 =
                      let uu____3361 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____3361  in
                    (uu____3360, [])  in
                  FStar_Pervasives_Native.Some uu____3353  in
                let uu____3370 = ok mlty  in (g, uu____3344, uu____3370)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3381 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3381 with
                 | (g1,x1) ->
                     let uu____3402 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3402))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3436 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3436 with
                 | (g1,x1) ->
                     let uu____3457 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3457))
            | FStar_Syntax_Syntax.Pat_dot_term uu____3489 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____3528 =
                  let uu____3537 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____3537 with
                  | FStar_Util.Inr
                      (uu____3546,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____3548;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____3549;_},ttys,uu____3551)
                      -> (n1, ttys)
                  | uu____3564 -> failwith "Expected a constructor"  in
                (match uu____3528 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____3598 = FStar_Util.first_N nTyVars pats  in
                     (match uu____3598 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____3727  ->
                                        match uu____3727 with
                                        | (p1,uu____3733) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____3734,t) ->
                                                 term_as_mlty g t
                                             | uu____3740 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____3744  ->
                                                       let uu____3745 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1
                                                          in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____3745);
                                                  FStar_Exn.raise
                                                    Un_extractable))))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              let uu____3747 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty
                                 in
                              FStar_Pervasives_Native.Some uu____3747
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____3776 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____3812  ->
                                   match uu____3812 with
                                   | (p1,imp1) ->
                                       let uu____3831 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____3831 with
                                        | (g2,p2,uu____3860) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____3776 with
                           | (g1,tyMLPats) ->
                               let uu____3921 =
                                 FStar_Util.fold_map
                                   (fun uu____3985  ->
                                      fun uu____3986  ->
                                        match (uu____3985, uu____3986) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____4079 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____4139 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____4079 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____4210 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____4210 with
                                                  | (g3,p2,uu____4251) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____3921 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____4369 =
                                      let uu____4380 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___62_4431  ->
                                                match uu___62_4431 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____4473 -> []))
                                         in
                                      FStar_All.pipe_right uu____4380
                                        FStar_List.split
                                       in
                                    (match uu____4369 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____4546 -> false  in
                                         let uu____4555 =
                                           let uu____4564 =
                                             let uu____4571 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____4574 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____4571, uu____4574)  in
                                           FStar_Pervasives_Native.Some
                                             uu____4564
                                            in
                                         (g2, uu____4555, pat_ty_compat))))))
  
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
            let uu____4701 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____4701 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____4758 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____4803 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____4803
             in
          let uu____4804 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____4804 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4954,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____4957 =
                  let uu____4968 =
                    let uu____4977 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____4977)  in
                  uu____4968 :: more_args  in
                eta_args uu____4957 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4990,uu____4991)
                -> ((FStar_List.rev more_args), t)
            | uu____5014 ->
                let uu____5015 =
                  let uu____5016 =
                    FStar_Extraction_ML_Code.string_of_mlexpr
                      g.FStar_Extraction_ML_UEnv.currentModule mlAppExpr
                     in
                  let uu____5017 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      g.FStar_Extraction_ML_UEnv.currentModule t
                     in
                  FStar_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)"
                    uu____5016 uu____5017
                   in
                failwith uu____5015
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____5049,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____5081 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____5103 = eta_args [] residualType  in
            match uu____5103 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____5156 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____5156
                 | uu____5157 ->
                     let uu____5168 = FStar_List.unzip eargs  in
                     (match uu____5168 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____5210 =
                                   let uu____5211 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____5211
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____5210
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____5220 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____5223,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5227;
                FStar_Extraction_ML_Syntax.loc = uu____5228;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5249 ->
                    let uu____5252 =
                      let uu____5259 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5259, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5252
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
                     FStar_Extraction_ML_Syntax.mlty = uu____5263;
                     FStar_Extraction_ML_Syntax.loc = uu____5264;_},uu____5265);
                FStar_Extraction_ML_Syntax.mlty = uu____5266;
                FStar_Extraction_ML_Syntax.loc = uu____5267;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5292 ->
                    let uu____5295 =
                      let uu____5302 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5302, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5295
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5306;
                FStar_Extraction_ML_Syntax.loc = uu____5307;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5315 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5315
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5319;
                FStar_Extraction_ML_Syntax.loc = uu____5320;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5322)) ->
              let uu____5335 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5335
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5339;
                     FStar_Extraction_ML_Syntax.loc = uu____5340;_},uu____5341);
                FStar_Extraction_ML_Syntax.mlty = uu____5342;
                FStar_Extraction_ML_Syntax.loc = uu____5343;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5355 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5355
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5359;
                     FStar_Extraction_ML_Syntax.loc = uu____5360;_},uu____5361);
                FStar_Extraction_ML_Syntax.mlty = uu____5362;
                FStar_Extraction_ML_Syntax.loc = uu____5363;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5365)) ->
              let uu____5382 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5382
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5388 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5388
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5392)) ->
              let uu____5401 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5401
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5405;
                FStar_Extraction_ML_Syntax.loc = uu____5406;_},uu____5407),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5414 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5414
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5418;
                FStar_Extraction_ML_Syntax.loc = uu____5419;_},uu____5420),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5421)) ->
              let uu____5434 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5434
          | uu____5437 -> mlAppExpr
  
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
        | uu____5467 -> (ml_e, tag)
  
type generalized_lb =
  (FStar_Syntax_Syntax.lbname,FStar_Extraction_ML_Syntax.e_tag,(FStar_Syntax_Syntax.typ,
                                                                 (FStar_Syntax_Syntax.binders,
                                                                   FStar_Extraction_ML_Syntax.mltyscheme)
                                                                   FStar_Pervasives_Native.tuple2)
                                                                 FStar_Pervasives_Native.tuple2,
    Prims.bool,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple5
[@@deriving show]
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
            (fun uu____5550  ->
               let uu____5551 = FStar_Syntax_Print.term_to_string e  in
               let uu____5552 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____5551
                 uu____5552);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5557) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____5558 ->
               let uu____5563 = term_as_mlexpr g e  in
               (match uu____5563 with
                | (ml_e,tag,t) ->
                    let uu____5577 = maybe_promote_effect ml_e tag t  in
                    (match uu____5577 with
                     | (ml_e1,tag1) ->
                         let uu____5588 =
                           FStar_Extraction_ML_Util.eff_leq tag1 f  in
                         if uu____5588
                         then
                           let uu____5593 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e1 t
                               ty
                              in
                           (uu____5593, ty)
                         else
                           (match (tag1, f, ty) with
                            | (FStar_Extraction_ML_Syntax.E_GHOST
                               ,FStar_Extraction_ML_Syntax.E_PURE
                               ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                                let uu____5599 =
                                  maybe_coerce e.FStar_Syntax_Syntax.pos g
                                    ml_e1 t ty
                                   in
                                (uu____5599, ty)
                            | uu____5600 ->
                                (err_unexpected_eff g e ty f tag1;
                                 (let uu____5608 =
                                    maybe_coerce e.FStar_Syntax_Syntax.pos g
                                      ml_e1 t ty
                                     in
                                  (uu____5608, ty)))))))

and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  =
  fun g  ->
    fun e  ->
      let uu____5611 = term_as_mlexpr' g e  in
      match uu____5611 with
      | (e1,f,t) ->
          let uu____5627 = maybe_promote_effect e1 f t  in
          (match uu____5627 with | (e2,f1) -> (e2, f1, t))

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
           let uu____5652 =
             let uu____5653 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____5654 = FStar_Syntax_Print.tag_of_term top  in
             let uu____5655 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5653 uu____5654 uu____5655
              in
           FStar_Util.print_string uu____5652);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5663 =
             let uu____5664 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5664
              in
           failwith uu____5663
       | FStar_Syntax_Syntax.Tm_delayed uu____5671 ->
           let uu____5696 =
             let uu____5697 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5697
              in
           failwith uu____5696
       | FStar_Syntax_Syntax.Tm_uvar uu____5704 ->
           let uu____5705 =
             let uu____5706 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5706
              in
           failwith uu____5705
       | FStar_Syntax_Syntax.Tm_bvar uu____5713 ->
           let uu____5714 =
             let uu____5715 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5715
              in
           failwith uu____5714
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____5723 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr g uu____5723
       | FStar_Syntax_Syntax.Tm_type uu____5724 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5725 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5732 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____5746;_})
           ->
           let uu____5761 =
             let uu____5770 =
               let uu____5787 =
                 FStar_Syntax_Syntax.lid_as_fv
                   FStar_Parser_Const.failwith_lid
                   FStar_Syntax_Syntax.Delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.lookup_fv g uu____5787  in
             FStar_All.pipe_left FStar_Util.right uu____5770  in
           (match uu____5761 with
            | (uu____5830,fw,uu____5832,uu____5833) ->
                let uu____5834 =
                  let uu____5835 =
                    let uu____5836 =
                      let uu____5843 =
                        let uu____5846 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Open quotation at runtime"))
                           in
                        [uu____5846]  in
                      (fw, uu____5843)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5836  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____5835
                   in
                (uu____5834, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____5865 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____5865 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____5873 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____5873 with
                 | FStar_Pervasives_Native.Some (false ,tm) ->
                     term_as_mlexpr g tm
                 | FStar_Pervasives_Native.Some (true ,tm) ->
                     let uu____5896 =
                       let uu____5905 =
                         let uu____5922 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.failwith_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         FStar_Extraction_ML_UEnv.lookup_fv g uu____5922  in
                       FStar_All.pipe_left FStar_Util.right uu____5905  in
                     (match uu____5896 with
                      | (uu____5965,fw,uu____5967,uu____5968) ->
                          let uu____5969 =
                            let uu____5970 =
                              let uu____5971 =
                                let uu____5978 =
                                  let uu____5981 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         FStar_Extraction_ML_Syntax.ml_string_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_String
                                            "Open quotation at runtime"))
                                     in
                                  [uu____5981]  in
                                (fw, uu____5978)  in
                              FStar_Extraction_ML_Syntax.MLE_App uu____5971
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____5970
                             in
                          (uu____5969, FStar_Extraction_ML_Syntax.E_PURE,
                            FStar_Extraction_ML_Syntax.ml_int_ty))
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____5989 =
                         FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                       FStar_Syntax_Embeddings.embed uu____5989
                         t.FStar_Syntax_Syntax.pos
                         (FStar_Reflection_Data.Tv_Var bv)
                        in
                     let t1 =
                       let uu____5995 =
                         let uu____6004 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____6004]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____5995
                        in
                     term_as_mlexpr g t1)
            | tv ->
                let tv1 =
                  let uu____6025 =
                    FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                  FStar_Syntax_Embeddings.embed uu____6025
                    t.FStar_Syntax_Syntax.pos tv
                   in
                let t1 =
                  let uu____6031 =
                    let uu____6040 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____6040]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____6031
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
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____6072)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____6102 =
                  let uu____6109 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m
                     in
                  FStar_Util.must uu____6109  in
                (match uu____6102 with
                 | (ed,qualifiers) ->
                     let uu____6136 =
                       let uu____6137 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                          in
                       FStar_All.pipe_right uu____6137 Prims.op_Negation  in
                     if uu____6136
                     then term_as_mlexpr g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____6153 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6155) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6161) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6167 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____6167 with
            | (uu____6180,ty,uu____6182) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____6184 =
                  let uu____6185 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____6185  in
                (uu____6184, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____6186 ->
           let uu____6187 = is_type g t  in
           if uu____6187
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6195 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____6195 with
              | (FStar_Util.Inl uu____6208,uu____6209) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____6230,x,mltys,uu____6233),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____6259 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____6259, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6260 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____6268 = is_type g t  in
           if uu____6268
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6276 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____6276 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____6285) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | FStar_Pervasives_Native.Some (FStar_Util.Inr
                  (uu____6302,x,mltys,uu____6305)) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____6326 =
                         maybe_eta_data_and_project_record g
                           fv.FStar_Syntax_Syntax.fv_qual t1 x
                          in
                       (uu____6326, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6327 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____6357 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____6357 with
            | (bs1,body1) ->
                let uu____6370 = binders_as_ml_binders g bs1  in
                (match uu____6370 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____6403 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c
                              in
                           if uu____6403
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____6408  ->
                                 let uu____6409 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____6409);
                            body1)
                        in
                     let uu____6410 = term_as_mlexpr env body2  in
                     (match uu____6410 with
                      | (ml_body,f,t1) ->
                          let uu____6426 =
                            FStar_List.fold_right
                              (fun uu____6445  ->
                                 fun uu____6446  ->
                                   match (uu____6445, uu____6446) with
                                   | ((uu____6467,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____6426 with
                           | (f1,tfun) ->
                               let uu____6487 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____6487, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6494;
              FStar_Syntax_Syntax.vars = uu____6495;_},(a1,uu____6497)::[])
           ->
           let ty =
             let uu____6527 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____6527  in
           let uu____6528 =
             let uu____6529 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____6529
              in
           (uu____6528, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6530;
              FStar_Syntax_Syntax.vars = uu____6531;_},(t1,uu____6533)::
            (r,uu____6535)::[])
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6574);
              FStar_Syntax_Syntax.pos = uu____6575;
              FStar_Syntax_Syntax.vars = uu____6576;_},uu____6577)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___63_6635  ->
                        match uu___63_6635 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____6636 -> false)))
              in
           let uu____6637 =
             let uu____6642 =
               let uu____6643 = FStar_Syntax_Subst.compress head1  in
               uu____6643.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____6642)  in
           (match uu____6637 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6652,uu____6653) ->
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
            | (uu____6655,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6657,FStar_Pervasives_Native.Some rc)) when
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
            | (uu____6678,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6680 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6680
                   in
                let tm =
                  let uu____6690 =
                    let uu____6695 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____6696 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6695 uu____6696  in
                  uu____6690 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr g tm
            | uu____6705 ->
                let rec extract_app is_data uu____6760 uu____6761 restArgs =
                  match (uu____6760, uu____6761) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6855) ->
                           let mlargs =
                             FStar_All.pipe_right (FStar_List.rev mlargs_f)
                               (FStar_List.map FStar_Pervasives_Native.fst)
                              in
                           let app =
                             let uu____6894 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t1)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (mlhead, mlargs))
                                in
                             FStar_All.pipe_left
                               (maybe_eta_data_and_project_record g is_data
                                  t1) uu____6894
                              in
                           (app, f, t1)
                       | ((arg,uu____6898)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____6939 =
                             let uu____6944 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f'
                                in
                             (uu____6944, t2)  in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____6939 rest
                       | ((e0,uu____6956)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let expected_effect =
                             let uu____6999 =
                               (FStar_Options.lax ()) &&
                                 (FStar_TypeChecker_Util.short_circuit_head
                                    head1)
                                in
                             if uu____6999
                             then FStar_Extraction_ML_Syntax.E_IMPURE
                             else FStar_Extraction_ML_Syntax.E_PURE  in
                           let uu____7001 =
                             check_term_as_mlexpr g e0 expected_effect
                               tExpected
                              in
                           (match uu____7001 with
                            | (e01,tInferred) ->
                                let uu____7014 =
                                  let uu____7019 =
                                    FStar_Extraction_ML_Util.join_l r [f; f']
                                     in
                                  (uu____7019, t2)  in
                                extract_app is_data
                                  (mlhead, ((e01, expected_effect) ::
                                    mlargs_f)) uu____7014 rest)
                       | uu____7030 ->
                           let uu____7045 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1  in
                           (match uu____7045 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                (match t1 with
                                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                                     (FStar_Extraction_ML_Syntax.ml_unit,
                                       FStar_Extraction_ML_Syntax.E_PURE, t1)
                                 | uu____7067 ->
                                     err_ill_typed_application g top restArgs
                                       t1)))
                   in
                let extract_app_maybe_projector is_data mlhead uu____7117
                  args1 =
                  match uu____7117 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____7149)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____7233))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____7235,f',t3)) ->
                                 let uu____7272 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____7272 t3
                             | uu____7273 -> (args2, f1, t2)  in
                           let uu____7298 = remove_implicits args1 f t1  in
                           (match uu____7298 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____7354 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____7378 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____7386 ->
                      let uu____7387 =
                        let uu____7406 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____7406 with
                        | (FStar_Util.Inr (uu____7431,x1,x2,x3),q) ->
                            ((x1, x2, x3), q)
                        | uu____7460 -> failwith "FIXME Ty"  in
                      (match uu____7387 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____7524)::uu____7525 -> is_type g a
                             | uu____7544 -> false  in
                           let uu____7553 =
                             match vars with
                             | uu____7586::uu____7587 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____7598 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____7630 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____7630 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____7721  ->
                                               match uu____7721 with
                                               | (x,uu____7727) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____7744 ->
                                              let uu___67_7747 = e  in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___67_7747.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___67_7747.FStar_Extraction_ML_Syntax.loc)
                                              }
                                           in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____7751 ->
                                              let uu___68_7752 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___68_7752.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___68_7752.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____7753 ->
                                              let uu___68_7754 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___68_7754.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___68_7754.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____7756;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____7757;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___69_7763 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes
                                                        in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___69_7763.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___69_7763.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____7764 ->
                                              failwith
                                                "Impossible: Unexpected head term"
                                           in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____7553 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____7835 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____7835,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____7836 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____7847 ->
                      let uu____7848 =
                        let uu____7867 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____7867 with
                        | (FStar_Util.Inr (uu____7892,x1,x2,x3),q) ->
                            ((x1, x2, x3), q)
                        | uu____7921 -> failwith "FIXME Ty"  in
                      (match uu____7848 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____7985)::uu____7986 -> is_type g a
                             | uu____8005 -> false  in
                           let uu____8014 =
                             match vars with
                             | uu____8047::uu____8048 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____8059 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____8091 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____8091 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____8182  ->
                                               match uu____8182 with
                                               | (x,uu____8188) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____8205 ->
                                              let uu___67_8208 = e  in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___67_8208.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___67_8208.FStar_Extraction_ML_Syntax.loc)
                                              }
                                           in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____8212 ->
                                              let uu___68_8213 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___68_8213.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___68_8213.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____8214 ->
                                              let uu___68_8215 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___68_8215.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___68_8215.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____8217;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____8218;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___69_8224 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes
                                                        in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___69_8224.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___69_8224.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____8225 ->
                                              failwith
                                                "Impossible: Unexpected head term"
                                           in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____8014 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____8296 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____8296,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____8297 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____8308 ->
                      let uu____8309 = term_as_mlexpr g head2  in
                      (match uu____8309 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____8325 = is_type g t  in
                if uu____8325
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____8333 =
                     let uu____8334 = FStar_Syntax_Util.un_uinst head1  in
                     uu____8334.FStar_Syntax_Syntax.n  in
                   match uu____8333 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____8344 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____8344 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____8353 -> extract_app_with_instantiations ())
                   | uu____8356 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____8359),f) ->
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
           let uu____8426 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____8426 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____8457 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8471 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____8471
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____8485 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____8485  in
                   let lb1 =
                     let uu___70_8487 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___70_8487.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___70_8487.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___70_8487.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___70_8487.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___70_8487.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___70_8487.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____8457 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8518 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8518
                               in
                            let lbdef =
                              let uu____8526 = FStar_Options.ml_ish ()  in
                              if uu____8526
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
                            let uu___71_8530 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___71_8530.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___71_8530.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___71_8530.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___71_8530.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___71_8530.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___71_8530.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let maybe_generalize uu____8537 =
                  match uu____8537 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8539;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;
                      FStar_Syntax_Syntax.lbattrs = uu____8543;
                      FStar_Syntax_Syntax.lbpos = uu____8544;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t2 = FStar_Syntax_Subst.compress t1  in
                      let no_gen uu____8602 =
                        let expected_t = term_as_mlty g t2  in
                        (lbname_, f_e, (t2, ([], ([], expected_t))), false,
                          e)
                         in
                      let uu____8664 =
                        FStar_TypeChecker_Util.must_erase_for_extraction
                          g.FStar_Extraction_ML_UEnv.tcenv t2
                         in
                      if uu____8664
                      then
                        (lbname_, f_e,
                          (t2,
                            ([],
                              ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                          false, e)
                      else
                        (match t2.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                             let uu____8700 = FStar_List.hd bs  in
                             FStar_All.pipe_right uu____8700
                               (is_type_binder g)
                             ->
                             let uu____8713 =
                               FStar_Syntax_Subst.open_comp bs c  in
                             (match uu____8713 with
                              | (bs1,c1) ->
                                  let uu____8720 =
                                    let uu____8727 =
                                      FStar_Util.prefix_until
                                        (fun x  ->
                                           let uu____8763 =
                                             is_type_binder g x  in
                                           Prims.op_Negation uu____8763) bs1
                                       in
                                    match uu____8727 with
                                    | FStar_Pervasives_Native.None  ->
                                        (bs1,
                                          (FStar_Syntax_Util.comp_result c1))
                                    | FStar_Pervasives_Native.Some
                                        (bs2,b,rest) ->
                                        let uu____8851 =
                                          FStar_Syntax_Util.arrow (b :: rest)
                                            c1
                                           in
                                        (bs2, uu____8851)
                                     in
                                  (match uu____8720 with
                                   | (tbinders,tbody) ->
                                       let n_tbinders =
                                         FStar_List.length tbinders  in
                                       let e1 =
                                         let uu____8880 = normalize_abs e  in
                                         FStar_All.pipe_right uu____8880
                                           FStar_Syntax_Util.unmeta
                                          in
                                       (match e1.FStar_Syntax_Syntax.n with
                                        | FStar_Syntax_Syntax.Tm_abs
                                            (bs2,body,copt) ->
                                            let uu____8906 =
                                              FStar_Syntax_Subst.open_term
                                                bs2 body
                                               in
                                            (match uu____8906 with
                                             | (bs3,body1) ->
                                                 if
                                                   n_tbinders <=
                                                     (FStar_List.length bs3)
                                                 then
                                                   let uu____8923 =
                                                     FStar_Util.first_N
                                                       n_tbinders bs3
                                                      in
                                                   (match uu____8923 with
                                                    | (targs,rest_args) ->
                                                        let expected_source_ty
                                                          =
                                                          let s =
                                                            FStar_List.map2
                                                              (fun uu____8993
                                                                  ->
                                                                 fun
                                                                   uu____8994
                                                                    ->
                                                                   match 
                                                                    (uu____8993,
                                                                    uu____8994)
                                                                   with
                                                                   | 
                                                                   ((x,uu____9012),
                                                                    (y,uu____9014))
                                                                    ->
                                                                    let uu____9023
                                                                    =
                                                                    let uu____9030
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____9030)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9023)
                                                              tbinders targs
                                                             in
                                                          FStar_Syntax_Subst.subst
                                                            s tbody
                                                           in
                                                        let env =
                                                          FStar_List.fold_left
                                                            (fun env  ->
                                                               fun uu____9045
                                                                  ->
                                                                 match uu____9045
                                                                 with
                                                                 | (a,uu____9051)
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
                                                          let uu____9058 =
                                                            FStar_All.pipe_right
                                                              targs
                                                              (FStar_List.map
                                                                 (fun
                                                                    uu____9072
                                                                     ->
                                                                    match uu____9072
                                                                    with
                                                                    | 
                                                                    (x,uu____9078)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                             in
                                                          (uu____9058,
                                                            expected_t)
                                                           in
                                                        let add_unit =
                                                          match rest_args
                                                          with
                                                          | [] ->
                                                              (let uu____9086
                                                                 =
                                                                 is_fstar_value
                                                                   body1
                                                                  in
                                                               Prims.op_Negation
                                                                 uu____9086)
                                                                ||
                                                                (let uu____9088
                                                                   =
                                                                   FStar_Syntax_Util.is_pure_comp
                                                                    c1
                                                                    in
                                                                 Prims.op_Negation
                                                                   uu____9088)
                                                          | uu____9089 ->
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
                                            uu____9120 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9137  ->
                                                     match uu____9137 with
                                                     | (a,uu____9143) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9150 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9164  ->
                                                        match uu____9164 with
                                                        | (x,uu____9170) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9150, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9202  ->
                                                      match uu____9202 with
                                                      | (bv,uu____9208) ->
                                                          let uu____9209 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9209
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
                                            uu____9235 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9246  ->
                                                     match uu____9246 with
                                                     | (a,uu____9252) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9259 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9273  ->
                                                        match uu____9273 with
                                                        | (x,uu____9279) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9259, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9311  ->
                                                      match uu____9311 with
                                                      | (bv,uu____9317) ->
                                                          let uu____9318 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9318
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
                                            uu____9344 ->
                                            let env =
                                              FStar_List.fold_left
                                                (fun env  ->
                                                   fun uu____9355  ->
                                                     match uu____9355 with
                                                     | (a,uu____9361) ->
                                                         FStar_Extraction_ML_UEnv.extend_ty
                                                           env a
                                                           FStar_Pervasives_Native.None)
                                                g tbinders
                                               in
                                            let expected_t =
                                              term_as_mlty env tbody  in
                                            let polytype =
                                              let uu____9368 =
                                                FStar_All.pipe_right tbinders
                                                  (FStar_List.map
                                                     (fun uu____9382  ->
                                                        match uu____9382 with
                                                        | (x,uu____9388) ->
                                                            FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                              x))
                                                 in
                                              (uu____9368, expected_t)  in
                                            let args =
                                              FStar_All.pipe_right tbinders
                                                (FStar_List.map
                                                   (fun uu____9420  ->
                                                      match uu____9420 with
                                                      | (bv,uu____9426) ->
                                                          let uu____9427 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              bv
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9427
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
                                        | uu____9453 ->
                                            err_value_restriction e1)))
                         | uu____9454 -> no_gen ())
                   in
                let check_lb env uu____9473 =
                  match uu____9473 with
                  | (nm,(_lbname,f,(_t,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9512  ->
                               match uu____9512 with
                               | (a,uu____9518) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____9520 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____9520 with
                       | (e1,ty) ->
                           let uu____9531 =
                             maybe_promote_effect e1 f expected_t  in
                           (match uu____9531 with
                            | (e2,f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_GHOST
                                     ,FStar_Extraction_ML_Syntax.MLTY_Erased
                                     ) -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu____9543 -> []  in
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
                let uu____9591 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____9682  ->
                         match uu____9682 with
                         | (env,lbs4) ->
                             let uu____9807 = lb  in
                             (match uu____9807 with
                              | (lbname,uu____9855,(t1,(uu____9857,polytype)),add_unit,uu____9860)
                                  ->
                                  let uu____9873 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____9873 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, [])
                   in
                (match uu____9591 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____10104 = term_as_mlexpr env_body e'1  in
                     (match uu____10104 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____10121 =
                              let uu____10124 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____10124  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10121
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____10133 =
                            let uu____10134 =
                              let uu____10135 =
                                let uu____10136 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____10136)  in
                              mk_MLE_Let top_level uu____10135 e'2  in
                            let uu____10145 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10134 uu____10145
                             in
                          (uu____10133, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10184 = term_as_mlexpr g scrutinee  in
           (match uu____10184 with
            | (e,f_e,t_e) ->
                let uu____10200 = check_pats_for_ite pats  in
                (match uu____10200 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10261 = term_as_mlexpr g then_e1  in
                            (match uu____10261 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10277 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____10277 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10293 =
                                        let uu____10304 =
                                          type_leq g t_then t_else  in
                                        if uu____10304
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10322 =
                                             type_leq g t_else t_then  in
                                           if uu____10322
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____10293 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10366 =
                                             let uu____10367 =
                                               let uu____10368 =
                                                 let uu____10377 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____10378 =
                                                   let uu____10381 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10381
                                                    in
                                                 (e, uu____10377,
                                                   uu____10378)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10368
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10367
                                              in
                                           let uu____10384 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____10366, uu____10384,
                                             t_branch))))
                        | uu____10385 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10401 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____10496 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____10496 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____10540 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____10540 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____10598 =
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
                                                   let uu____10621 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____10621 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____10598 with
                                              | (when_opt1,f_when) ->
                                                  let uu____10670 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____10670 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____10704 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____10781 
                                                                 ->
                                                                 match uu____10781
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
                                                         uu____10704)))))
                               true)
                           in
                        match uu____10401 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____10946  ->
                                      let uu____10947 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____10948 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____10947 uu____10948);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____10973 =
                                   let uu____10982 =
                                     let uu____10999 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____10999
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____10982
                                    in
                                 (match uu____10973 with
                                  | (uu____11042,fw,uu____11044,uu____11045)
                                      ->
                                      let uu____11046 =
                                        let uu____11047 =
                                          let uu____11048 =
                                            let uu____11055 =
                                              let uu____11058 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____11058]  in
                                            (fw, uu____11055)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11048
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____11047
                                         in
                                      (uu____11046,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____11061,uu____11062,(uu____11063,f_first,t_first))::rest
                                 ->
                                 let uu____11123 =
                                   FStar_List.fold_left
                                     (fun uu____11165  ->
                                        fun uu____11166  ->
                                          match (uu____11165, uu____11166)
                                          with
                                          | ((topt,f),(uu____11223,uu____11224,
                                                       (uu____11225,f_branch,t_branch)))
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
                                                    let uu____11281 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____11281
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11285 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____11285
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
                                 (match uu____11123 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11380  ->
                                                match uu____11380 with
                                                | (p,(wopt,uu____11409),
                                                   (b1,uu____11411,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11430 -> b1
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
                                      let uu____11435 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____11435, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11461 =
          let uu____11466 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11466  in
        match uu____11461 with
        | (uu____11491,fstar_disc_type) ->
            let wildcards =
              let uu____11500 =
                let uu____11501 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____11501.FStar_Syntax_Syntax.n  in
              match uu____11500 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11511) ->
                  let uu____11528 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___64_11562  ->
                            match uu___64_11562 with
                            | (uu____11569,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11570)) ->
                                true
                            | uu____11573 -> false))
                     in
                  FStar_All.pipe_right uu____11528
                    (FStar_List.map
                       (fun uu____11606  ->
                          let uu____11613 = fresh "_"  in
                          (uu____11613, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11614 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____11625 =
                let uu____11626 =
                  let uu____11637 =
                    let uu____11638 =
                      let uu____11639 =
                        let uu____11654 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____11657 =
                          let uu____11668 =
                            let uu____11677 =
                              let uu____11678 =
                                let uu____11685 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____11685,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____11678
                               in
                            let uu____11688 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____11677, FStar_Pervasives_Native.None,
                              uu____11688)
                             in
                          let uu____11691 =
                            let uu____11702 =
                              let uu____11711 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____11711)
                               in
                            [uu____11702]  in
                          uu____11668 :: uu____11691  in
                        (uu____11654, uu____11657)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11639  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11638
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11637)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11626  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11625
               in
            let uu____11766 =
              let uu____11767 =
                let uu____11770 =
                  let uu____11771 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____11771;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____11770]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____11767)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____11766
  