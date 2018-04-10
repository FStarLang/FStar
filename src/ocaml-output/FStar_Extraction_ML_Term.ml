open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Un_extractable  -> true | uu____4 -> false
  
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
  
let (erasableType :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t  ->
      FStar_Extraction_ML_Util.erasableType
        (FStar_Extraction_ML_Util.udelta_unfold g) t
  
let (eraseTypeDeep :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun t  ->
      FStar_Extraction_ML_Util.eraseTypeDeep
        (FStar_Extraction_ML_Util.udelta_unfold g) t
  
let record_fields :
  'Auu____50 .
    FStar_Ident.ident Prims.list ->
      'Auu____50 Prims.list ->
        (Prims.string,'Auu____50) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2 (fun f  -> fun e  -> ((f.FStar_Ident.idText), e)) fs vs
  
let fail :
  'Auu____84 .
    FStar_Range.range ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2 ->
        'Auu____84
  = fun r  -> fun err  -> FStar_Errors.raise_error err r 
let err_uninst :
  'Auu____106 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (Prims.string Prims.list,FStar_Extraction_ML_Syntax.mlty)
          FStar_Pervasives_Native.tuple2 ->
          FStar_Syntax_Syntax.term -> 'Auu____106
  =
  fun env  ->
    fun t  ->
      fun uu____127  ->
        fun app  ->
          match uu____127 with
          | (vars,ty) ->
              let uu____141 =
                let uu____146 =
                  let uu____147 = FStar_Syntax_Print.term_to_string t  in
                  let uu____148 =
                    FStar_All.pipe_right vars (FStar_String.concat ", ")  in
                  let uu____151 =
                    FStar_Extraction_ML_Code.string_of_mlty
                      env.FStar_Extraction_ML_UEnv.currentModule ty
                     in
                  let uu____152 = FStar_Syntax_Print.term_to_string app  in
                  FStar_Util.format4
                    "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                    uu____147 uu____148 uu____151 uu____152
                   in
                (FStar_Errors.Fatal_Uninstantiated, uu____146)  in
              fail t.FStar_Syntax_Syntax.pos uu____141
  
let err_ill_typed_application :
  'Auu____159 'Auu____160 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,'Auu____159) FStar_Pervasives_Native.tuple2
          Prims.list -> FStar_Extraction_ML_Syntax.mlty -> 'Auu____160
  =
  fun env  ->
    fun t  ->
      fun args  ->
        fun ty  ->
          let uu____189 =
            let uu____194 =
              let uu____195 = FStar_Syntax_Print.term_to_string t  in
              let uu____196 =
                let uu____197 =
                  FStar_All.pipe_right args
                    (FStar_List.map
                       (fun uu____215  ->
                          match uu____215 with
                          | (x,uu____221) ->
                              FStar_Syntax_Print.term_to_string x))
                   in
                FStar_All.pipe_right uu____197 (FStar_String.concat " ")  in
              let uu____224 =
                FStar_Extraction_ML_Code.string_of_mlty
                  env.FStar_Extraction_ML_UEnv.currentModule ty
                 in
              FStar_Util.format3
                "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
                uu____195 uu____196 uu____224
               in
            (FStar_Errors.Fatal_IllTyped, uu____194)  in
          fail t.FStar_Syntax_Syntax.pos uu____189
  
let err_value_restriction :
  'Auu____227 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'Auu____227
  =
  fun t  ->
    let uu____236 =
      let uu____241 =
        let uu____242 = FStar_Syntax_Print.tag_of_term t  in
        let uu____243 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu____242 uu____243
         in
      (FStar_Errors.Fatal_ValueRestriction, uu____241)  in
    fail t.FStar_Syntax_Syntax.pos uu____236
  
let (err_unexpected_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.e_tag ->
          FStar_Extraction_ML_Syntax.e_tag -> Prims.unit)
  =
  fun env  ->
    fun t  ->
      fun ty  ->
        fun f0  ->
          fun f1  ->
            let uu____263 =
              let uu____268 =
                let uu____269 = FStar_Syntax_Print.term_to_string t  in
                let uu____270 =
                  FStar_Extraction_ML_Code.string_of_mlty
                    env.FStar_Extraction_ML_UEnv.currentModule ty
                   in
                let uu____271 = FStar_Extraction_ML_Util.eff_to_string f0  in
                let uu____272 = FStar_Extraction_ML_Util.eff_to_string f1  in
                FStar_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu____269 uu____270 uu____271 uu____272
                 in
              (FStar_Errors.Warning_ExtractionUnexpectedEffect, uu____268)
               in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____263
  
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  let rec delta_norm_eff g l =
    let uu____287 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
    match uu____287 with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None  ->
        let res =
          let uu____292 =
            FStar_TypeChecker_Env.lookup_effect_abbrev
              g.FStar_Extraction_ML_UEnv.tcenv [FStar_Syntax_Syntax.U_zero] l
             in
          match uu____292 with
          | FStar_Pervasives_Native.None  -> l
          | FStar_Pervasives_Native.Some (uu____303,c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c)
           in
        (FStar_Util.smap_add cache l.FStar_Ident.str res; res)
     in
  fun g  ->
    fun l  ->
      let l1 = delta_norm_eff g l  in
      let uu____313 =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid  in
      if uu____313
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu____315 =
           FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid  in
         if uu____315
         then FStar_Extraction_ML_Syntax.E_GHOST
         else
           (let ed_opt =
              FStar_TypeChecker_Env.effect_decl_opt
                g.FStar_Extraction_ML_UEnv.tcenv l1
               in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                let uu____338 =
                  FStar_All.pipe_right qualifiers
                    (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                   in
                if uu____338
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None  ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
  
let rec (is_arity :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let uu____355 =
        let uu____356 = FStar_Syntax_Subst.compress t1  in
        uu____356.FStar_Syntax_Syntax.n  in
      match uu____355 with
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____359 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_ascribed uu____384 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_meta uu____411 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____419 = FStar_Syntax_Util.unfold_lazy i  in
          is_arity env uu____419
      | FStar_Syntax_Syntax.Tm_uvar uu____420 -> false
      | FStar_Syntax_Syntax.Tm_constant uu____437 -> false
      | FStar_Syntax_Syntax.Tm_name uu____438 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu____439 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu____446 -> false
      | FStar_Syntax_Syntax.Tm_type uu____447 -> true
      | FStar_Syntax_Syntax.Tm_arrow (uu____448,c) ->
          is_arity env (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar uu____466 ->
          let t2 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant]
              env.FStar_Extraction_ML_UEnv.tcenv t1
             in
          let uu____468 =
            let uu____469 = FStar_Syntax_Subst.compress t2  in
            uu____469.FStar_Syntax_Syntax.n  in
          (match uu____468 with
           | FStar_Syntax_Syntax.Tm_fvar uu____472 -> false
           | uu____473 -> is_arity env t2)
      | FStar_Syntax_Syntax.Tm_app uu____474 ->
          let uu____489 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____489 with | (head1,uu____505) -> is_arity env head1)
      | FStar_Syntax_Syntax.Tm_uinst (head1,uu____527) -> is_arity env head1
      | FStar_Syntax_Syntax.Tm_refine (x,uu____533) ->
          is_arity env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs (uu____538,body,uu____540) ->
          is_arity env body
      | FStar_Syntax_Syntax.Tm_let (uu____561,body) -> is_arity env body
      | FStar_Syntax_Syntax.Tm_match (uu____579,branches) ->
          (match branches with
           | (uu____617,uu____618,e)::uu____620 -> is_arity env e
           | uu____667 -> false)
  
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____691 ->
          let uu____716 =
            let uu____717 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____717  in
          failwith uu____716
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____718 =
            let uu____719 = FStar_Syntax_Print.tag_of_term t1  in
            FStar_Util.format1 "Impossible: %s" uu____719  in
          failwith uu____718
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____721 = FStar_Syntax_Util.unfold_lazy i  in
          is_type_aux env uu____721
      | FStar_Syntax_Syntax.Tm_constant uu____722 -> false
      | FStar_Syntax_Syntax.Tm_type uu____723 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____724 -> true
      | FStar_Syntax_Syntax.Tm_arrow uu____731 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.failwith_lid ->
          false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar (uu____746,t2) -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu____772;
            FStar_Syntax_Syntax.index = uu____773;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name
          { FStar_Syntax_Syntax.ppname = uu____777;
            FStar_Syntax_Syntax.index = uu____778;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____783,uu____784) ->
          is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____826) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____833) ->
          let uu____854 = FStar_Syntax_Subst.open_term bs body  in
          (match uu____854 with | (uu____859,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
          let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
          let uu____876 =
            let uu____881 =
              let uu____882 = FStar_Syntax_Syntax.mk_binder x  in [uu____882]
               in
            FStar_Syntax_Subst.open_term uu____881 body  in
          (match uu____876 with | (uu____883,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_let ((uu____885,lbs),body) ->
          let uu____902 = FStar_Syntax_Subst.open_let_rec lbs body  in
          (match uu____902 with | (uu____909,body1) -> is_type_aux env body1)
      | FStar_Syntax_Syntax.Tm_match (uu____915,branches) ->
          (match branches with
           | b::uu____954 ->
               let uu____999 = FStar_Syntax_Subst.open_branch b  in
               (match uu____999 with
                | (uu____1000,uu____1001,e) -> is_type_aux env e)
           | uu____1019 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu____1036 -> false
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____1044) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app (head1,uu____1050) ->
          is_type_aux env head1
  
let (is_type :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu____1081  ->
           let uu____1082 = FStar_Syntax_Print.tag_of_term t  in
           let uu____1083 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2 "checking is_type (%s) %s\n" uu____1082
             uu____1083);
      (let b = is_type_aux env t  in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu____1089  ->
            if b
            then
              let uu____1090 = FStar_Syntax_Print.term_to_string t  in
              let uu____1091 = FStar_Syntax_Print.tag_of_term t  in
              FStar_Util.print2 "is_type %s (%s)\n" uu____1090 uu____1091
            else
              (let uu____1093 = FStar_Syntax_Print.term_to_string t  in
               let uu____1094 = FStar_Syntax_Print.tag_of_term t  in
               FStar_Util.print2 "not a type %s (%s)\n" uu____1093 uu____1094));
       b)
  
let is_type_binder :
  'Auu____1098 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____1098) FStar_Pervasives_Native.tuple2 ->
        Prims.bool
  =
  fun env  ->
    fun x  ->
      is_arity env (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
  
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1118 =
      let uu____1119 = FStar_Syntax_Subst.compress t  in
      uu____1119.FStar_Syntax_Syntax.n  in
    match uu____1118 with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1122;
          FStar_Syntax_Syntax.fv_delta = uu____1123;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor );_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu____1124;
          FStar_Syntax_Syntax.fv_delta = uu____1125;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu____1126);_}
        -> true
    | uu____1133 -> false
  
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1137 =
      let uu____1138 = FStar_Syntax_Subst.compress t  in
      uu____1138.FStar_Syntax_Syntax.n  in
    match uu____1137 with
    | FStar_Syntax_Syntax.Tm_constant uu____1141 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu____1142 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu____1143 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____1144 -> true
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1183 = is_constructor head1  in
        if uu____1183
        then
          FStar_All.pipe_right args
            (FStar_List.for_all
               (fun uu____1199  ->
                  match uu____1199 with
                  | (te,uu____1205) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____1208) -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____1214,uu____1215) ->
        is_fstar_value t1
    | uu____1256 -> false
  
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu____1260 -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu____1261 -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu____1262 -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu____1263 -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu____1274,exps) ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu____1283,fields) ->
        FStar_Util.for_all
          (fun uu____1308  ->
             match uu____1308 with | (uu____1313,e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h,uu____1316) -> is_ml_value h
    | uu____1321 -> false
  
let (fresh : Prims.string -> Prims.string) =
  let c = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun x  ->
    FStar_Util.incr c;
    (let uu____1362 =
       let uu____1363 = FStar_ST.op_Bang c  in
       FStar_Util.string_of_int uu____1363  in
     Prims.strcat x uu____1362)
  
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0  ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs (bs',body,copt1) ->
          aux (FStar_List.append bs bs') body copt1
      | uu____1462 ->
          let e' = FStar_Syntax_Util.unascribe t1  in
          let uu____1464 = FStar_Syntax_Util.is_fun e'  in
          if uu____1464
          then aux bs e' copt
          else FStar_Syntax_Util.abs bs e' copt
       in
    aux [] t0 FStar_Pervasives_Native.None
  
let (unit_binder : FStar_Syntax_Syntax.binder) =
  let uu____1470 =
    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
      FStar_Syntax_Syntax.t_unit
     in
  FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1470 
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
      (let uu____1548 = FStar_List.hd l  in
       match uu____1548 with
       | (p1,w1,e1) ->
           let uu____1582 =
             let uu____1591 = FStar_List.tl l  in FStar_List.hd uu____1591
              in
           (match uu____1582 with
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
                 | uu____1665 -> def)))
  
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
      let uu____1694 = FStar_Extraction_ML_Util.doms_and_cod t  in
      match uu____1694 with
      | (ts,r) ->
          if ts = []
          then e
          else
            (let vs = FStar_List.map (fun uu____1714  -> fresh "a") ts  in
             let vs_ts = FStar_List.zip vs ts  in
             let vs_es =
               let uu____1725 = FStar_List.zip vs ts  in
               FStar_List.map
                 (fun uu____1739  ->
                    match uu____1739 with
                    | (v1,t1) ->
                        FStar_Extraction_ML_Syntax.with_ty t1
                          (FStar_Extraction_ML_Syntax.MLE_Var v1)) uu____1725
                in
             let body =
               FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty r)
                 (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es))
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t)
               (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
  
let (maybe_eta_expand :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun expect  ->
    fun e  ->
      let uu____1761 =
        (FStar_Options.ml_no_eta_expand_coertions ()) ||
          (let uu____1763 = FStar_Options.codegen ()  in
           uu____1763 = (FStar_Pervasives_Native.Some FStar_Options.Kremlin))
         in
      if uu____1761 then e else eta_expand expect e
  
let (maybe_coerce :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g  ->
    fun e  ->
      fun ty  ->
        fun expect  ->
          let ty1 = eraseTypeDeep g ty  in
          let uu____1782 =
            type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect  in
          match uu____1782 with
          | (true ,FStar_Pervasives_Native.Some e') -> e'
          | uu____1792 ->
              (FStar_Extraction_ML_UEnv.debug g
                 (fun uu____1804  ->
                    let uu____1805 =
                      FStar_Extraction_ML_Code.string_of_mlexpr
                        g.FStar_Extraction_ML_UEnv.currentModule e
                       in
                    let uu____1806 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule ty1
                       in
                    let uu____1807 =
                      FStar_Extraction_ML_Code.string_of_mlty
                        g.FStar_Extraction_ML_UEnv.currentModule expect
                       in
                    FStar_Util.print3
                      "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                      uu____1805 uu____1806 uu____1807);
               (let uu____1808 =
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty expect)
                    (FStar_Extraction_ML_Syntax.MLE_Coerce (e, ty1, expect))
                   in
                maybe_eta_expand expect uu____1808))
  
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g  ->
    fun bv  ->
      let uu____1815 = FStar_Extraction_ML_UEnv.lookup_bv g bv  in
      match uu____1815 with
      | FStar_Util.Inl (uu____1816,t) -> t
      | uu____1830 -> FStar_Extraction_ML_Syntax.MLTY_Top
  
let (must_erase :
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____1851 =
          let uu____1852 = FStar_Syntax_Subst.compress t1  in
          uu____1852.FStar_Syntax_Syntax.n  in
        match uu____1851 with
        | FStar_Syntax_Syntax.Tm_type uu____1855 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid
        | FStar_Syntax_Syntax.Tm_arrow uu____1857 ->
            let uu____1870 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____1870 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____1896 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____1896
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____1898;
               FStar_Syntax_Syntax.index = uu____1899;
               FStar_Syntax_Syntax.sort = t2;_},uu____1901)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1909,uu____1910) ->
            aux env t2
        | uu____1951 -> false
      
      and aux env t1 =
        let t2 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Primops;
            FStar_TypeChecker_Normalize.Weak;
            FStar_TypeChecker_Normalize.HNF;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.Delta_constant;
            FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses;
            FStar_TypeChecker_Normalize.Zeta;
            FStar_TypeChecker_Normalize.Iota] env t1
           in
        let res = aux_whnf env t2  in
        FStar_Extraction_ML_UEnv.debug g
          (fun uu____1961  ->
             let uu____1962 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "must_erase=%s: %s\n"
               (if res then "true" else "false") uu____1962);
        res
       in aux g.FStar_Extraction_ML_UEnv.tcenv t
  
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
      let arg_as_mlty g1 uu____1996 =
        match uu____1996 with
        | (a,uu____2002) ->
            let uu____2003 = is_type g1 a  in
            if uu____2003
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_UEnv.erasedContent
         in
      let fv_app_as_mlty g1 fv args =
        let uu____2015 =
          let uu____2028 =
            FStar_TypeChecker_Env.lookup_lid
              g1.FStar_Extraction_ML_UEnv.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____2028 with
          | ((uu____2049,fvty),uu____2051) ->
              let fvty1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.UnfoldUntil
                     FStar_Syntax_Syntax.Delta_constant]
                  g1.FStar_Extraction_ML_UEnv.tcenv fvty
                 in
              FStar_Syntax_Util.arrow_formals fvty1
           in
        match uu____2015 with
        | (formals,uu____2058) ->
            let mlargs = FStar_List.map (arg_as_mlty g1) args  in
            let mlargs1 =
              let n_args = FStar_List.length args  in
              if (FStar_List.length formals) > n_args
              then
                let uu____2102 = FStar_Util.first_N n_args formals  in
                match uu____2102 with
                | (uu____2129,rest) ->
                    let uu____2155 =
                      FStar_List.map
                        (fun uu____2163  ->
                           FStar_Extraction_ML_UEnv.erasedContent) rest
                       in
                    FStar_List.append mlargs uu____2155
              else mlargs  in
            let nm =
              let uu____2170 =
                FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g1 fv
                 in
              match uu____2170 with
              | FStar_Pervasives_Native.Some p -> p
              | FStar_Pervasives_Native.None  ->
                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm)
         in
      let aux env t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_type uu____2184 ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu____2185 ->
            let uu____2186 =
              let uu____2187 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2187
               in
            failwith uu____2186
        | FStar_Syntax_Syntax.Tm_delayed uu____2188 ->
            let uu____2213 =
              let uu____2214 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2214
               in
            failwith uu____2213
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____2215 =
              let uu____2216 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1 "Impossible: Unexpected term %s" uu____2216
               in
            failwith uu____2215
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____2218 = FStar_Syntax_Util.unfold_lazy i  in
            translate_term_to_mlty env uu____2218
        | FStar_Syntax_Syntax.Tm_constant uu____2219 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_quoted uu____2220 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_uvar uu____2227 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2245) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____2250;
               FStar_Syntax_Syntax.index = uu____2251;
               FStar_Syntax_Syntax.sort = t2;_},uu____2253)
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2261) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2267,uu____2268) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____2335 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____2335 with
             | (bs1,c1) ->
                 let uu____2342 = binders_as_ml_binders env bs1  in
                 (match uu____2342 with
                  | (mlbs,env1) ->
                      let t_ret =
                        let eff =
                          FStar_TypeChecker_Env.norm_eff_name
                            env1.FStar_Extraction_ML_UEnv.tcenv
                            (FStar_Syntax_Util.comp_effect_name c1)
                           in
                        let uu____2369 =
                          let uu____2376 =
                            FStar_TypeChecker_Env.effect_decl_opt
                              env1.FStar_Extraction_ML_UEnv.tcenv eff
                             in
                          FStar_Util.must uu____2376  in
                        match uu____2369 with
                        | (ed,qualifiers) ->
                            let uu____2397 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____2397
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
                      let uu____2404 =
                        FStar_List.fold_right
                          (fun uu____2423  ->
                             fun uu____2424  ->
                               match (uu____2423, uu____2424) with
                               | ((uu____2445,t2),(tag,t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (erase, t_ret)
                         in
                      (match uu____2404 with | (uu____2457,t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let res =
              let uu____2482 =
                let uu____2483 = FStar_Syntax_Util.un_uinst head1  in
                uu____2483.FStar_Syntax_Syntax.n  in
              match uu____2482 with
              | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv args
              | FStar_Syntax_Syntax.Tm_app (head2,args') ->
                  let uu____2510 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_app
                         (head2, (FStar_List.append args' args)))
                      FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                     in
                  translate_term_to_mlty env uu____2510
              | uu____2527 -> FStar_Extraction_ML_UEnv.unknownType  in
            res
        | FStar_Syntax_Syntax.Tm_abs (bs,ty,uu____2530) ->
            let uu____2551 = FStar_Syntax_Subst.open_term bs ty  in
            (match uu____2551 with
             | (bs1,ty1) ->
                 let uu____2558 = binders_as_ml_binders env bs1  in
                 (match uu____2558 with
                  | (bts,env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu____2583 ->
            FStar_Extraction_ML_UEnv.unknownType
        | FStar_Syntax_Syntax.Tm_match uu____2596 ->
            FStar_Extraction_ML_UEnv.unknownType
         in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top  -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu____2623 ->
            let uu____2630 = FStar_Extraction_ML_Util.udelta_unfold g t  in
            (match uu____2630 with
             | FStar_Pervasives_Native.None  -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu____2634 -> false  in
      let uu____2635 = must_erase g t0  in
      if uu____2635
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0  in
         let uu____2638 = is_top_ty mlt  in
         if uu____2638
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
      let uu____2653 =
        FStar_All.pipe_right bs
          (FStar_List.fold_left
             (fun uu____2696  ->
                fun b  ->
                  match uu____2696 with
                  | (ml_bs,env) ->
                      let uu____2736 = is_type_binder g b  in
                      if uu____2736
                      then
                        let b1 = FStar_Pervasives_Native.fst b  in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1
                            (FStar_Pervasives_Native.Some
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                           in
                        let ml_b =
                          let uu____2754 =
                            FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1  in
                          (uu____2754, FStar_Extraction_ML_Syntax.ml_unit_ty)
                           in
                        ((ml_b :: ml_bs), env1)
                      else
                        (let b1 = FStar_Pervasives_Native.fst b  in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort
                            in
                         let uu____2768 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false false
                            in
                         match uu____2768 with
                         | (env1,b2) ->
                             let ml_b =
                               let uu____2792 =
                                 FStar_Extraction_ML_UEnv.removeTick b2  in
                               (uu____2792, t)  in
                             ((ml_b :: ml_bs), env1))) ([], g))
         in
      match uu____2653 with | (ml_bs,env) -> ((FStar_List.rev ml_bs), env)

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
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,uu____2867) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (FStar_List.append es1 [e2])
      | (uu____2870,FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu____2874 -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
  
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
                    | uu____2902 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu____2903 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu____2904 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu____2907 -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
  
let (resugar_pat :
  FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlpattern ->
      FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun q  ->
    fun p  ->
      match p with
      | FStar_Extraction_ML_Syntax.MLP_CTor (d,pats) ->
          let uu____2924 = FStar_Extraction_ML_Util.is_xtuple d  in
          (match uu____2924 with
           | FStar_Pervasives_Native.Some n1 ->
               FStar_Extraction_ML_Syntax.MLP_Tuple pats
           | uu____2928 ->
               (match q with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Record_ctor (ty,fns)) ->
                    let path =
                      FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns
                       in
                    let fs = record_fields fns pats  in
                    FStar_Extraction_ML_Syntax.MLP_Record (path, fs)
                | uu____2955 -> p))
      | uu____2958 -> p
  
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
                       (fun uu____3038  ->
                          let uu____3039 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t'
                             in
                          let uu____3040 =
                            FStar_Extraction_ML_Code.string_of_mlty
                              g.FStar_Extraction_ML_UEnv.currentModule t
                             in
                          FStar_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu____3039 uu____3040)
                   else ();
                   ok)
               in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c,swopt)) when
                let uu____3070 = FStar_Options.codegen ()  in
                uu____3070 <>
                  (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
                ->
                let uu____3075 =
                  match swopt with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3088 =
                        let uu____3089 =
                          let uu____3090 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None))
                             in
                          FStar_Extraction_ML_Syntax.MLE_Const uu____3090  in
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu____3089
                         in
                      (uu____3088, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          (g.FStar_Extraction_ML_UEnv.tcenv).FStar_TypeChecker_Env.dsenv
                          c sw FStar_Range.dummyRange
                         in
                      let uu____3111 = term_as_mlexpr g source_term  in
                      (match uu____3111 with
                       | (mlterm,uu____3123,mlty) -> (mlterm, mlty))
                   in
                (match uu____3075 with
                 | (mlc,ml_ty) ->
                     let x = FStar_Extraction_ML_Syntax.gensym ()  in
                     let when_clause =
                       let uu____3143 =
                         let uu____3144 =
                           let uu____3151 =
                             let uu____3154 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                 (FStar_Extraction_ML_Syntax.MLE_Var x)
                                in
                             [uu____3154; mlc]  in
                           (FStar_Extraction_ML_Util.prims_op_equality,
                             uu____3151)
                            in
                         FStar_Extraction_ML_Syntax.MLE_App uu____3144  in
                       FStar_All.pipe_left
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.ml_bool_ty) uu____3143
                        in
                     let uu____3157 = ok ml_ty  in
                     (g,
                       (FStar_Pervasives_Native.Some
                          ((FStar_Extraction_ML_Syntax.MLP_Var x),
                            [when_clause])), uu____3157))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  FStar_TypeChecker_TcTerm.tc_constant
                    g.FStar_Extraction_ML_UEnv.tcenv FStar_Range.dummyRange s
                   in
                let mlty = term_as_mlty g t  in
                let uu____3177 =
                  let uu____3186 =
                    let uu____3193 =
                      let uu____3194 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s
                         in
                      FStar_Extraction_ML_Syntax.MLP_Const uu____3194  in
                    (uu____3193, [])  in
                  FStar_Pervasives_Native.Some uu____3186  in
                let uu____3203 = ok mlty  in (g, uu____3177, uu____3203)
            | FStar_Syntax_Syntax.Pat_var x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3214 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3214 with
                 | (g1,x1) ->
                     let uu____3237 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3237))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let mlty = term_as_mlty g x.FStar_Syntax_Syntax.sort  in
                let uu____3271 =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], mlty) false
                    false imp
                   in
                (match uu____3271 with
                 | (g1,x1) ->
                     let uu____3294 = ok mlty  in
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       uu____3294))
            | FStar_Syntax_Syntax.Pat_dot_term uu____3326 ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f,pats) ->
                let uu____3365 =
                  let uu____3370 = FStar_Extraction_ML_UEnv.lookup_fv g f  in
                  match uu____3370 with
                  | FStar_Util.Inr
                      (uu____3375,{
                                    FStar_Extraction_ML_Syntax.expr =
                                      FStar_Extraction_ML_Syntax.MLE_Name n1;
                                    FStar_Extraction_ML_Syntax.mlty =
                                      uu____3377;
                                    FStar_Extraction_ML_Syntax.loc =
                                      uu____3378;_},ttys,uu____3380)
                      -> (n1, ttys)
                  | uu____3393 -> failwith "Expected a constructor"  in
                (match uu____3365 with
                 | (d,tys) ->
                     let nTyVars =
                       FStar_List.length (FStar_Pervasives_Native.fst tys)
                        in
                     let uu____3415 = FStar_Util.first_N nTyVars pats  in
                     (match uu____3415 with
                      | (tysVarPats,restPats) ->
                          let f_ty_opt =
                            try
                              let mlty_args =
                                FStar_All.pipe_right tysVarPats
                                  (FStar_List.map
                                     (fun uu____3548  ->
                                        match uu____3548 with
                                        | (p1,uu____3556) ->
                                            (match p1.FStar_Syntax_Syntax.v
                                             with
                                             | FStar_Syntax_Syntax.Pat_dot_term
                                                 (uu____3561,t) ->
                                                 term_as_mlty g t
                                             | uu____3567 ->
                                                 (FStar_Extraction_ML_UEnv.debug
                                                    g
                                                    (fun uu____3571  ->
                                                       let uu____3572 =
                                                         FStar_Syntax_Print.pat_to_string
                                                           p1
                                                          in
                                                       FStar_Util.print1
                                                         "Pattern %s is not extractable"
                                                         uu____3572);
                                                  FStar_Exn.raise
                                                    Un_extractable))))
                                 in
                              let f_ty =
                                FStar_Extraction_ML_Util.subst tys mlty_args
                                 in
                              let uu____3574 =
                                FStar_Extraction_ML_Util.uncurry_mlty_fun
                                  f_ty
                                 in
                              FStar_Pervasives_Native.Some uu____3574
                            with
                            | Un_extractable  -> FStar_Pervasives_Native.None
                             in
                          let uu____3603 =
                            FStar_Util.fold_map
                              (fun g1  ->
                                 fun uu____3639  ->
                                   match uu____3639 with
                                   | (p1,imp1) ->
                                       let uu____3658 =
                                         extract_one_pat true g1 p1
                                           FStar_Pervasives_Native.None
                                           term_as_mlexpr
                                          in
                                       (match uu____3658 with
                                        | (g2,p2,uu____3687) -> (g2, p2))) g
                              tysVarPats
                             in
                          (match uu____3603 with
                           | (g1,tyMLPats) ->
                               let uu____3748 =
                                 FStar_Util.fold_map
                                   (fun uu____3812  ->
                                      fun uu____3813  ->
                                        match (uu____3812, uu____3813) with
                                        | ((g2,f_ty_opt1),(p1,imp1)) ->
                                            let uu____3906 =
                                              match f_ty_opt1 with
                                              | FStar_Pervasives_Native.Some
                                                  (hd1::rest,res) ->
                                                  ((FStar_Pervasives_Native.Some
                                                      (rest, res)),
                                                    (FStar_Pervasives_Native.Some
                                                       hd1))
                                              | uu____3966 ->
                                                  (FStar_Pervasives_Native.None,
                                                    FStar_Pervasives_Native.None)
                                               in
                                            (match uu____3906 with
                                             | (f_ty_opt2,expected_ty) ->
                                                 let uu____4037 =
                                                   extract_one_pat false g2
                                                     p1 expected_ty
                                                     term_as_mlexpr
                                                    in
                                                 (match uu____4037 with
                                                  | (g3,p2,uu____4078) ->
                                                      ((g3, f_ty_opt2), p2))))
                                   (g1, f_ty_opt) restPats
                                  in
                               (match uu____3748 with
                                | ((g2,f_ty_opt1),restMLPats) ->
                                    let uu____4196 =
                                      let uu____4207 =
                                        FStar_All.pipe_right
                                          (FStar_List.append tyMLPats
                                             restMLPats)
                                          (FStar_List.collect
                                             (fun uu___60_4258  ->
                                                match uu___60_4258 with
                                                | FStar_Pervasives_Native.Some
                                                    x -> [x]
                                                | uu____4300 -> []))
                                         in
                                      FStar_All.pipe_right uu____4207
                                        FStar_List.split
                                       in
                                    (match uu____4196 with
                                     | (mlPats,when_clauses) ->
                                         let pat_ty_compat =
                                           match f_ty_opt1 with
                                           | FStar_Pervasives_Native.Some
                                               ([],t) -> ok t
                                           | uu____4373 -> false  in
                                         let uu____4382 =
                                           let uu____4391 =
                                             let uu____4398 =
                                               resugar_pat
                                                 f.FStar_Syntax_Syntax.fv_qual
                                                 (FStar_Extraction_ML_Syntax.MLP_CTor
                                                    (d, mlPats))
                                                in
                                             let uu____4401 =
                                               FStar_All.pipe_right
                                                 when_clauses
                                                 FStar_List.flatten
                                                in
                                             (uu____4398, uu____4401)  in
                                           FStar_Pervasives_Native.Some
                                             uu____4391
                                            in
                                         (g2, uu____4382, pat_ty_compat))))))
  
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
            let uu____4514 =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr  in
            match uu____4514 with
            | (g2,FStar_Pervasives_Native.Some (x,v1),b) -> (g2, (x, v1), b)
            | uu____4571 ->
                failwith "Impossible: Unable to translate pattern"
             in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd1::tl1 ->
                let uu____4614 =
                  FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1
                    tl1
                   in
                FStar_Pervasives_Native.Some uu____4614
             in
          let uu____4615 =
            extract_one_pat1 g p (FStar_Pervasives_Native.Some expected_t)
             in
          match uu____4615 with
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
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0,uu____4753,t1) ->
                let x = FStar_Extraction_ML_Syntax.gensym ()  in
                let uu____4756 =
                  let uu____4767 =
                    let uu____4776 =
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty t0)
                        (FStar_Extraction_ML_Syntax.MLE_Var x)
                       in
                    ((x, t0), uu____4776)  in
                  uu____4767 :: more_args  in
                eta_args uu____4756 t1
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu____4789,uu____4790)
                -> ((FStar_List.rev more_args), t)
            | uu____4813 -> failwith "Impossible: Head type is not an arrow"
             in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor
               (uu____4841,args),FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Record_ctor (tyname,fields))) ->
                let path =
                  FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns
                   in
                let fields1 = record_fields fields args  in
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path, fields1))
            | uu____4873 -> e  in
          let resugar_and_maybe_eta qual1 e =
            let uu____4891 = eta_args [] residualType  in
            match uu____4891 with
            | (eargs,tres) ->
                (match eargs with
                 | [] ->
                     let uu____4944 = as_record qual1 e  in
                     FStar_Extraction_ML_Util.resugar_exp uu____4944
                 | uu____4945 ->
                     let uu____4956 = FStar_List.unzip eargs  in
                     (match uu____4956 with
                      | (binders,eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head1,args)
                               ->
                               let body =
                                 let uu____4998 =
                                   let uu____4999 =
                                     FStar_All.pipe_left
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head1,
                                            (FStar_List.append args eargs1)))
                                      in
                                   FStar_All.pipe_left (as_record qual1)
                                     uu____4999
                                    in
                                 FStar_All.pipe_left
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu____4998
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu____5008 ->
                               failwith "Impossible: Not a constructor")))
             in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu____5011,FStar_Pervasives_Native.None ) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5015;
                FStar_Extraction_ML_Syntax.loc = uu____5016;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5043 ->
                    let uu____5046 =
                      let uu____5053 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5053, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5046
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
                     FStar_Extraction_ML_Syntax.mlty = uu____5057;
                     FStar_Extraction_ML_Syntax.loc = uu____5058;_},uu____5059);
                FStar_Extraction_ML_Syntax.mlty = uu____5060;
                FStar_Extraction_ML_Syntax.loc = uu____5061;_},mle::args),FStar_Pervasives_Native.Some
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
                | uu____5092 ->
                    let uu____5095 =
                      let uu____5102 =
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj
                         in
                      (uu____5102, args)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5095
                 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5106;
                FStar_Extraction_ML_Syntax.loc = uu____5107;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5115 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5115
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5119;
                FStar_Extraction_ML_Syntax.loc = uu____5120;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5122)) ->
              let uu____5135 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5135
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5139;
                     FStar_Extraction_ML_Syntax.loc = uu____5140;_},uu____5141);
                FStar_Extraction_ML_Syntax.mlty = uu____5142;
                FStar_Extraction_ML_Syntax.loc = uu____5143;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5155 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5155
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu____5159;
                     FStar_Extraction_ML_Syntax.loc = uu____5160;_},uu____5161);
                FStar_Extraction_ML_Syntax.mlty = uu____5162;
                FStar_Extraction_ML_Syntax.loc = uu____5163;_},mlargs),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5165)) ->
              let uu____5182 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5182
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor
             )) ->
              let uu____5188 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5188
          | (FStar_Extraction_ML_Syntax.MLE_Name
             mlp,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5192)) ->
              let uu____5201 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5201
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5205;
                FStar_Extraction_ML_Syntax.loc = uu____5206;_},uu____5207),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Data_ctor )) ->
              let uu____5214 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5214
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu____5218;
                FStar_Extraction_ML_Syntax.loc = uu____5219;_},uu____5220),FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_ctor uu____5221)) ->
              let uu____5234 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, []))
                 in
              FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____5234
          | uu____5237 -> mlAppExpr
  
let (maybe_downgrade_eff :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.e_tag)
  =
  fun g  ->
    fun f  ->
      fun t  ->
        let rec non_informative1 t1 =
          let uu____5257 =
            (type_leq g t1 FStar_Extraction_ML_Syntax.ml_unit_ty) ||
              (erasableType g t1)
             in
          if uu____5257
          then true
          else
            (match t1 with
             | FStar_Extraction_ML_Syntax.MLTY_Fun
                 (uu____5259,FStar_Extraction_ML_Syntax.E_PURE ,t2) ->
                 non_informative1 t2
             | FStar_Extraction_ML_Syntax.MLTY_Fun
                 (uu____5261,FStar_Extraction_ML_Syntax.E_GHOST ,t2) ->
                 non_informative1 t2
             | uu____5263 -> false)
           in
        let uu____5264 =
          (f = FStar_Extraction_ML_Syntax.E_GHOST) && (non_informative1 t)
           in
        if uu____5264 then FStar_Extraction_ML_Syntax.E_PURE else f
  
let rec (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.e_tag,
        FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple3)
  = fun g  -> fun t  -> term_as_mlexpr' g t

and (check_term_as_mlexpr :
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
            (fun uu____5318  ->
               let uu____5319 = FStar_Syntax_Print.term_to_string e  in
               let uu____5320 =
                 FStar_Extraction_ML_Code.string_of_mlty
                   g.FStar_Extraction_ML_UEnv.currentModule ty
                  in
               FStar_Util.print2 "Checking %s at type %s\n" uu____5319
                 uu____5320);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_GHOST ,uu____5325) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE
              ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu____5326 ->
               let uu____5331 = term_as_mlexpr g e  in
               (match uu____5331 with
                | (ml_e,tag,t) ->
                    let uu____5345 = FStar_Extraction_ML_Util.eff_leq tag f
                       in
                    if uu____5345
                    then
                      let uu____5350 = maybe_coerce g ml_e t ty  in
                      (uu____5350, ty)
                    else
                      (match (tag, f, ty) with
                       | (FStar_Extraction_ML_Syntax.E_GHOST
                          ,FStar_Extraction_ML_Syntax.E_PURE
                          ,FStar_Extraction_ML_Syntax.MLTY_Erased ) ->
                           let uu____5356 = maybe_coerce g ml_e t ty  in
                           (uu____5356, ty)
                       | uu____5357 ->
                           (err_unexpected_eff g e ty f tag;
                            (let uu____5365 = maybe_coerce g ml_e t ty  in
                             (uu____5365, ty))))))

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
           let uu____5378 =
             let uu____5379 =
               FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
             let uu____5380 = FStar_Syntax_Print.tag_of_term top  in
             let uu____5381 = FStar_Syntax_Print.term_to_string top  in
             FStar_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu____5379 uu____5380 uu____5381
              in
           FStar_Util.print_string uu____5378);
      (let t = FStar_Syntax_Subst.compress top  in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5389 =
             let uu____5390 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5390
              in
           failwith uu____5389
       | FStar_Syntax_Syntax.Tm_delayed uu____5397 ->
           let uu____5422 =
             let uu____5423 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5423
              in
           failwith uu____5422
       | FStar_Syntax_Syntax.Tm_uvar uu____5430 ->
           let uu____5447 =
             let uu____5448 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5448
              in
           failwith uu____5447
       | FStar_Syntax_Syntax.Tm_bvar uu____5455 ->
           let uu____5456 =
             let uu____5457 = FStar_Syntax_Print.tag_of_term t  in
             FStar_Util.format1 "Impossible: Unexpected term: %s" uu____5457
              in
           failwith uu____5456
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____5465 = FStar_Syntax_Util.unfold_lazy i  in
           term_as_mlexpr' g uu____5465
       | FStar_Syntax_Syntax.Tm_type uu____5466 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu____5467 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu____5474 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____5488;_})
           ->
           let uu____5503 =
             let uu____5512 =
               let uu____5529 =
                 FStar_Syntax_Syntax.lid_as_fv
                   FStar_Parser_Const.failwith_lid
                   FStar_Syntax_Syntax.Delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Extraction_ML_UEnv.lookup_fv g uu____5529  in
             FStar_All.pipe_left FStar_Util.right uu____5512  in
           (match uu____5503 with
            | (uu____5572,fw,uu____5574,uu____5575) ->
                let uu____5576 =
                  let uu____5577 =
                    let uu____5578 =
                      let uu____5585 =
                        let uu____5588 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Open quotation at runtime"))
                           in
                        [uu____5588]  in
                      (fw, uu____5585)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____5578  in
                  FStar_All.pipe_left
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu____5577
                   in
                (uu____5576, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = aqs;_})
           ->
           let uu____5607 = FStar_Reflection_Basic.inspect_ln qt  in
           (match uu____5607 with
            | FStar_Reflection_Data.Tv_Var bv ->
                let uu____5615 = FStar_Syntax_Syntax.lookup_aq bv aqs  in
                (match uu____5615 with
                 | FStar_Pervasives_Native.Some (false ,tm) ->
                     term_as_mlexpr' g tm
                 | FStar_Pervasives_Native.Some (true ,tm) ->
                     let uu____5638 =
                       let uu____5647 =
                         let uu____5664 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.failwith_lid
                             FStar_Syntax_Syntax.Delta_constant
                             FStar_Pervasives_Native.None
                            in
                         FStar_Extraction_ML_UEnv.lookup_fv g uu____5664  in
                       FStar_All.pipe_left FStar_Util.right uu____5647  in
                     (match uu____5638 with
                      | (uu____5707,fw,uu____5709,uu____5710) ->
                          let uu____5711 =
                            let uu____5712 =
                              let uu____5713 =
                                let uu____5720 =
                                  let uu____5723 =
                                    FStar_All.pipe_left
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         FStar_Extraction_ML_Syntax.ml_string_ty)
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_String
                                            "Open quotation at runtime"))
                                     in
                                  [uu____5723]  in
                                (fw, uu____5720)  in
                              FStar_Extraction_ML_Syntax.MLE_App uu____5713
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_int_ty)
                              uu____5712
                             in
                          (uu____5711, FStar_Extraction_ML_Syntax.E_PURE,
                            FStar_Extraction_ML_Syntax.ml_int_ty))
                 | FStar_Pervasives_Native.None  ->
                     let tv =
                       let uu____5731 =
                         FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                       FStar_Syntax_Embeddings.embed uu____5731
                         t.FStar_Syntax_Syntax.pos
                         (FStar_Reflection_Data.Tv_Var bv)
                        in
                     let t1 =
                       let uu____5737 =
                         let uu____5746 = FStar_Syntax_Syntax.as_arg tv  in
                         [uu____5746]  in
                       FStar_Syntax_Util.mk_app
                         (FStar_Reflection_Data.refl_constant_term
                            FStar_Reflection_Data.fstar_refl_pack_ln)
                         uu____5737
                        in
                     term_as_mlexpr' g t1)
            | tv ->
                let tv1 =
                  let uu____5749 =
                    FStar_Reflection_Embeddings.e_term_view_aq aqs  in
                  FStar_Syntax_Embeddings.embed uu____5749
                    t.FStar_Syntax_Syntax.pos tv
                   in
                let t1 =
                  let uu____5755 =
                    let uu____5764 = FStar_Syntax_Syntax.as_arg tv1  in
                    [uu____5764]  in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_Data.refl_constant_term
                       FStar_Reflection_Data.fstar_refl_pack_ln) uu____5755
                   in
                term_as_mlexpr' g t1)
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Mutable_alloc ))
           ->
           FStar_Errors.raise_err
             (FStar_Errors.Error_NoLetMutable,
               "let-mutable no longer supported")
       | FStar_Syntax_Syntax.Tm_meta
           (t1,FStar_Syntax_Syntax.Meta_monadic (m,uu____5778)) ->
           let t2 = FStar_Syntax_Subst.compress t1  in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) when
                FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let uu____5808 =
                  let uu____5815 =
                    FStar_TypeChecker_Env.effect_decl_opt
                      g.FStar_Extraction_ML_UEnv.tcenv m
                     in
                  FStar_Util.must uu____5815  in
                (match uu____5808 with
                 | (ed,qualifiers) ->
                     let uu____5842 =
                       let uu____5843 =
                         FStar_All.pipe_right qualifiers
                           (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                          in
                       FStar_All.pipe_right uu____5843 Prims.op_Negation  in
                     if uu____5842
                     then term_as_mlexpr' g t2
                     else
                       failwith
                         "This should not happen (should have been handled at Tm_abs level)")
            | uu____5859 -> term_as_mlexpr' g t2)
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5861) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5867) -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____5873 =
             FStar_TypeChecker_TcTerm.type_of_tot_term
               g.FStar_Extraction_ML_UEnv.tcenv t
              in
           (match uu____5873 with
            | (uu____5886,ty,uu____5888) ->
                let ml_ty = term_as_mlty g ty  in
                let uu____5890 =
                  let uu____5891 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c
                     in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu____5891  in
                (uu____5890, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu____5892 ->
           let uu____5893 = is_type g t  in
           if uu____5893
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____5901 = FStar_Extraction_ML_UEnv.lookup_term g t  in
              match uu____5901 with
              | (FStar_Util.Inl uu____5914,uu____5915) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Util.Inr (uu____5952,x,mltys,uu____5955),qual) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____6001 =
                         maybe_eta_data_and_project_record g qual t1 x  in
                       (uu____6001, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6002 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu____6010 = is_type g t  in
           if uu____6010
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu____6018 = FStar_Extraction_ML_UEnv.try_lookup_fv g fv
                 in
              match uu____6018 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____6027) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | FStar_Pervasives_Native.Some (FStar_Util.Inr
                  (uu____6060,x,mltys,uu____6063)) ->
                  (match mltys with
                   | ([],t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([],t1) ->
                       let uu____6104 =
                         maybe_eta_data_and_project_record g
                           fv.FStar_Syntax_Syntax.fv_qual t1 x
                          in
                       (uu____6104, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu____6105 -> err_uninst g t mltys t))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,copt) ->
           let uu____6135 = FStar_Syntax_Subst.open_term bs body  in
           (match uu____6135 with
            | (bs1,body1) ->
                let uu____6148 = binders_as_ml_binders g bs1  in
                (match uu____6148 with
                 | (ml_bs,env) ->
                     let body2 =
                       match copt with
                       | FStar_Pervasives_Native.Some c ->
                           let uu____6181 =
                             FStar_TypeChecker_Env.is_reifiable
                               env.FStar_Extraction_ML_UEnv.tcenv c
                              in
                           if uu____6181
                           then
                             FStar_TypeChecker_Util.reify_body
                               env.FStar_Extraction_ML_UEnv.tcenv body1
                           else body1
                       | FStar_Pervasives_Native.None  ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu____6186  ->
                                 let uu____6187 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print1
                                   "No computation type for: %s\n" uu____6187);
                            body1)
                        in
                     let uu____6188 = term_as_mlexpr env body2  in
                     (match uu____6188 with
                      | (ml_body,f,t1) ->
                          let uu____6204 =
                            FStar_List.fold_right
                              (fun uu____6223  ->
                                 fun uu____6224  ->
                                   match (uu____6223, uu____6224) with
                                   | ((uu____6245,targ),(f1,t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1)
                             in
                          (match uu____6204 with
                           | (f1,tfun) ->
                               let uu____6265 =
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body))
                                  in
                               (uu____6265, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6272;
              FStar_Syntax_Syntax.vars = uu____6273;_},(a1,uu____6275)::[])
           ->
           let ty =
             let uu____6305 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid  in
             term_as_mlty g uu____6305  in
           let uu____6306 =
             let uu____6307 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos
                in
             FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty)
               uu____6307
              in
           (uu____6306, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6308;
              FStar_Syntax_Syntax.vars = uu____6309;_},(t1,uu____6311)::
            (r,uu____6313)::[])
           -> term_as_mlexpr' g t1
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____6352);
              FStar_Syntax_Syntax.pos = uu____6353;
              FStar_Syntax_Syntax.vars = uu____6354;_},uu____6355)
           -> failwith "Unreachable? Tm_app Const_reflect"
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_List.existsb
                     (fun uu___61_6411  ->
                        match uu___61_6411 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____6412 -> false)))
              in
           let uu____6413 =
             let uu____6418 =
               let uu____6419 = FStar_Syntax_Subst.compress head1  in
               uu____6419.FStar_Syntax_Syntax.n  in
             ((head1.FStar_Syntax_Syntax.n), uu____6418)  in
           (match uu____6413 with
            | (FStar_Syntax_Syntax.Tm_uvar uu____6428,uu____6429) ->
                let t1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.Iota;
                    FStar_TypeChecker_Normalize.Zeta;
                    FStar_TypeChecker_Normalize.EraseUniverses;
                    FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                    g.FStar_Extraction_ML_UEnv.tcenv t
                   in
                term_as_mlexpr' g t1
            | (uu____6447,FStar_Syntax_Syntax.Tm_abs
               (bs,uu____6449,FStar_Pervasives_Native.Some rc)) when
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
                term_as_mlexpr' g t1
            | (uu____6470,FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify )) ->
                let e =
                  let uu____6472 = FStar_List.hd args  in
                  FStar_TypeChecker_Util.reify_body_with_arg
                    g.FStar_Extraction_ML_UEnv.tcenv head1 uu____6472
                   in
                let tm =
                  let uu____6482 =
                    let uu____6483 = FStar_TypeChecker_Util.remove_reify e
                       in
                    let uu____6484 = FStar_List.tl args  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____6483 uu____6484  in
                  uu____6482 FStar_Pervasives_Native.None
                    t.FStar_Syntax_Syntax.pos
                   in
                term_as_mlexpr' g tm
            | uu____6493 ->
                let rec extract_app is_data uu____6538 uu____6539 restArgs =
                  match (uu____6538, uu____6539) with
                  | ((mlhead,mlargs_f),(f,t1)) ->
                      (match (restArgs, t1) with
                       | ([],uu____6629) ->
                           let mlargs =
                             FStar_All.pipe_right (FStar_List.rev mlargs_f)
                               (FStar_List.map FStar_Pervasives_Native.fst)
                              in
                           let app =
                             let uu____6664 =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t1)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (mlhead, mlargs))
                                in
                             FStar_All.pipe_left
                               (maybe_eta_data_and_project_record g is_data
                                  t1) uu____6664
                              in
                           (app, f, t1)
                       | ((arg,uu____6668)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (formal_t,f',t2)) when
                           (is_type g arg) &&
                             (type_leq g formal_t
                                FStar_Extraction_ML_Syntax.ml_unit_ty)
                           ->
                           let uu____6699 =
                             let uu____6704 =
                               FStar_Extraction_ML_Util.join
                                 arg.FStar_Syntax_Syntax.pos f f'
                                in
                             (uu____6704, t2)  in
                           extract_app is_data
                             (mlhead,
                               ((FStar_Extraction_ML_Syntax.ml_unit,
                                  FStar_Extraction_ML_Syntax.E_PURE) ::
                               mlargs_f)) uu____6699 rest
                       | ((e0,uu____6716)::rest,FStar_Extraction_ML_Syntax.MLTY_Fun
                          (tExpected,f',t2)) ->
                           let r = e0.FStar_Syntax_Syntax.pos  in
                           let expected_effect =
                             let uu____6749 =
                               (FStar_Options.lax ()) &&
                                 (FStar_TypeChecker_Util.short_circuit_head
                                    head1)
                                in
                             if uu____6749
                             then FStar_Extraction_ML_Syntax.E_IMPURE
                             else FStar_Extraction_ML_Syntax.E_PURE  in
                           let uu____6751 =
                             check_term_as_mlexpr g e0 expected_effect
                               tExpected
                              in
                           (match uu____6751 with
                            | (e01,tInferred) ->
                                let uu____6764 =
                                  let uu____6769 =
                                    FStar_Extraction_ML_Util.join_l r [f; f']
                                     in
                                  (uu____6769, t2)  in
                                extract_app is_data
                                  (mlhead, ((e01, expected_effect) ::
                                    mlargs_f)) uu____6764 rest)
                       | uu____6780 ->
                           let uu____6793 =
                             FStar_Extraction_ML_Util.udelta_unfold g t1  in
                           (match uu____6793 with
                            | FStar_Pervasives_Native.Some t2 ->
                                extract_app is_data (mlhead, mlargs_f)
                                  (f, t2) restArgs
                            | FStar_Pervasives_Native.None  ->
                                (match t1 with
                                 | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                                     (FStar_Extraction_ML_Syntax.ml_unit,
                                       FStar_Extraction_ML_Syntax.E_PURE, t1)
                                 | uu____6815 ->
                                     err_ill_typed_application g top restArgs
                                       t1)))
                   in
                let extract_app_maybe_projector is_data mlhead uu____6857
                  args1 =
                  match uu____6857 with
                  | (f,t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu____6889)
                           ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6967))::args3,FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu____6969,f',t3)) ->
                                 let uu____7006 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f'
                                    in
                                 remove_implicits args3 uu____7006 t3
                             | uu____7007 -> (args2, f1, t2)  in
                           let uu____7032 = remove_implicits args1 f t1  in
                           (match uu____7032 with
                            | (args2,f1,t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu____7088 ->
                           extract_app is_data (mlhead, []) (f, t1) args1)
                   in
                let extract_app_with_instantiations uu____7110 =
                  let head2 = FStar_Syntax_Util.un_uinst head1  in
                  match head2.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu____7118 ->
                      let uu____7119 =
                        let uu____7132 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____7132 with
                        | (FStar_Util.Inr (uu____7151,x1,x2,x3),q) ->
                            ((x1, x2, x3), q)
                        | uu____7196 -> failwith "FIXME Ty"  in
                      (match uu____7119 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____7246)::uu____7247 -> is_type g a
                             | uu____7266 -> false  in
                           let uu____7275 =
                             match vars with
                             | uu____7304::uu____7305 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____7316 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____7344 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____7344 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____7433  ->
                                               match uu____7433 with
                                               | (x,uu____7439) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____7452 ->
                                              let uu___65_7455 = e  in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___65_7455.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___65_7455.FStar_Extraction_ML_Syntax.loc)
                                              }
                                           in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____7459 ->
                                              let uu___66_7460 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___66_7460.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___66_7460.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____7461 ->
                                              let uu___66_7462 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___66_7462.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___66_7462.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____7464;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____7465;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___67_7471 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes
                                                        in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___67_7471.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___67_7471.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____7472 ->
                                              failwith
                                                "Impossible: Unexpected head term"
                                           in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____7275 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____7533 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____7533,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____7534 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu____7543 ->
                      let uu____7544 =
                        let uu____7557 =
                          FStar_Extraction_ML_UEnv.lookup_term g head2  in
                        match uu____7557 with
                        | (FStar_Util.Inr (uu____7576,x1,x2,x3),q) ->
                            ((x1, x2, x3), q)
                        | uu____7621 -> failwith "FIXME Ty"  in
                      (match uu____7544 with
                       | ((head_ml,(vars,t1),inst_ok),qual) ->
                           let has_typ_apps =
                             match args with
                             | (a,uu____7671)::uu____7672 -> is_type g a
                             | uu____7691 -> false  in
                           let uu____7700 =
                             match vars with
                             | uu____7729::uu____7730 when
                                 (Prims.op_Negation has_typ_apps) && inst_ok
                                 -> (head_ml, t1, args)
                             | uu____7741 ->
                                 let n1 = FStar_List.length vars  in
                                 if n1 <= (FStar_List.length args)
                                 then
                                   let uu____7769 =
                                     FStar_Util.first_N n1 args  in
                                   (match uu____7769 with
                                    | (prefix1,rest) ->
                                        let prefixAsMLTypes =
                                          FStar_List.map
                                            (fun uu____7858  ->
                                               match uu____7858 with
                                               | (x,uu____7864) ->
                                                   term_as_mlty g x) prefix1
                                           in
                                        let t2 =
                                          instantiate (vars, t1)
                                            prefixAsMLTypes
                                           in
                                        let mk_tapp e ty_args =
                                          match ty_args with
                                          | [] -> e
                                          | uu____7877 ->
                                              let uu___65_7880 = e  in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (FStar_Extraction_ML_Syntax.MLE_TApp
                                                     (e, ty_args));
                                                FStar_Extraction_ML_Syntax.mlty
                                                  =
                                                  (uu___65_7880.FStar_Extraction_ML_Syntax.mlty);
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___65_7880.FStar_Extraction_ML_Syntax.loc)
                                              }
                                           in
                                        let head3 =
                                          match head_ml.FStar_Extraction_ML_Syntax.expr
                                          with
                                          | FStar_Extraction_ML_Syntax.MLE_Name
                                              uu____7884 ->
                                              let uu___66_7885 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___66_7885.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___66_7885.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_Var
                                              uu____7886 ->
                                              let uu___66_7887 =
                                                mk_tapp head_ml
                                                  prefixAsMLTypes
                                                 in
                                              {
                                                FStar_Extraction_ML_Syntax.expr
                                                  =
                                                  (uu___66_7887.FStar_Extraction_ML_Syntax.expr);
                                                FStar_Extraction_ML_Syntax.mlty
                                                  = t2;
                                                FStar_Extraction_ML_Syntax.loc
                                                  =
                                                  (uu___66_7887.FStar_Extraction_ML_Syntax.loc)
                                              }
                                          | FStar_Extraction_ML_Syntax.MLE_App
                                              (head3,{
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         FStar_Extraction_ML_Syntax.MLE_Const
                                                         (FStar_Extraction_ML_Syntax.MLC_Unit
                                                         );
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         = uu____7889;
                                                       FStar_Extraction_ML_Syntax.loc
                                                         = uu____7890;_}::[])
                                              ->
                                              FStar_All.pipe_right
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   ((let uu___67_7896 =
                                                       mk_tapp head3
                                                         prefixAsMLTypes
                                                        in
                                                     {
                                                       FStar_Extraction_ML_Syntax.expr
                                                         =
                                                         (uu___67_7896.FStar_Extraction_ML_Syntax.expr);
                                                       FStar_Extraction_ML_Syntax.mlty
                                                         =
                                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                                            (FStar_Extraction_ML_Syntax.ml_unit_ty,
                                                              FStar_Extraction_ML_Syntax.E_PURE,
                                                              t2));
                                                       FStar_Extraction_ML_Syntax.loc
                                                         =
                                                         (uu___67_7896.FStar_Extraction_ML_Syntax.loc)
                                                     }),
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2)
                                          | uu____7897 ->
                                              failwith
                                                "Impossible: Unexpected head term"
                                           in
                                        (head3, t2, rest))
                                 else err_uninst g head2 (vars, t1) top
                              in
                           (match uu____7700 with
                            | (head_ml1,head_t,args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu____7958 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1
                                        in
                                     (uu____7958,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu____7959 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu____7968 ->
                      let uu____7969 = term_as_mlexpr g head2  in
                      (match uu____7969 with
                       | (head3,f,t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head3 (f, t1) args)
                   in
                let uu____7985 = is_type g t  in
                if uu____7985
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu____7993 =
                     let uu____7994 = FStar_Syntax_Util.un_uinst head1  in
                     uu____7994.FStar_Syntax_Syntax.n  in
                   match uu____7993 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu____8004 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv g fv  in
                       (match uu____8004 with
                        | FStar_Pervasives_Native.None  ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu____8013 -> extract_app_with_instantiations ())
                   | uu____8016 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed (e0,(tc,uu____8019),f) ->
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
           let uu____8086 = check_term_as_mlexpr g e0 f1 t1  in
           (match uu____8086 with | (e,t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let ((is_rec,lbs),e') ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs  in
           let uu____8117 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu____8131 = FStar_Syntax_Syntax.is_top_level lbs  in
                if uu____8131
                then (lbs, e')
                else
                  (let lb = FStar_List.hd lbs  in
                   let x =
                     let uu____8145 =
                       FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                     FStar_Syntax_Syntax.freshen_bv uu____8145  in
                   let lb1 =
                     let uu___68_8147 = lb  in
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Util.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (uu___68_8147.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (uu___68_8147.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (uu___68_8147.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (uu___68_8147.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (uu___68_8147.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (uu___68_8147.FStar_Syntax_Syntax.lbpos)
                     }  in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)] e'
                      in
                   ([lb1], e'1)))
              in
           (match uu____8117 with
            | (lbs1,e'1) ->
                let lbs2 =
                  if top_level
                  then
                    FStar_All.pipe_right lbs1
                      (FStar_List.map
                         (fun lb  ->
                            let tcenv =
                              let uu____8178 =
                                FStar_Ident.lid_of_path
                                  (FStar_List.append
                                     (FStar_Pervasives_Native.fst
                                        g.FStar_Extraction_ML_UEnv.currentModule)
                                     [FStar_Pervasives_Native.snd
                                        g.FStar_Extraction_ML_UEnv.currentModule])
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.set_current_module
                                g.FStar_Extraction_ML_UEnv.tcenv uu____8178
                               in
                            let lbdef =
                              let uu____8186 = FStar_Options.ml_ish ()  in
                              if uu____8186
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
                            let uu___69_8190 = lb  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___69_8190.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___69_8190.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___69_8190.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___69_8190.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___69_8190.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___69_8190.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1  in
                let maybe_generalize uu____8213 =
                  match uu____8213 with
                  | { FStar_Syntax_Syntax.lbname = lbname_;
                      FStar_Syntax_Syntax.lbunivs = uu____8233;
                      FStar_Syntax_Syntax.lbtyp = t1;
                      FStar_Syntax_Syntax.lbeff = lbeff;
                      FStar_Syntax_Syntax.lbdef = e;
                      FStar_Syntax_Syntax.lbattrs = uu____8237;
                      FStar_Syntax_Syntax.lbpos = uu____8238;_} ->
                      let f_e = effect_as_etag g lbeff  in
                      let t2 = FStar_Syntax_Subst.compress t1  in
                      let no_gen uu____8312 =
                        let expected_t = term_as_mlty g t2  in
                        (lbname_, f_e, (t2, ([], ([], expected_t))), false,
                          e)
                         in
                      if Prims.op_Negation top_level
                      then no_gen ()
                      else
                        (let uu____8393 = must_erase g t2  in
                         if uu____8393
                         then
                           (lbname_, f_e,
                             (t2,
                               ([],
                                 ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                             false, e)
                         else
                           (match t2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                let uu____8509 = FStar_List.hd bs  in
                                FStar_All.pipe_right uu____8509
                                  (is_type_binder g)
                                ->
                                let uu____8522 =
                                  FStar_Syntax_Subst.open_comp bs c  in
                                (match uu____8522 with
                                 | (bs1,c1) ->
                                     let uu____8547 =
                                       let uu____8554 =
                                         FStar_Util.prefix_until
                                           (fun x  ->
                                              let uu____8590 =
                                                is_type_binder g x  in
                                              Prims.op_Negation uu____8590)
                                           bs1
                                          in
                                       match uu____8554 with
                                       | FStar_Pervasives_Native.None  ->
                                           (bs1,
                                             (FStar_Syntax_Util.comp_result
                                                c1))
                                       | FStar_Pervasives_Native.Some
                                           (bs2,b,rest) ->
                                           let uu____8678 =
                                             FStar_Syntax_Util.arrow (b ::
                                               rest) c1
                                              in
                                           (bs2, uu____8678)
                                        in
                                     (match uu____8547 with
                                      | (tbinders,tbody) ->
                                          let n_tbinders =
                                            FStar_List.length tbinders  in
                                          let e1 =
                                            let uu____8723 = normalize_abs e
                                               in
                                            FStar_All.pipe_right uu____8723
                                              FStar_Syntax_Util.unmeta
                                             in
                                          (match e1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (bs2,body,copt) ->
                                               let uu____8765 =
                                                 FStar_Syntax_Subst.open_term
                                                   bs2 body
                                                  in
                                               (match uu____8765 with
                                                | (bs3,body1) ->
                                                    if
                                                      n_tbinders <=
                                                        (FStar_List.length
                                                           bs3)
                                                    then
                                                      let uu____8818 =
                                                        FStar_Util.first_N
                                                          n_tbinders bs3
                                                         in
                                                      (match uu____8818 with
                                                       | (targs,rest_args) ->
                                                           let expected_source_ty
                                                             =
                                                             let s =
                                                               FStar_List.map2
                                                                 (fun
                                                                    uu____8906
                                                                     ->
                                                                    fun
                                                                    uu____8907
                                                                     ->
                                                                    match 
                                                                    (uu____8906,
                                                                    uu____8907)
                                                                    with
                                                                    | 
                                                                    ((x,uu____8925),
                                                                    (y,uu____8927))
                                                                    ->
                                                                    let uu____8936
                                                                    =
                                                                    let uu____8943
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    y  in
                                                                    (x,
                                                                    uu____8943)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____8936)
                                                                 tbinders
                                                                 targs
                                                                in
                                                             FStar_Syntax_Subst.subst
                                                               s tbody
                                                              in
                                                           let env =
                                                             FStar_List.fold_left
                                                               (fun env  ->
                                                                  fun
                                                                    uu____8954
                                                                     ->
                                                                    match uu____8954
                                                                    with
                                                                    | 
                                                                    (a,uu____8960)
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
                                                             let uu____8969 =
                                                               FStar_All.pipe_right
                                                                 targs
                                                                 (FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____8987
                                                                     ->
                                                                    match uu____8987
                                                                    with
                                                                    | 
                                                                    (x,uu____8993)
                                                                    ->
                                                                    FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                    x))
                                                                in
                                                             (uu____8969,
                                                               expected_t)
                                                              in
                                                           let add_unit =
                                                             match rest_args
                                                             with
                                                             | [] ->
                                                                 let uu____9001
                                                                   =
                                                                   is_fstar_value
                                                                    body1
                                                                    in
                                                                 Prims.op_Negation
                                                                   uu____9001
                                                             | uu____9002 ->
                                                                 false
                                                              in
                                                           let rest_args1 =
                                                             if add_unit
                                                             then unit_binder
                                                               :: rest_args
                                                             else rest_args
                                                              in
                                                           let polytype1 =
                                                             if add_unit
                                                             then
                                                               FStar_Extraction_ML_Syntax.push_unit
                                                                 polytype
                                                             else polytype
                                                              in
                                                           let body2 =
                                                             FStar_Syntax_Util.abs
                                                               rest_args1
                                                               body1 copt
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
                                               uu____9071 ->
                                               let env =
                                                 FStar_List.fold_left
                                                   (fun env  ->
                                                      fun uu____9088  ->
                                                        match uu____9088 with
                                                        | (a,uu____9094) ->
                                                            FStar_Extraction_ML_UEnv.extend_ty
                                                              env a
                                                              FStar_Pervasives_Native.None)
                                                   g tbinders
                                                  in
                                               let expected_t =
                                                 term_as_mlty env tbody  in
                                               let polytype =
                                                 let uu____9103 =
                                                   FStar_All.pipe_right
                                                     tbinders
                                                     (FStar_List.map
                                                        (fun uu____9115  ->
                                                           match uu____9115
                                                           with
                                                           | (x,uu____9121)
                                                               ->
                                                               FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                 x))
                                                    in
                                                 (uu____9103, expected_t)  in
                                               let args =
                                                 FStar_All.pipe_right
                                                   tbinders
                                                   (FStar_List.map
                                                      (fun uu____9137  ->
                                                         match uu____9137
                                                         with
                                                         | (bv,uu____9143) ->
                                                             let uu____9144 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 bv
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____9144
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
                                               uu____9186 ->
                                               let env =
                                                 FStar_List.fold_left
                                                   (fun env  ->
                                                      fun uu____9197  ->
                                                        match uu____9197 with
                                                        | (a,uu____9203) ->
                                                            FStar_Extraction_ML_UEnv.extend_ty
                                                              env a
                                                              FStar_Pervasives_Native.None)
                                                   g tbinders
                                                  in
                                               let expected_t =
                                                 term_as_mlty env tbody  in
                                               let polytype =
                                                 let uu____9212 =
                                                   FStar_All.pipe_right
                                                     tbinders
                                                     (FStar_List.map
                                                        (fun uu____9224  ->
                                                           match uu____9224
                                                           with
                                                           | (x,uu____9230)
                                                               ->
                                                               FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                 x))
                                                    in
                                                 (uu____9212, expected_t)  in
                                               let args =
                                                 FStar_All.pipe_right
                                                   tbinders
                                                   (FStar_List.map
                                                      (fun uu____9246  ->
                                                         match uu____9246
                                                         with
                                                         | (bv,uu____9252) ->
                                                             let uu____9253 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 bv
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____9253
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
                                               uu____9295 ->
                                               let env =
                                                 FStar_List.fold_left
                                                   (fun env  ->
                                                      fun uu____9306  ->
                                                        match uu____9306 with
                                                        | (a,uu____9312) ->
                                                            FStar_Extraction_ML_UEnv.extend_ty
                                                              env a
                                                              FStar_Pervasives_Native.None)
                                                   g tbinders
                                                  in
                                               let expected_t =
                                                 term_as_mlty env tbody  in
                                               let polytype =
                                                 let uu____9321 =
                                                   FStar_All.pipe_right
                                                     tbinders
                                                     (FStar_List.map
                                                        (fun uu____9333  ->
                                                           match uu____9333
                                                           with
                                                           | (x,uu____9339)
                                                               ->
                                                               FStar_Extraction_ML_UEnv.bv_as_ml_tyvar
                                                                 x))
                                                    in
                                                 (uu____9321, expected_t)  in
                                               let args =
                                                 FStar_All.pipe_right
                                                   tbinders
                                                   (FStar_List.map
                                                      (fun uu____9355  ->
                                                         match uu____9355
                                                         with
                                                         | (bv,uu____9361) ->
                                                             let uu____9362 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 bv
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____9362
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
                                           | uu____9404 ->
                                               err_value_restriction e1)))
                            | uu____9423 -> no_gen ()))
                   in
                let check_lb env uu____9466 =
                  match uu____9466 with
                  | (nm,(lbname,f,(t1,(targs,polytype)),add_unit,e)) ->
                      let env1 =
                        FStar_List.fold_left
                          (fun env1  ->
                             fun uu____9601  ->
                               match uu____9601 with
                               | (a,uu____9607) ->
                                   FStar_Extraction_ML_UEnv.extend_ty env1 a
                                     FStar_Pervasives_Native.None) env targs
                         in
                      let expected_t = FStar_Pervasives_Native.snd polytype
                         in
                      let uu____9609 =
                        check_term_as_mlexpr env1 e f expected_t  in
                      (match uu____9609 with
                       | (e1,ty) ->
                           let f1 = maybe_downgrade_eff env1 f expected_t  in
                           let meta =
                             match ty with
                             | FStar_Extraction_ML_Syntax.MLTY_Erased  ->
                                 [FStar_Extraction_ML_Syntax.Erased]
                             | uu____9626 -> []  in
                           (f1,
                             {
                               FStar_Extraction_ML_Syntax.mllb_name = nm;
                               FStar_Extraction_ML_Syntax.mllb_tysc =
                                 (FStar_Pervasives_Native.Some polytype);
                               FStar_Extraction_ML_Syntax.mllb_add_unit =
                                 add_unit;
                               FStar_Extraction_ML_Syntax.mllb_def = e1;
                               FStar_Extraction_ML_Syntax.mllb_meta = meta;
                               FStar_Extraction_ML_Syntax.print_typ = true
                             }))
                   in
                let lbs3 =
                  FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize)
                   in
                let uu____9692 =
                  FStar_List.fold_right
                    (fun lb  ->
                       fun uu____9783  ->
                         match uu____9783 with
                         | (env,lbs4) ->
                             let uu____9908 = lb  in
                             (match uu____9908 with
                              | (lbname,uu____9956,(t1,(uu____9958,polytype)),add_unit,uu____9961)
                                  ->
                                  let uu____9974 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit true
                                     in
                                  (match uu____9974 with
                                   | (env1,nm) -> (env1, ((nm, lb) :: lbs4)))))
                    lbs3 (g, [])
                   in
                (match uu____9692 with
                 | (env_body,lbs4) ->
                     let env_def = if is_rec then env_body else g  in
                     let lbs5 =
                       FStar_All.pipe_right lbs4
                         (FStar_List.map (check_lb env_def))
                        in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos  in
                     let uu____10251 = term_as_mlexpr env_body e'1  in
                     (match uu____10251 with
                      | (e'2,f',t') ->
                          let f =
                            let uu____10268 =
                              let uu____10271 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  lbs5
                                 in
                              f' :: uu____10271  in
                            FStar_Extraction_ML_Util.join_l e'_rng
                              uu____10268
                             in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec  in
                          let uu____10280 =
                            let uu____10281 =
                              let uu____10282 =
                                let uu____10283 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    lbs5
                                   in
                                (is_rec1, uu____10283)  in
                              mk_MLE_Let top_level uu____10282 e'2  in
                            let uu____10292 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos
                               in
                            FStar_Extraction_ML_Syntax.with_ty_loc t'
                              uu____10281 uu____10292
                             in
                          (uu____10280, f, t'))))
       | FStar_Syntax_Syntax.Tm_match (scrutinee,pats) ->
           let uu____10331 = term_as_mlexpr g scrutinee  in
           (match uu____10331 with
            | (e,f_e,t_e) ->
                let uu____10347 = check_pats_for_ite pats  in
                (match uu____10347 with
                 | (b,then_e,else_e) ->
                     let no_lift x t1 = x  in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some
                           then_e1,FStar_Pervasives_Native.Some else_e1) ->
                            let uu____10404 = term_as_mlexpr g then_e1  in
                            (match uu____10404 with
                             | (then_mle,f_then,t_then) ->
                                 let uu____10420 = term_as_mlexpr g else_e1
                                    in
                                 (match uu____10420 with
                                  | (else_mle,f_else,t_else) ->
                                      let uu____10436 =
                                        let uu____10445 =
                                          type_leq g t_then t_else  in
                                        if uu____10445
                                        then (t_else, no_lift)
                                        else
                                          (let uu____10459 =
                                             type_leq g t_else t_then  in
                                           if uu____10459
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr))
                                         in
                                      (match uu____10436 with
                                       | (t_branch,maybe_lift1) ->
                                           let uu____10493 =
                                             let uu____10494 =
                                               let uu____10495 =
                                                 let uu____10504 =
                                                   maybe_lift1 then_mle
                                                     t_then
                                                    in
                                                 let uu____10505 =
                                                   let uu____10508 =
                                                     maybe_lift1 else_mle
                                                       t_else
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____10508
                                                    in
                                                 (e, uu____10504,
                                                   uu____10505)
                                                  in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu____10495
                                                in
                                             FStar_All.pipe_left
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu____10494
                                              in
                                           let uu____10511 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else
                                              in
                                           (uu____10493, uu____10511,
                                             t_branch))))
                        | uu____10512 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu____10528 =
                          FStar_All.pipe_right pats
                            (FStar_Util.fold_map
                               (fun compat  ->
                                  fun br  ->
                                    let uu____10637 =
                                      FStar_Syntax_Subst.open_branch br  in
                                    match uu____10637 with
                                    | (pat,when_opt,branch1) ->
                                        let uu____10681 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr
                                           in
                                        (match uu____10681 with
                                         | (env,p,pat_t_compat) ->
                                             let uu____10739 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let uu____10761 =
                                                     term_as_mlexpr env w  in
                                                   (match uu____10761 with
                                                    | (w1,f_w,t_w) ->
                                                        let w2 =
                                                          maybe_coerce env w1
                                                            t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w))
                                                in
                                             (match uu____10739 with
                                              | (when_opt1,f_when) ->
                                                  let uu____10810 =
                                                    term_as_mlexpr env
                                                      branch1
                                                     in
                                                  (match uu____10810 with
                                                   | (mlbranch,f_branch,t_branch)
                                                       ->
                                                       let uu____10844 =
                                                         FStar_All.pipe_right
                                                           p
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____10921 
                                                                 ->
                                                                 match uu____10921
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
                                                         uu____10844)))))
                               true)
                           in
                        match uu____10528 with
                        | (pat_t_compat,mlbranches) ->
                            let mlbranches1 = FStar_List.flatten mlbranches
                               in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu____11086  ->
                                      let uu____11087 =
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          e
                                         in
                                      let uu____11088 =
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          g.FStar_Extraction_ML_UEnv.currentModule
                                          t_e
                                         in
                                      FStar_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu____11087 uu____11088);
                                 FStar_All.pipe_left
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top)))
                               in
                            (match mlbranches1 with
                             | [] ->
                                 let uu____11113 =
                                   let uu____11122 =
                                     let uu____11139 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Parser_Const.failwith_lid
                                         FStar_Syntax_Syntax.Delta_constant
                                         FStar_Pervasives_Native.None
                                        in
                                     FStar_Extraction_ML_UEnv.lookup_fv g
                                       uu____11139
                                      in
                                   FStar_All.pipe_left FStar_Util.right
                                     uu____11122
                                    in
                                 (match uu____11113 with
                                  | (uu____11182,fw,uu____11184,uu____11185)
                                      ->
                                      let uu____11186 =
                                        let uu____11187 =
                                          let uu____11188 =
                                            let uu____11195 =
                                              let uu____11198 =
                                                FStar_All.pipe_left
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable"))
                                                 in
                                              [uu____11198]  in
                                            (fw, uu____11195)  in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu____11188
                                           in
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu____11187
                                         in
                                      (uu____11186,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu____11201,uu____11202,(uu____11203,f_first,t_first))::rest
                                 ->
                                 let uu____11263 =
                                   FStar_List.fold_left
                                     (fun uu____11305  ->
                                        fun uu____11306  ->
                                          match (uu____11305, uu____11306)
                                          with
                                          | ((topt,f),(uu____11363,uu____11364,
                                                       (uu____11365,f_branch,t_branch)))
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
                                                    let uu____11421 =
                                                      type_leq g t1 t_branch
                                                       in
                                                    if uu____11421
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu____11425 =
                                                         type_leq g t_branch
                                                           t1
                                                          in
                                                       if uu____11425
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
                                 (match uu____11263 with
                                  | (topt,f_match) ->
                                      let mlbranches2 =
                                        FStar_All.pipe_right mlbranches1
                                          (FStar_List.map
                                             (fun uu____11520  ->
                                                match uu____11520 with
                                                | (p,(wopt,uu____11549),
                                                   (b1,uu____11551,t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                           ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu____11570 -> b1
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
                                      let uu____11575 =
                                        FStar_All.pipe_left
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2))
                                         in
                                      (uu____11575, f_match, t_match)))))))

let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env  ->
    fun discName  ->
      fun constrName  ->
        let uu____11595 =
          let uu____11600 =
            FStar_TypeChecker_Env.lookup_lid
              env.FStar_Extraction_ML_UEnv.tcenv discName
             in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11600  in
        match uu____11595 with
        | (uu____11625,fstar_disc_type) ->
            let wildcards =
              let uu____11634 =
                let uu____11635 = FStar_Syntax_Subst.compress fstar_disc_type
                   in
                uu____11635.FStar_Syntax_Syntax.n  in
              match uu____11634 with
              | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11645) ->
                  let uu____11662 =
                    FStar_All.pipe_right binders
                      (FStar_List.filter
                         (fun uu___62_11694  ->
                            match uu___62_11694 with
                            | (uu____11701,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____11702)) ->
                                true
                            | uu____11705 -> false))
                     in
                  FStar_All.pipe_right uu____11662
                    (FStar_List.map
                       (fun uu____11738  ->
                          let uu____11745 = fresh "_"  in
                          (uu____11745, FStar_Extraction_ML_Syntax.MLTY_Top)))
              | uu____11746 -> failwith "Discriminator must be a function"
               in
            let mlid = fresh "_discr_"  in
            let targ = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
            let discrBody =
              let uu____11757 =
                let uu____11758 =
                  let uu____11769 =
                    let uu____11770 =
                      let uu____11771 =
                        let uu____11786 =
                          FStar_All.pipe_left
                            (FStar_Extraction_ML_Syntax.with_ty targ)
                            (FStar_Extraction_ML_Syntax.MLE_Name ([], mlid))
                           in
                        let uu____11789 =
                          let uu____11800 =
                            let uu____11809 =
                              let uu____11810 =
                                let uu____11817 =
                                  FStar_Extraction_ML_Syntax.mlpath_of_lident
                                    constrName
                                   in
                                (uu____11817,
                                  [FStar_Extraction_ML_Syntax.MLP_Wild])
                                 in
                              FStar_Extraction_ML_Syntax.MLP_CTor uu____11810
                               in
                            let uu____11820 =
                              FStar_All.pipe_left
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Const
                                   (FStar_Extraction_ML_Syntax.MLC_Bool true))
                               in
                            (uu____11809, FStar_Pervasives_Native.None,
                              uu____11820)
                             in
                          let uu____11823 =
                            let uu____11834 =
                              let uu____11843 =
                                FStar_All.pipe_left
                                  (FStar_Extraction_ML_Syntax.with_ty
                                     FStar_Extraction_ML_Syntax.ml_bool_ty)
                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                     (FStar_Extraction_ML_Syntax.MLC_Bool
                                        false))
                                 in
                              (FStar_Extraction_ML_Syntax.MLP_Wild,
                                FStar_Pervasives_Native.None, uu____11843)
                               in
                            [uu____11834]  in
                          uu____11800 :: uu____11823  in
                        (uu____11786, uu____11789)  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____11771  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.ml_bool_ty) uu____11770
                     in
                  ((FStar_List.append wildcards [(mlid, targ)]), uu____11769)
                   in
                FStar_Extraction_ML_Syntax.MLE_Fun uu____11758  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____11757
               in
            let uu____11898 =
              let uu____11899 =
                let uu____11902 =
                  let uu____11903 =
                    FStar_Extraction_ML_UEnv.convIdent
                      discName.FStar_Ident.ident
                     in
                  {
                    FStar_Extraction_ML_Syntax.mllb_name = uu____11903;
                    FStar_Extraction_ML_Syntax.mllb_tysc =
                      FStar_Pervasives_Native.None;
                    FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                    FStar_Extraction_ML_Syntax.mllb_def = discrBody;
                    FStar_Extraction_ML_Syntax.mllb_meta = [];
                    FStar_Extraction_ML_Syntax.print_typ = false
                  }  in
                [uu____11902]  in
              (FStar_Extraction_ML_Syntax.NonRec, uu____11899)  in
            FStar_Extraction_ML_Syntax.MLM_Let uu____11898
  